#!/usr/bin/env python3
"""Inventory the pinned ELF and its separate debug file without executing either.

Only the Python standard library and readelf/isolated ARM objdump are used.
The small ELF reader deliberately accepts only ELF64 little-endian AArch64.
"""
import argparse
import hashlib
import json
import pathlib
import re
import struct
import subprocess

EXPECTED = "79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06"
BUILD_ID = "977c021c364ee3c495c0e5f2375bf6ba2124a6da"


def sha(data):
    return hashlib.sha256(data).hexdigest()


class ELF:
    def __init__(self, path):
        self.path = path
        self.data = path.read_bytes()
        if self.data[:6] != b"\x7fELF\x02\x01":
            raise ValueError("requires ELF64 little endian")
        h = struct.unpack_from("<16sHHIQQQIHHHHHH", self.data)
        if h[2] != 183:
            raise ValueError("requires AArch64")
        self.sections = [struct.unpack_from("<IIQQQQIIQQ", self.data, h[6] + i*h[11])
                         for i in range(h[12])]
        self.loads = [p for i in range(h[10])
                      if (p := struct.unpack_from("<IIQQQQQQ", self.data, h[5]+i*h[9]))[0] == 1]

    def symbols(self):
        result = []
        for s in self.sections:
            if s[1] not in (2, 11):
                continue
            st = self.sections[s[6]]
            strings = self.data[st[4]:st[4]+st[5]]
            for off in range(s[4], s[4]+s[5], s[9]):
                n, info, other, ndx, value, size = struct.unpack_from("<IBBHQQ", self.data, off)
                typ = {2: "FUNC", 10: "IFUNC"}.get(info & 15)
                if not typ or not ndx:
                    continue
                name = strings[n:strings.index(b"\0", n)].decode()
                result.append(dict(name=name, address=value, size=size, type=typ,
                                   binding={0: "LOCAL", 1: "GLOBAL", 2: "WEAK"}.get(info >> 4, str(info >> 4))))
        return sorted(result, key=lambda s: (s["address"], s["name"]))

    def at(self, address, size):
        for p in self.loads:
            if p[3] <= address and address+size <= p[3]+p[5]:
                off = p[2]+address-p[3]
                return self.data[off:off+size]
        raise ValueError(f"non-file-backed range {address:x}+{size}")


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--toolchain", type=pathlib.Path, required=True)
    p.add_argument("--repo", type=pathlib.Path, required=True)
    p.add_argument("--out", type=pathlib.Path, required=True)
    p.add_argument("--arm-env", default="/home/charles/code/friends/.toolchains/arm-validation/picinae-env")
    a = p.parse_args()
    a.out.mkdir(parents=True, exist_ok=True)
    binary = a.toolchain/"root/lib/aarch64-linux-gnu/libc.so.6"
    debug = a.toolchain/f"root/usr/lib/debug/.build-id/{BUILD_ID[:2]}/{BUILD_ID[2:]}.debug"
    elf, dbg = ELF(binary), ELF(debug)
    if sha(elf.data) != EXPECTED:
        raise ValueError("wrong libc SHA256")
    for f in (binary, debug):
        notes = subprocess.run(["readelf", "-n", str(f)], check=True, capture_output=True, text=True).stdout
        if f"Build ID: {BUILD_ID}" not in notes:
            raise ValueError("mismatched debug build ID")
    symbols = dbg.symbols()
    relevant = [s.copy() for s in symbols if re.match(r"^_*(?:mem|str|stp|rawmem|bzero|bcmp|index|rindex|wmem|wcs)", s["name"])]
    for s in relevant:
        s["ghidra_address"] = hex(s["address"] + 0x100000)
        s["elf_address"] = hex(s["address"])
        s["sha256_bytes"] = sha(elf.at(s["address"], s["size"]))
        s["same_entry_symbols"] = sorted({t["name"] for t in symbols if t["address"] == s["address"]})
    byname = {s["name"]: s for s in symbols}
    ports = []
    names = {f.name.removesuffix("_amd64.v") for f in (a.repo/"Examples/claude").glob("*_amd64.v")}
    names |= set("div ldiv ffs ffsl ffsll swab sigaddset sigdelset sigismember memcpy memmove mempcpy __memcpy_chk __memmove_chk __mempcpy_chk memset memcmp strlen strcpy strcmp strchr strspn strcspn strsep strtok_r strdup strndup memccpy bsearch lfind lsearch pthread_mutex_lock pthread_mutex_unlock".split())
    for n in sorted(names):
        lifted = (a.repo/f"Examples/claude/{n}_arm8.v").exists()
        proof = (a.repo/f"Examples/claude/arm8_{n}_proof.v").exists()
        s = byname.get(n)
        ports.append(dict(target=n, symbol=s, lift_present=lifted, proof_file_present=proof,
                          status="existing lift; proof file present (not audited)" if proof else
                          "existing lift; no proof file" if lifted else
                          "missing ARM lift" if s else "no exact symbol; resolve variant/name before assigning"))
    comparisons = []
    for name in ("div", "ldiv", "ffs", "ffsl", "ffsll", "swab"):
        source = a.repo/f"Examples/claude/{name}_arm8.v"
        text = source.read_text()
        entry = int(re.search(r"entry: (0x[0-9a-f]+)", text)[1], 16)
        insns = re.findall(r"\(\* (0x[0-9a-f]+): (.*?) \*\)", text)
        s = byname[name]
        addresses = [int(i[0], 16)-0x100000 for i in insns]
        if entry != s["address"]+0x100000 or addresses != list(range(s["address"], s["address"]+s["size"], 4)):
            raise ValueError(f"{name}: symbol extent/address mismatch")
        comparisons.append(dict(function=name, elf_entry=hex(s["address"]), ghidra_entry=hex(entry),
                                size=s["size"], instructions=len(insns), sha256_bytes=sha(elf.at(s["address"], s["size"])),
                                lift_sha256=sha(source.read_bytes()), extent_check="PASS",
                                instruction_comments="see ghidra-audit.json for exact Ghidra decoder comparison"))
    manifest = dict(libc_sha256=sha(elf.data), build_id=BUILD_ID, debug_sha256=sha(dbg.data),
                    image_base="0x100000", elf_type="ELF64 little-endian AArch64 ET_DYN",
                    packages=[dict(file=f.name, sha256=sha(f.read_bytes())) for f in sorted((a.toolchain/"downloads").glob("*.deb"))],
                    memory_string_symbols=relevant, ports=ports, existing_lift_extents=comparisons)
    (a.out/"inventory.json").write_text(json.dumps(manifest, indent=2)+"\n")
    lines = ["name\ttype\tELF address\tGhidra address\tsize\tSHA256 bytes\tsame entry symbols"]
    lines += ["\t".join(str(s[k]) if k != "same_entry_symbols" else ",".join(s[k]) for k in
                        ("name", "type", "elf_address", "ghidra_address", "size", "sha256_bytes", "same_entry_symbols")) for s in relevant]
    (a.out/"memory-string-symbols.tsv").write_text("\n".join(lines)+"\n")
    names = {s["name"] for s in relevant if s["name"] in {
        "memcpy", "memmove", "mempcpy", "__mempcpy", "__memcpy_chk", "__memmove_chk",
        "__mempcpy_chk", "__memset_chk", "strlen", "memchr", "memset", "memcmp",
        "strcmp", "strcpy", "strchr", "strspn", "strcspn"} or
        s["name"].startswith(("__memcpy_", "__memmove_", "__memset_", "__strlen_", "__memchr_"))
        and not s["name"].endswith("_ifunc")}
    names |= set("div ldiv ffs ffsl ffsll swab sigaddset sigdelset sigismember".split())
    edges = []
    with (a.out/"copy-string-disassembly.txt").open("w") as out:
        for name in sorted(names):
            s = byname[name]
            out.write(f'\nSYMBOL {name} ELF {s["address"]:#x} size {s["size"]} SHA256 {sha(elf.at(s["address"], s["size"]))}\n')
            command = [a.arm_env, "aarch64-linux-gnu-objdump", "-d",
                       f'--start-address={s["address"]}', f'--stop-address={s["address"]+s["size"]}', str(binary)]
            disasm = subprocess.run(command, check=True, capture_output=True, text=True).stdout
            out.write(disasm)
            for match in re.finditer(r'^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(b(?:\.[a-z]+)?|bl)\s+([0-9a-f]+)\s', disasm, re.M):
                address, kind, target = int(match[1], 16), match[2], int(match[3], 16)
                if not s["address"] <= target < s["address"]+s["size"]:
                    edges.append(dict(function=name, instruction=hex(address), kind=kind, target=hex(target),
                                      target_entries=sorted({t["name"] for t in symbols if t["address"] == target}),
                                      target_containing_extents=sorted({t["name"] for t in symbols if t["address"] <= target < t["address"]+t["size"]})))
    (a.out/"external-direct-edges.json").write_text(json.dumps(edges, indent=2)+"\n")
    print(f"PASS exact libc/debug build ID; {len(relevant)} memory/string symbols; six lift extents")
    print(f"PASS {len(names)} disassembly ranges; {len(edges)} direct edges outside symbol extents (not a complete CFG)")


if __name__ == "__main__":
    main()
