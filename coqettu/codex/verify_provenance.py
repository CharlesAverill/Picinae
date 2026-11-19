#!/usr/bin/env python3
"""Check lift hashes, global addresses, sizes, and reachable instruction coverage.

This checks correspondence of instruction boundaries, not correctness of Ghidra
or of the p-code-to-Picinae translation. Those remain trusted inputs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

EXPECTED = "8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de"
IMAGE_BASE = 0x10000
# Internal support routines are pinned by exact bytes, not exported symbols.
SUPPORT = {
    "pc_thunk_bx": (0x3A842, 4, bytes.fromhex("8b1c24c3")),
    "pc_thunk_ax": (0x3A83E, 4, bytes.fromhex("8b0424c3")),
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path)
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    baseline = json.loads((directory / "lifter_base/SOURCE.json").read_text())
    for name, expected in baseline["files_sha256"].items():
        actual = hashlib.sha256((directory / "lifter_base" / name).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Pinned lifter baseline changed: {name}")
    binary = directory.parent / "alpine_musl/x86/lib/libc.musl-x86.so.1"
    digest = hashlib.sha256(binary.read_bytes()).hexdigest()
    if digest != EXPECTED:
        raise SystemExit(f"Unexpected binary SHA256: {digest}")
    table = subprocess.check_output(["objdump", "-T", str(binary)], text=True)
    symbols = {}
    for line in table.splitlines():
        fields = line.split()
        if len(fields) == 6 and fields[3] == ".text":
            symbols[fields[5]] = (int(fields[0], 16), int(fields[4], 16))
    manifest = []
    for source in sorted((directory / "x86").glob("*_i386.v")):
        text = source.read_text()
        name_match = re.search(r"^function: (\S+)$", text, re.M)
        hash_match = re.search(r"^SHA256: (\S+)$", text, re.M)
        if not name_match or not hash_match or hash_match[1] != digest:
            raise SystemExit(f"Missing or inconsistent provenance in {source.name}")
        name = name_match[1]
        if name in SUPPORT:
            address, size, expected_bytes = SUPPORT[name]
            selection = [f"--start-address={address}", f"--stop-address={address + size}"]
        else:
            address, size = symbols[name]
            selection = [f"--start-address={address}", f"--stop-address={address + size}"]
        assembly = subprocess.check_output(["objdump", "-d", "-w", *selection, str(binary)], text=True)
        instructions, encodings = {}, {}
        for line in assembly.splitlines():
            match = re.match(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)\s*(\S.*)$", line)
            if match:
                pc = int(match[1], 16)
                instructions[pc] = (len(match[2].split()), match[3].strip())
                encodings[pc] = bytes.fromhex("".join(match[2].split()))
        if name in SUPPORT and b"".join(encodings[pc] for pc in sorted(encodings)) != expected_bytes:
            raise SystemExit(f"Internal support bytes changed: {name}")
        lifted = {
            int(pc, 16) - IMAGE_BASE: int(length)
            for pc, length in re.findall(
                r"^\|\s+(0x[0-9a-f]+)\s*=>\s*Some\s*\((\d+),", text, re.M
            )
        }
        if not lifted or address not in lifted:
            raise SystemExit(f"Missing function entry in {source.name}")
        for pc, length in lifted.items():
            if not address <= pc < address + size:
                raise SystemExit(f"Out-of-range instruction {pc:#x} in {source.name}")
            if pc not in instructions or instructions[pc][0] != length:
                raise SystemExit(f"Instruction boundary/size mismatch at {pc:#x} in {source.name}")
        reachable, pending = set(), [address]
        while pending:
            pc = pending.pop()
            if pc in reachable:
                continue
            if pc not in instructions:
                raise SystemExit(f"Missing disassembly at reachable address {pc:#x} in {name}")
            reachable.add(pc)
            length, operation = instructions[pc]
            mnemonic, *operands = operation.split(maxsplit=1)
            if mnemonic.startswith("ret"):
                continue
            if mnemonic.startswith("j"):
                target = re.match(r"([0-9a-f]+)\b", operands[0] if operands else "")
                if not target:
                    raise SystemExit(f"Unhandled indirect branch in {name}: {operation}")
                pending.append(int(target[1], 16))
                if mnemonic in {"jmp", "jmpl"}:
                    continue
            pending.append(pc + length)
        missing = reachable - lifted.keys()
        if missing:
            raise SystemExit(f"Unlifted reachable instructions in {name}: {sorted(missing)}")
        manifest.append({
            "function": name,
            "internal_support": name in SUPPORT,
            "source": str(source.relative_to(directory)),
            "elf_address": hex(address),
            "global_entry": hex(address + IMAGE_BASE),
            "elf_size": size,
            "lifted_instructions": len(lifted),
            "reachable_instructions": len(reachable),
            "lift_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "bounded_bsf_adapter": "Codex-local BSF32 adapter" in text,
        })
    if not manifest:
        raise SystemExit("No lifted functions found")
    result = {"binary_sha256": digest, "ghidra_image_base": hex(IMAGE_BASE),
              "lifter_baseline": baseline,
              "adapter_sha256": {name: hashlib.sha256((directory / name).read_bytes()).hexdigest()
                                 for name in ["bsf_adapter.py", "segment_adapter.py", "pcode2coq_codex.py"]},
              "functions": manifest}
    if args.manifest:
        args.manifest.parent.mkdir(parents=True, exist_ok=True)
        args.manifest.write_text(json.dumps(result, indent=2) + "\n")
    count = sum(item["reachable_instructions"] for item in manifest)
    print(f"Verified provenance and coverage of {len(manifest)} lifts ({count} reachable instructions).")


if __name__ == "__main__":
    main()
