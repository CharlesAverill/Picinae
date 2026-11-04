"""Reproduce the exact e01 wide-copy register/encoding handoff; no lifting.

Run with --write once to save copy-operands.json, then without it to verify.
All extents stay half-open st_value/st_size: external CFG closure is e17 work.
"""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from amd64_vector_layout import vector_operand, register_view

E01 = ROOT / "Examples/claude/inventory/e01-x86-inventory/generated"
PINNED = {
    "inventory.json": "95c024247e40ff85c01a39476e53eac0590aadca49aff7ef58545b96c8143a1d",
    "disassembly.txt": "23134f9be4d4acb07fb77888e7c5d29412b116cb4cf8a63675144b20bdc0ba0e",
}


def collect():
    for name, digest in PINNED.items():
        assert hashlib.sha256((E01 / name).read_bytes()).hexdigest() == digest, name
    inventory = json.loads((E01 / "inventory.json").read_text())
    assert inventory["libc_sha256"] == "9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9"
    selected = [e for e in inventory["extents"] if "copy" in e["scope"] and
                any(re.match(r"__(memcpy|memmove|mempcpy).*_(avx512|evex)_", n)
                    for n in e["names"])]
    extents = {int(e["elf_address"], 16): e for e in selected}
    rows = {entry: [] for entry in extents}
    entry = None
    for line in (E01 / "disassembly.txt").read_text().splitlines():
        if line.startswith("# ELF "):
            entry = int(line.split()[2], 16)
        match = re.fullmatch(r"([0-9a-f]+)\s+([0-9a-f]+)\s+(\S+)\s*(.*)", line)
        if match is not None and entry in rows:
            address, raw, mnemonic, operands = match.groups()
            assert entry <= int(address, 16) < entry + extents[entry]["size"]
            rows[entry].append((address, raw, mnemonic, operands))
    output = []
    all_registers = set()
    for entry, extent in sorted(extents.items()):
        instructions = rows[entry]
        assert instructions and int(instructions[0][0], 16) == entry
        registers, shapes, masks = set(), {}, []
        for address, raw, mnemonic, operands in instructions:
            names = re.findall(r"\b(?:[xyz]mm\d+|k\d+)\b", operands)
            if not names:
                continue
            encoding = "evex" if raw.startswith("62") else "vex" if raw[:2] in ("c4", "c5") else "legacy"
            if encoding == "evex":
                # Verify EVEX.P2.z/aaa directly as well as the printed operands.
                assert int(raw[6:8], 16) & 0x87 == 0, (address, raw)
            for name in names:
                size = {"x": 16, "y": 32, "z": 64, "k": 8}[name[0]]
                if name[0] == "k":
                    register_view(name.upper(), size)
                else:
                    vector_operand(name.upper(), size, encoding)
                registers.add(name)
            key = f"{encoding}:{mnemonic}:" + ",".join(sorted(set(names)))
            shape = shapes.setdefault(key, {"count": 0, "first_elf_address": "0x"+address,
                                            "bytes": raw, "assembly": mnemonic+" "+operands})
            shape["count"] += 1
            if "{" in operands or any(name.startswith("k") for name in names):
                masks.append("0x" + address)
        all_registers.update(registers)
        output.append({"names": extent["names"], "elf_address": extent["elf_address"],
                       "size": extent["size"], "sha256": extent["sha256"],
                       "registers": sorted(registers), "mask_sites": masks,
                       "vector_shapes": dict(sorted(shapes.items()))})
    assert len(output) == 20
    assert "ymm31" in all_registers and "zmm29" in all_registers
    assert not any(e["mask_sites"] for e in output)
    return {"e01_commit": "131ad4b86cf4abcbd392048297038f3f219423bb",
            "libc_sha256": inventory["libc_sha256"], "e01_files": PINNED,
            "boundary": "exact symbol extents only; not a closed reachable CFG or instruction lowering",
            "registers": sorted(all_registers), "extents": output}


if __name__ == "__main__":
    result = collect()
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    target = Path(__file__).with_name("copy-operands.json")
    if sys.argv[1:] == ["--write"]:
        target.write_text(text)
    else:
        assert not sys.argv[1:], "usage: operand_inventory.py [--write]"
        assert target.read_text() == text, "operand metadata differs; inspect e01 provenance"
    print(f"PASS: {len(result['extents'])} exact wide-copy extents; "
          f"{len(result['registers'])} named register views; no explicit opmask operands")
