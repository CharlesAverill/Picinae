"""Strict register-layout boundary for the companion AMD64_AVX512 ISA.

Ghidra 11.4.2 PUBLIC ia.sinc: vectors at 0x1200, stride 64 bytes;
K0..K7 at decimal 2100, stride 8 bytes. No instruction lowering here.
All offsets returned below are bits within the single canonical cell.
"""
from dataclasses import asdict, dataclass
import re


@dataclass(frozen=True)
class RegisterView:
    bank: str
    slot: int
    low_bit: int
    bits: int
    physical_bits: int

    def to_dict(self):
        return asdict(self)


def register_view(name, size_bytes):
    """Resolve a full XMM/YMM/ZMM/K name; reject missing or wrong widths."""
    if not isinstance(name, str):
        raise ValueError("register name must be a string")
    match = re.fullmatch(r"(XMM|YMM|ZMM|K)(0|[1-9][0-9]*)", name)
    if match is None:
        raise ValueError(f"unsupported register name: {name!r}")
    prefix, index = match.groups()
    slot = int(index)
    bits = {"XMM": 128, "YMM": 256, "ZMM": 512, "K": 64}[prefix]
    if type(size_bytes) is not int or size_bytes * 8 != bits:
        raise ValueError(f"wrong varnode size for {name}")
    if slot >= (8 if prefix == "K" else 32):
        raise ValueError(f"out-of-range register: {name}")
    return RegisterView("R_K" if prefix == "K" else "R_ZMM", slot, 0,
                        bits, 64 if prefix == "K" else 512)


def register_slice(offset, size_bytes):
    """Resolve a little-endian Ghidra register-space byte slice.

    Only the two canonical banks are accepted; no unknown register fallback.
    This is a pcode storage slice, not an instruction-level upper-lane policy.
    """
    if type(offset) is not int or type(size_bytes) is not int or size_bytes <= 0:
        raise ValueError("invalid varnode extent")
    for base, stride, count, bank in ((0x1200, 64, 32, "R_ZMM"),
                                      (2100, 8, 8, "R_K")):
        if base <= offset < base + stride * count:
            slot, byte = divmod(offset - base, stride)
            if byte + size_bytes > stride:
                raise ValueError("varnode crosses a physical register boundary")
            return RegisterView(bank, slot, byte * 8, size_bytes * 8, stride * 8)
    raise ValueError("register-space offset is outside the vector/mask banks")


def vector_operand(name, size_bytes, encoding):
    """Check only encoding/register reach and vector length, not an opcode."""
    view = register_view(name, size_bytes)
    if view.bank != "R_ZMM" or encoding not in ("legacy", "vex", "evex"):
        raise ValueError("not a vector operand/encoding")
    if encoding == "legacy" and (view.bits != 128 or view.slot >= 16):
        raise ValueError("legacy operand requires XMM0..15")
    if encoding == "vex" and (view.bits == 512 or view.slot >= 16):
        raise ValueError("VEX operand requires XMM/YMM0..15")
    return view


def writemask(aaa, zeroing=False, memory_destination=False):
    """Decode the EVEX mask field; K0 data is never used as a writemask."""
    if type(aaa) is not int or not 0 <= aaa < 8:
        raise ValueError("EVEX.aaa must be a three-bit value")
    if type(zeroing) is not bool or type(memory_destination) is not bool:
        raise ValueError("mask policy flags must be booleans")
    if zeroing and (aaa == 0 or memory_destination):
        raise ValueError("zeroing requires a nonzero mask and register destination")
    return {"slot": aaa if aaa else None,
            "policy": "zero" if zeroing else "merge" if aaa else "unmasked"}
