#!/usr/bin/env python3
"""Extract verified halfwords, instruction starts and complete literal words.

Deliberately conservative: only linked ELF32 little-endian ARM with mapping
symbols. No relocations, stripped inputs, ARM state or system approximations.
This parser and the assembler/disassembler remain part of the trusted base.
"""
import bisect
import hashlib
import os
from pathlib import Path
import re
import struct
import subprocess
import sys


class Rejected(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


class ELF:
    def __init__(self, path):
        self.data = Path(path).read_bytes()
        require(self.data[:7] == b'\x7fELF\x01\x01\x01',
                'expected ELF32 little-endian version 1')
        hdr = self.unpack('<HHIIIIIHHHHHH', 16)
        kind, machine, _, _, _, shoff, _, _, _, _, shsize, shnum, names = hdr
        require(kind == 2 and machine == 40, 'expected linked ARM ET_EXEC (not relocatable/shared)')
        require(shsize == 40 and shnum > 0 and names < shnum, 'invalid/extended section table')
        self.sections = [self.unpack('<IIIIIIIIII', shoff + 40 * i) for i in range(shnum)]
        self.symbols = []
        for sec in self.sections:
            _, typ, _, _, off, size, link, _, _, entsize = sec
            if typ in (4, 9):
                require(size == 0, 'ELF contains unresolved/retained relocations')
            if typ == 2:
                require(entsize == 16 and link < shnum and size % 16 == 0, 'invalid symbol table')
                strings = self.section_bytes(self.sections[link])
                for at in range(off, off + size, 16):
                    n, value, length, info, _, index = self.unpack('<IIIBBH', at)
                    require(n < len(strings), 'invalid symbol name')
                    end = strings.find(b'\0', n)
                    require(end >= n, 'unterminated symbol')
                    name = strings[n:end].decode('ascii')
                    self.symbols.append((name, value, length, info & 15, index))
        require(self.symbols, 'symbol table required (preserve $t/$d mapping symbols)')
        self.mappings = {}
        for name, value, _, _, index in self.symbols:
            if re.fullmatch(r'\$[tda](?:\..*)?', name):
                self.mappings.setdefault(index, []).append((value, name[1]))
        for mapping in self.mappings.values():
            mapping.sort()

    def unpack(self, fmt, offset):
        size = struct.calcsize(fmt)
        require(0 <= offset <= len(self.data) - size, 'truncated ELF')
        return struct.unpack_from(fmt, self.data, offset)

    def section_bytes(self, sec):
        off, size = sec[4:6]
        require(off + size <= len(self.data), 'truncated section')
        return self.data[off:off + size]

    def read(self, address, size, immutable=False):
        candidates = [s for s in self.sections if s[1] == 1 and s[2] & 2
                      and s[3] <= address and address + size <= s[3] + s[5]]
        require(len(candidates) == 1, f'missing/ambiguous bytes at 0x{address:x} (+{size})')
        sec = candidates[0]
        require(not immutable or sec[2] & 1 == 0, 'literal word in writable section')
        data = self.section_bytes(sec)
        at = address - sec[3]
        return data[at:at + size]

    def mode(self, index, address):
        mapping = self.mappings.get(index, [])
        at = bisect.bisect_right(mapping, (address, 'z')) - 1
        require(at >= 0, f'missing mapping symbol at 0x{address:x}')
        return mapping[at][1]


def accepted16(hw):
    """Conservative encoding checks in addition to objdump recognition.

    Exclude invalid/system encodings and architecturally unpredictable operand
    cases that the inherited total decoder deliberately does not distinguish.
    """
    top = hw >> 12
    if top <= 3 or top in (5, 6, 7, 8, 9, 10):
        return True
    if top == 4:
        if hw & 0xfc00 != 0x4400:
            return True
        op, rd, rm = (hw >> 8) & 3, (hw & 7) | ((hw >> 4) & 8), (hw >> 3) & 15
        if op == 3:
            return hw & 7 == 0 and rm != 15
        if op == 1:
            return rd not in (13, 15) and rm not in (13, 15) and (rd >= 8 or rm >= 8)
        return not (rd == 15 and rm == 15)
    if top == 11:
        group = (hw >> 8) & 15
        if group in (0, 2):
            return True
        if group in (4, 12):
            return hw & 255 != 0
        if group in (5, 13):
            return True
        if group == 10:
            return (hw >> 6) & 3 != 2
        return hw == 0xbf00  # only NOP; no hints, CPS or exceptions
    if top == 12:
        rn, regs = (hw >> 8) & 7, hw & 255
        # STM base in list must be the lowest register.
        return regs != 0 and (hw & 0x800 != 0 or regs & (1 << rn) == 0
                              or regs & ((1 << rn) - 1) == 0)
    if top == 13:
        return (hw >> 8) & 15 < 14
    return top == 14 and hw & 0x800 == 0


def extract(path, name, function, objdump):
    require(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name), 'invalid Coq definition name')
    elf = ELF(path)
    ranges = []
    if function:
        symbols = [s for s in elf.symbols if s[0] == function and s[3] == 2]
        require(len(symbols) == 1, 'expected one sized STT_FUNC symbol')
        _, value, size, _, index = symbols[0]
        require(index < len(elf.sections) and size > 0, 'function requires a defined nonzero size')
        require(value & 1, 'function must have the Thumb symbol bit')
        ranges.append((index, value & ~1, (value & ~1) + size))
    else:
        for index, sec in enumerate(elf.sections):
            if sec[1] == 1 and sec[2] & 6 == 6 and sec[5]:
                ranges.append((index, sec[3], sec[3] + sec[5]))
    require(ranges, 'no executable ranges')
    # Objdump provides independent disassembly/recognition. Bytes always come
    # directly from the ELF, never from text columns (which can abbreviate data).
    proc = subprocess.run([objdump, '-d', '-z', path], check=True,
                          text=True, capture_output=True)
    decoded = {}
    for line in proc.stdout.splitlines():
        match = re.match(r'^\s*([0-9a-f]+):\s+([0-9a-f]{4}(?:\s+[0-9a-f]{4})?)\s+([^\s].*)$', line)
        if match:
            address = int(match[1], 16)
            halves = [int(h, 16) for h in match[2].split()]
            require(address not in decoded, 'overlapping disassembly addresses')
            decoded[address] = (halves, match[3])
    halfwords, starts = {}, []

    def include(address, size, immutable=False):
        require(address % 2 == 0 and size % 2 == 0 and address + size <= 2**32,
                'unaligned/overflowing halfword range')
        data = elf.read(address, size, immutable)
        for offset in range(0, size, 2):
            halfwords[address + offset] = int.from_bytes(data[offset:offset + 2], 'little')

    for index, lo, hi in ranges:
        require(lo % 2 == 0 and hi % 2 == 0, 'odd executable range')
        sec = elf.sections[index]
        require(sec[1] == 1 and sec[2] & 6 == 6 and sec[3] <= lo < hi <= sec[3] + sec[5],
                'function outside executable section')
        include(lo, hi - lo)
        a = lo
        while a < hi:
            mode = elf.mode(index, a)
            require(mode in ('t', 'd'), f'ARM-state code at 0x{a:x}')
            if mode == 'd':
                a += 2
                continue
            hw = halfwords[a]
            width = 4 if hw >> 11 >= 29 else 2
            require(a + width <= hi, f'truncated instruction at 0x{a:x}')
            require(all(elf.mode(index, b) == 't' for b in range(a, a + width)),
                    f'instruction crosses mapping boundary at 0x{a:x}')
            require(a in decoded, f'objdump did not decode 0x{a:x}')
            halves, text = decoded[a]
            expected = [halfwords[b] for b in range(a, a + width, 2)]
            require(halves == expected and not text.startswith('.') and 'undefined' not in text,
                    f'unknown instruction at 0x{a:x}: {text}')
            if width == 4:
                supported = hw & 0xf800 == 0xf000 and halves[1] & 0xd000 == 0xd000
            else:
                supported = accepted16(hw)
            require(supported, f'unsupported instruction at 0x{a:x}: {text}')
            starts.append(a)
            if hw & 0xf800 == 0x4800:  # LDR literal: include the entire word, even past STT_FUNC size
                literal = ((a + 4) & ~3) + (hw & 255) * 4
                include(literal, 4, immutable=True)
            a += width
    require(starts, 'no supported instructions')
    digest = hashlib.sha256(elf.data).hexdigest()
    lines = [f'(* Generated by armv6m_lifter.sh; ELF SHA256 {digest}.',
             '   Literal loads assume immutable pool bytes. Use the finite _prog entrypoint. *)',
             'From Stdlib Require Import NArith List.', 'Require Import Picinae_armv6m.',
             'Open Scope N.', f'Definition {name} (a : addr) : N :=', '  match a with']
    lines += [f'  | 0x{a:x} => 0x{hw:04x}' for a, hw in sorted(halfwords.items())]
    lines += ['  | _ => 0', '  end.',
              f'Definition start_{name} : N := 0x{min(starts):x}.',
              f'Definition end_{name} : N := 0x{max(halfwords):x}.',
              f'Definition {name}_entries : list N :=',
              '  ' + ' :: '.join(f'0x{a:x}' for a in starts) + ' :: nil.',
              f'Definition {name}_prog : program := fun s a =>',
              f'  if existsb (N.eqb a) {name}_entries then lift_armv6m {name} s a else None.',
              # Kernel check that the strict frontend never accepted T_Invalid.
              # This checks the actual Rocq decoder, independent of accepted16.
              f'Example {name}_decode_check :',
              '  forallb (fun a =>',
              f'    match (if is_32bit_insn ({name} a)',
              f'           then thumb32_decode ({name} a) ({name} (a + 2))',
              f'           else thumb16_decode ({name} a)) with',
              f'    | T_Invalid => false | _ => true end) {name}_entries = true.',
              'Proof. vm_compute. reflexivity. Qed.',
              f'Theorem {name}_welltyped : welltyped_prog armv6mtypctx {name}_prog.',
              'Proof.',
              f'  intros s a. unfold {name}_prog. destruct (existsb (N.eqb a) {name}_entries).',
              '  apply welltyped_lift_armv6m. exact I.',
              'Qed.']
    return '\n'.join(lines) + '\n'


def main():
    try:
        require(len(sys.argv) in (3, 4),
                'usage: armv6m_lifter.sh <linked-elf> <coq_definition> [function]')
        objdump = os.environ.get('OBJDUMP')
        require(objdump, 'set OBJDUMP to an ARM objdump executable')
        result = extract(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) == 4 else None, objdump)
    except (Rejected, OSError, UnicodeError, struct.error, subprocess.CalledProcessError) as err:
        print(f'armv6m lifter: {err}', file=sys.stderr)
        return 1
    # No partial Coq output on rejection, including subprocess failure.
    sys.stdout.write(result)
    return 0


if __name__ == '__main__':
    sys.exit(main())
