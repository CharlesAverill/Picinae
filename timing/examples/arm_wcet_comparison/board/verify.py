"""Check that the functions in the firmware are byte-identical to the ELFs aiT
analyzed (../<dir>/<name>.elf), and sit at the same address mod 64.

    python3 verify.py build/flash/timing.elf
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FUNCS = [  # (function, analyzed ELF)
    ('sum', '../cache/cache.elf'),
    ('while_true_break', '../while_true_break/while_true_break.elf'),
    ('find', '../arraysearch/arraysearch.elf'),
    ('collatz', '../collatz/collatz.elf'),
    ('find_in_list', '../llsearch/linked_list.elf'),
    ('insert_after_pos_in_list', '../llsearch/linked_list.elf'),
    ('insert_in_sorted_list', '../llsearch/linked_list.elf'),
]
ALIGN = 64


def symbols(elf):
    out = subprocess.run(['arm-none-eabi-nm', '-S', elf], check=True,
                         capture_output=True, text=True).stdout
    syms = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 4:
            syms[parts[3]] = (int(parts[0], 16), int(parts[1], 16))
    return syms


def func_bytes(elf, name):
    addr, size = symbols(elf)[name]
    # Find the section base: the lowest address among .text/.bench
    hdr = subprocess.run(['arm-none-eabi-objdump', '-h', elf], check=True,
                         capture_output=True, text=True).stdout
    bases = []
    for line in hdr.splitlines():
        p = line.split()
        if len(p) >= 4 and p[1] in ('.text', '.bench'):
            bases.append((int(p[3], 16), int(p[2], 16), p[1]))  # vma, size, name
    # Read the bytes straight out of the section that contains the function
    for vma, sz, sec in bases:
        if vma <= addr < vma + sz:
            data = subprocess.run(['arm-none-eabi-objcopy', '-O', 'binary',
                                   f'--only-section={sec}', elf, '/dev/stdout'],
                                  check=True, capture_output=True).stdout
            return addr, data[addr - vma: addr - vma + size]
    raise SystemExit(f'{name}: no section contains 0x{addr:x} in {elf}')


def main():
    fw = sys.argv[1]
    bad = 0
    for name, ref in FUNCS:
        ref = HERE / ref
        a_fw, b_fw = func_bytes(fw, name)
        a_ref, b_ref = func_bytes(str(ref), name)
        same = b_fw == b_ref
        aligned = (a_fw - a_ref) % ALIGN == 0
        print(f'{"ok " if same and aligned else "BAD"} {name:26s} 0x{a_fw:08x} '
              f'(analyzed at 0x{a_ref:08x}), {len(b_fw)} bytes'
              f'{"" if same else ", bytes differ"}{"" if aligned else ", alignment differs"}')
        bad += not (same and aligned)
    if bad:
        sys.exit(f'{bad} function(s) differ from the analyzed binaries')


if __name__ == '__main__':
    main()
