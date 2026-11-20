"""Numerical diagnostic only: not an IL execution or kernel proof."""
from pathlib import Path
import re
Q, H = 1 << 64, 1 << 63
d, s, n = 4096, 8192, H + 4096
delta = (d-s) % Q
sign = (((delta+n) % Q) ^ delta) >> 63
guard = ((delta & 0xf00) + sign) % (1 << 32)
assert H <= n and d < s < d+n and s+n <= Q and n <= delta
assert sign == 0 and guard == 0
L = ((d+n-129) % Q) & (Q-32)
assert L == d+n-160
assert L-32*128+s-d == L
print(f'd={d}, s={s}, n={n}, d+n={d+n}, s+n={s+n}')
print(f'delta={delta}, sign={sign}, dispatch_sum={guard}')
print(f'first row destination L={L}, 33rd row source={L-32*128+s-d}')
print(f'candidate wrong destination byte={L-4096}, source offset={L-s}')
source = Path('Examples/claude/memmove_avx_amd64.v').read_text()
for address, asm in re.findall(r'\(\*\s+(\d+): ([^\n]+?) \*\)', source):
    if int(address) in {318,331,337,341,344,348,354,357,501,511,533,544,549,554,559,563,567,572,577,582,586,590,593}:
        print(address, asm)
print('PASS numerical diagnostic; no execution/termination/correctness certificate')
