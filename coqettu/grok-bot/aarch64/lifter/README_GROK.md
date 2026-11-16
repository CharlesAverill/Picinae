# Patched copy of the Picinae Ghidra lifter (Grok Bot / coqettu)

Copied from `~/research/picinae-llm/tools/ghidra-lifter` (repo HEAD a4bae9c plus the
uncommitted working-tree changes present on 2026-11-16) so we can fix lifter bugs
without touching shared files.  `../lift.sh` uses this copy.

## Fixes
1. **BOOL_NEGATE lifted as bitwise NOT** (`pcode2coq_lib.py`).  Upstream maps
   `INT_NEGATE | BOOL_NEGATE` to `UnOp OP_NOT`.  For BOOL_NEGATE the operand is a
   0/1 boolean byte (e.g. the carry flag `R_CY`), so NOT gives 0xff/0xfe instead of
   0/1.  Branches only use the low bit (`Cast CAST_LOW 1`), so they were unaffected,
   but value-producing uses are wrong: `cset w0,cc` (wcscmp at 0x15fb20) produced
   W0 = 254/255 instead of 0/1, i.e. the upstream lift says wcscmp returns 254 for
   equal strings.  Fixed to `BinOp OP_XOR e (Word 1 w)`.
   Affected lifts (upstream vs fixed, see ../lifted_raw_upstream vs ../lifted_raw):
   memchr memcpy memmove memrchr memset stpcpy strchrnul strcmp strncmp strnlen swab
   tolower toupper wcschr wcscmp wcsncmp wcsnlen wmemcmp wmemcpy wmemset.
2. **LZCOUNT (clz) lifted as width - popcount(x)** (`pcode2coq_lib.py`).  That is only
   correct when the set bits of x are contiguous from bit 0.  E.g. 64-bit
   clz(0x8000000000000001) = 0 but upstream yields 62.  Fixed to
   `BinOp OP_MINUS (Word w w) (UnOp OP_BITWIDTH x)` (OP_BITWIDTH = N.size, so
   w - N.size x = number of leading zeros for x < 2^w, and = w for x = 0).
   Affected lifts among ours: ffs (rbit + clz).

3. **Narrow read of a wider unique temp lost its truncation** (`pcode2coq_lib.py`,
   `vnToExp`/`vnWidth`).  Ghidra lifts `cmp w2,w1,UXTB` as
   `(unique,0x4900,4) COPY w1; (unique,0x4a00,4) INT_ZEXT (unique,0x4900,1)`:
   the second op reads only the low byte of the temp.  Upstream emitted
   `Var (V_TEMP 0x4900)` (all 32 bits), i.e. the uxtb was dropped and strchr
   compared the found byte with c mod 2^32 instead of c mod 256 (wrong for
   c >= 256, e.g. strchr(s, 0x141) must find 'A').  Fixed: emit
   `Extract (8n-1) 0 (Var temp)` when the read size n is smaller than the
   temp's typed width.  Re-lifting every function we have proofs for showed
   that only strchr_armv8.v changed (2026-11-16 04:5x CST).
