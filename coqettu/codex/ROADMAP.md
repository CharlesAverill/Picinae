# Codex / musl i386

Assignment: `alpine_musl/x86/lib/libc.musl-x86.so.1`, musl-1.2.6-r6.
All work is isolated here; do not consult the other models' directories.

## Solved

- Verified the x86 APK and ELF against `../sha256sums`.
- Strict Ghidra 12.0 / PyGhidra lifts with global addresses and generated type
  checks; separate IL and proof artifacts, reusable ABI/bit/string/stack libraries.
- Completed functional-correctness and full ABI return contracts:
  - `toascii`: all 32-bit arguments; seven-bit range and idempotence.
  - `htonl`, `ntohl`, `htons`, `ntohs`: exact byte reversal and round trips.
    The 16-bit functions also describe the untouched upper EAX bits.
  - `isascii`, `isdigit`, `islower`, `isupper`, `isprint`, `isgraph`: exact
    ASCII classification; interval proofs account for modular subtraction.
  - `abs`, `labs`: exact binary results for every argument, plus agreement
    with mathematical signed absolute value away from INT_MIN/LONG_MIN.
  - `strlen`: alignment scan, four-byte zero detection and final byte scan;
    the result is an existential first-NUL index, never an input assumption.
  - `wmemchr`: bounded wide-character search, both return sites and zero count;
    no precomputed match witness or artificial count limit.
  - `memcmp`: byte comparison loop, exact first-difference result, EBX save
    and restoration, stack memory frame, transport back to original buffers.
  - `wmemcmp`: signed 32-bit wide-character ordering, first mismatch and
    equal-prefix results, with EBX restoration and the explicit stack frame.
  - `ffs`, `ffsl`, `ffsll`: zero or the one-based first set-bit index, all
    32-bit and 64-bit representations. A reusable checked BSF32 theorem
    covers the bounded instruction expansion; `ffsll` composes two scans.
  - `strcmp`: first unsigned-byte mismatch or common NUL, an equal nonzero
    prefix in original memory, and restoration of both ESI and EBX.
  - `memrchr`: greatest matching byte index or NULL, an explicit nonmatching
    suffix, unsigned-byte conversion, and the two-register ABI frame.
  - `wmemset`: every requested wide element equals the input value; every
    disjoint read is unchanged, the original pointer is returned, and the
    original return address and full register frame survive the memory writes.
- Every correctness theorem supports an arbitrary containing program extending
  its lift. Completed return contracts include the saved return address, stack
  pop, memory frame, callee-saved registers, and access-permission frame.
- Independent kernel recheck passed for all 23 completed functions;
  their 46 public contracts passed the logical-assumption audit.
- Native checks against the exact musl ELF pass, including string alignments,
  first/last mismatch positions, signed wide ordering, zero counts, 32/64-bit
  first-set-bit results, and wide fills with surrounding canaries.
- Provenance checker validated 25 lifts and 247 reachable instructions against
  ELF disassembly (hash, global addresses, instruction sizes, complete coverage).
  The full lifting script reproduced all 25 files byte-for-byte in a fresh
  output directory, without modifying the checked sources.
- Assumption audit found only Picinae's pre-existing
  `FunctionalExtensionality.functional_extensionality_dep` axiom; no admitted
  functional-correctness theorems. This is not a claim of an axiom-free foundation.

## Next steps

1. Handle `bcmp` by composing its PIC thunk, calls, stack frame and `memcmp`.
2. Lift and verify the `memchr` callee, then compose `strnlen`.
3. Extend the frame library for `strncmp`: it saves four registers, uses a
   stack-local word, and advances its second argument slot in memory.
4. Extend the checked fill/outside-region frame library to `memset` and
   copying primitives, including their optimized instruction sequences.

## Open problems and limits

- BSF lifting uses a Codex-local adapter for the exact Ghidra register BSF32
  graph. It emits 32 guarded rounds; checked lemmas establish the first-set-bit
  result and architectural frame. Recognition, rejection and numerical scan
  tests pass. Other backward p-code branches remain rejected.
- The original shared lifter is pinned under `lifter_base/`, with commit and
  file hashes, so concurrent edits to repository tools cannot change our lifts.
- The pinned baseline translates LZCOUNT as width minus popcount, which is
  not a leading-zero count. None of the selected lifts uses that translation.
  Address it before accepting a target containing LZCOUNT p-code.
- `bcmp` / `strnlen`: preparatory lifts typecheck, but their call targets need
  linked callee contracts and proofs. These lifts are not correctness results.
- Correctness is partial: no theorem currently guarantees termination or
  successful concrete memory accesses. Picinae memory addresses wrap modulo
  2^32 and the access permissions constrain admitted execution traces.
- `wmemset` protects the entry return address and three argument words with
  destination/stack disjointness. Its finite-region bound is derived from that
  condition, rather than imposed as an extra caller count restriction. The
  memory frame describes every disjoint little-endian read, for any length.
- `strlen` can read a full word beyond a terminator. Its proof does not establish
  a separate concrete page-access safety theorem.
- `memcmp` / `wmemcmp` save EBX in the four bytes below entry ESP; the
  compared regions must avoid that slot. `strcmp` / `memrchr` save ESI and EBX
  in the eight bytes below entry ESP. Their contracts explicitly require the
  input bytes to avoid those two slots and describe exactly these memory writes.
  `strcmp` expresses this through the first NUL without a caller length witness.
- Ghidra instruction semantics and the lifter remain trusted inputs; instruction
  coverage/provenance checks do not prove semantic translation correctness.

## Useful lessons

- Ghidra imports this ET_DYN ELF at image base `0x10000`: add that to ELF VAs.
  Example: toascii ELF `0x3f62d` becomes IL address `0x4f62d`.
- Use `--globalAddressing --strictFailure --typeCheck`. The actual command-line
  flag spelling is camelCase even where skill prose uses hyphens.
- Headless Ghidra can report script failure while returning status zero. Check
  its log and require every requested function to have been freshly emitted.
- The local Linux man-pages 6.9.1 supply specifications; headers record their
  exact locations and the binary hash. No other models' artifacts were used.
- Substitute entry-store equalities from `destruct_inv` before stepping.
- Keep modular scan indices unbounded internally and normalize the first-NUL
  witness at return. This avoids requiring callers to provide a string length.
- The `check` target rejects an audit inventory missing either public contract
  for any function proof source. Add both names whenever adding a function.
- For BSF, prove raw instruction execution before resetting instruction-local
  temporaries; ordinary instruction stepping intentionally discards them.
- Prove the zero-byte mask over an abstract word with bit/division lemmas;
  apply it to memory only after its proof is checked.
- `psimpl` removes getmem address moduli. Normalize goal addresses to match
  branch hypotheses before using the latter.
- Avoid unrestricted `cbn` on mixed symbolic Z arithmetic: it can expand huge
  binary pattern matches. Use `change` to evaluate just the numeric constants.
- Compile with `ulimit -v 8000000`; keep memory out of arithmetic tactics.
- Do not edit a source file while a compiler is reading it. Sequentially finish
  the process before patching that file.
- The exported `simple solve bits inj` notation currently misses a tactic
  argument; the explicit equivalent is `solve_bits_inj false ltac:(0)`.

## Reproduction

See [README.md](README.md). From the repository root:

```sh
make -C coqettu/codex
make -C coqettu/codex check
bash coqettu/codex/lift.sh
```

The last command needs Ghidra/PyGhidra and permission to update Ghidra's user
configuration. Its command prefix is already authorized in this session.
Temporary project: `/tmp/coqettu-codex-ghidra/musl_x86`;
program: `ld-musl-i386.so.1`. Source binary SHA256:
`8affe9226ae00e51301465232d5ca760c186aab1142f715770bc7be5c3b698de`.
