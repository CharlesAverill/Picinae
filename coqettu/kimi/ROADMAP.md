# Kimi ARMv7 verification roadmap

Target: `coqettu/alpine_musl/armv7/lib/ld-musl-armhf.so.1` (musl 1.2.6-r6,
SHA-256 `30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e`).
All Kimi-specific Rocq artifacts live in `armv7/`.

## Open problems

- Every lifted return still contains an ignored `CALLOTHER` for the ISA mode
  switch. The `TB`/`ISAModeSwitch` registers now map to `R_T`, but the userop
  itself remains unmodeled. Current correctness claims stop immediately before
  the return instruction.
- The invalid-speed error paths of `cfsetispeed` and `cfsetospeed` are not
  covered by their current successful-path theorems.
- The memory-copy functions remain open.

## Next steps

1. Verify the memory-copy functions.
2. Model the `setISAMode` userop and extend correctness theorems through their
   actual return jumps.

## Solved problems

Forty-two functions have machine-checked partial-correctness proofs, all
generalized to arbitrary programs containing the verified instructions:

- Byte order: `htonl`, `ntohl`, `htons`, `ntohs`.
- Character conversion: `toascii`, `tolower`, `toupper`.
- Resolver memory access: `ns_get16`, `ns_get32`, `ns_put16`, `ns_put32`.
- Termios: `cfgetispeed`, `cfgetospeed`, plus successful valid-speed paths of
  `cfsetispeed`, `cfsetospeed`, and `cfsetspeed`, with exact termios and
  saved-stack memory. The `cfsetspeed` proof composes both setters, models its
  second call with speed zero, excludes termios writes that would corrupt saved
  LR/R3, and preserves the exact status-slot result under other aliasing.
- Absolute value: `abs`, `labs`, `llabs`, and `imaxabs`, including concrete
  modular behavior for minimum signed inputs and 64-bit register-pair borrow.
- Character classification: `isascii`, `isdigit`, `islower`, `isupper`,
  `isalpha`, `isgraph`, `isprint`, `isblank`, `iscntrl`, `isspace`, `isalnum`,
  `isxdigit`, and `ispunct`, including conditional Thumb `IT` blocks, early
  returns, and the `isalnum` caller/callee composition.
- Array/string functions: general proofs for `memcmp`, `strcmp`, `strlen`,
  `memchr`, and `strnlen`. `strlen` and `memchr` cover both byte-at-a-time and
  word-at-a-time loops; `memchr` includes its alignment scan, word loop, final
  byte scan, NULL result, and first-match pointer result. `strnlen` composes
  that contract with its actual caller and callee stack frames and returns the
  first NUL index below the bound, or the bound itself.
- Division: the signed 32-bit helper, its quotient/remainder wrapper, `div`, and
  `ldiv`. The proof covers unit, power-of-two, and general divisors through all
  32 unsigned stages, all four signed return sites, exact stack/result memory,
  and SP/LR/R4 preservation. A shared program and level-tagged invariant family
  compose the complete call chain; caller proofs stop before `POP`.

Additional results:

- Added Ghidra-to-Picinae aliases for ARM `NG/ZR/CY/OV`, one-bit staging flags,
  shift carry, `Q`, `TB`, and `ISAModeSwitch`. ARMv7 functions now lift with
  real signed/unsigned flag and Thumb `IT` semantics and type-check.
- Added the 32-bit `R_MULT_ADDR` temporary. Push/pop now retain their actual
  stack stores, loads, register updates, and SP updates instead of becoming Nops.
- Fixed `LZCOUNT` to use `width - N.size(x)` via `OP_BITWIDTH`, rather than the
  incorrect `width - popcount(x)`.
- `armv7_abs64.v` proves the arithmetic-shift sign mask and exact 64-bit
  absolute-value words. `armv7_zero32.v` proves that the classic word test
  detects a zero in any byte lane. `armv7_string.v` connects word loads to
  little-endian bytes. `armv7_memchr.v` extends the word test to equality with
  a replicated target byte.
- Proved non-writable code and generated well-typedness for every verified
  function. Proved memory/LR/callee-saved preservation where applicable;
  functions that write memory instead have exact post-memory specifications.
- Passed ordered builds under an 8 GB memory cap. `Print Assumptions` for every
  correctness theorem reports only Picinae's existing functional-extensionality
  dependency. No proof is admitted.

## Useful lessons

- Ghidra adds image base `0x10000`, and ELF Thumb symbols have bit zero set:
  ELF `htonl` `0x426dd` becomes lifted entry `0x526dc`.
- Put a cut at every conditional instruction and join. Split the input into
  concrete comparison cases before `arm7_step`; otherwise an `ITE` can leave an
  unevaluated optional exit and stall symbolic execution. Inspect actual branch
  destinations rather than assuming a goal order.
- When a flag invariant wraps its condition in a specification definition,
  destruct that exact Boolean before stepping. For `LS/HI`, carry and zero are
  independent: zero after `CMP x,#31` means `x = 31`, while `x <= 31` is
  `NOT CF OR ZF`.
- Picinae normalizes subtraction-based zero tests to comparisons against the
  original input. `msub_eqb_spec` proves
  `(x ⊖ y =? z-y) = (x mod 2^32 =? z)` for `y <= z < 2^32`.
- `solve_range_movhi` in `armv7_common.v` handles recurring conditional moves.
- For compound loop invariants, split conjunctions before `elimstore` so each
  subgoal retains its frame hypotheses. Avoid blanket `psimpl` over large store
  terms, and clear symbolic-memory hypotheses before calling `lia`/`nia`.
- For calls, use a tagged multi-function invariant family with `perform_call`.
  Keep the callee store folded and prove its few relevant register and memory
  equalities separately; normalizing every postcondition field can expand the
  entire updated store and take many minutes.
- `ISA_invhere` abstracts register values in the goal. If a later equality needs
  the unabstracted expression, execute the final instruction with
  `NIStep`/`ISA_symbolic_interp`, then use `arm7_step` to enter the invariant.
  Post-call invariants must retain restored registers such as SP and R4 when
  later caller instructions use them.
- When a callee writes an arbitrary pointer, a normal-return proof needs
  disjointness from its saved LR and any restored registers used by the caller.
  Four-byte `getmem_frame` needs both modular distance directions. Reduce store
  projections with `update_updated`/`update_frame`, not `psimpl` over the entire
  assigned memory, and prove saved-LR reads as separate small lemmas.
- Apply `getmem_mod_l` with explicit width, endianness, length, memory, and
  address. Leaving memory as an evar in a rewrite caused a runaway compile.
  Splitting the four byte-lane arithmetic proofs also avoids a slow shared `nia`.
- Check immediate constants against the disassembly, not nearby functions:
  `isgraph` compares against `0x5d`, while `isprint` uses `0x5e`.

## Verification commands

Run from `coqettu/kimi/armv7/`:

```sh
ulimit -v 8000000
for f in \
  armv7_common.v armv7_abs64.v armv7_zero32.v armv7_string.v armv7_memchr.v \
  htonl_armv7.v htonl_proof.v ntohl_armv7.v ntohl_proof.v \
  htons_armv7.v htons_proof.v ntohs_armv7.v ntohs_proof.v \
  toascii_armv7.v toascii_proof.v \
  ns_get16_armv7.v ns_get16_proof.v ns_get32_armv7.v ns_get32_proof.v \
  ns_put16_armv7.v ns_put16_proof.v ns_put32_armv7.v ns_put32_proof.v \
  cfgetispeed_armv7.v cfgetispeed_proof.v cfgetospeed_armv7.v cfgetospeed_proof.v \
  cfsetispeed_armv7.v cfsetispeed_proof.v cfsetospeed_armv7.v cfsetospeed_proof.v \
  cfsetspeed_armv7.v cfsetspeed_family.v cfsetspeed_proof.v \
  abs_armv7.v abs_proof.v labs_armv7.v labs_proof.v \
  llabs_armv7.v llabs_proof.v imaxabs_armv7.v imaxabs_proof.v \
  isascii_armv7.v isascii_proof.v isdigit_armv7.v isdigit_proof.v \
  islower_armv7.v islower_proof.v isupper_armv7.v isupper_proof.v \
  isalpha_armv7.v isalpha_proof.v tolower_armv7.v tolower_proof.v \
  toupper_armv7.v toupper_proof.v isgraph_armv7.v isgraph_proof.v \
  isprint_armv7.v isprint_proof.v isblank_armv7.v isblank_proof.v \
  iscntrl_armv7.v iscntrl_proof.v isspace_armv7.v isspace_proof.v \
  isalnum_armv7.v isalnum_proof.v isxdigit_armv7.v isxdigit_proof.v \
  memcmp_armv7.v memcmp_proof.v strcmp_armv7.v strcmp_proof.v \
  strlen_armv7.v strlen_proof.v memchr_armv7.v memchr_proof.v \
  strnlen_armv7.v strnlen_family.v strnlen_proof.v \
  ispunct_armv7.v ispunct_family.v ispunct_proof.v \
  FUN_0003046e_armv7.v FUN_000306fc_armv7.v div_armv7.v ldiv_armv7.v \
  division_program.v armv7_divstep.v signed_div_spec.v signed_div_stages.v \
  signed_div_entry.v signed_div_family.v signed_div_proof.v \
  divmod_family.v divmod_proof.v div_family.v div_proof.v \
  ldiv_family.v ldiv_proof.v
do
  rocq c -R ../../.. Picinae "$f" || exit
done
```
