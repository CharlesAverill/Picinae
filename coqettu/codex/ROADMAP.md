# Codex / musl i386

Assignment: `alpine_musl/x86/lib/libc.musl-x86.so.1`, musl-1.2.6-r6.
All work is isolated here; do not consult the other models' directories.

## Active continuation

See [WORKLOG.md](WORKLOG.md) for the current task, milestone checklist, last
validated checkpoint and interruption/resume instructions. Active target:
`strncat`, after completing `strcoll` and `wcscoll`.

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
  - `isalpha`, `isalnum`, `isblank`, `iscntrl`, `isspace`, `isxdigit`: exact
    ASCII classifications, including full 32-bit representations, with shared
    case-folding and interval proofs.
  - `tolower`, `toupper`: exact ASCII case conversion or unchanged input,
    both return sites and the full ABI frame, including EOF representations.
  - `wcscmp`, `wcsncmp`: signed wide-character ordering, equal nonzero
    prefixes, mismatch/common-NUL stopping, and bounded-count exhaustion.
    No caller-supplied string length or stop witness.
  - `abs`, `labs`: exact binary results for every argument, plus agreement
    with mathematical signed absolute value away from INT_MIN/LONG_MIN.
  - `llabs`, `imaxabs`: exact 64-bit absolute-value representations in EDX:EAX,
    with word-borrow arithmetic, EBX restoration, and signed mathematical
    agreement away from INT64_MIN. The minimum-value bit pattern is also proved
    and confirmed against the native binary.
  - `strlen`: alignment scan, four-byte zero detection and final byte scan;
    the result is an existential first-NUL index, never an input assumption.
  - `wmemchr`: bounded wide-character search, both return sites and zero count;
    no precomputed match witness or artificial count limit.
  - `memcmp`: byte comparison loop, exact first-difference result, EBX save
    and restoration, stack memory frame, transport back to original buffers.
  - `memchr`: initial byte scan, optimized four-byte XOR/mask loop and byte
    tail; first-match/minimality or exhausted-prefix result in original memory,
    all four register restores, and exact optional-local stack snapshot.
  - `strnlen`: composes the PIC thunk and `memchr` proof, returning the first
    NUL below the bound or the bound after all nonzero bytes. It describes all
    ten nested-call stack-word writes plus the optional endpoint and restores
    the full ABI frame. A zero bound permits a NULL pointer.
  - `wcsnlen`: PIC-thunk and `wmemchr` call composition, both callee return
    sites, exact signed pointer subtraction/SAR result, count-agreement
    corollary, six-word stack snapshot, and the full ABI return contract.
  - `isalnum_l`, `isalpha_l`, `isblank_l`, `iscntrl_l`, `isdigit_l`,
    `isgraph_l`, `islower_l`, `isprint_l`, `isspace_l`, `isupper_l`,
    `isxdigit_l`, `iswdigit_l`, `iswxdigit_l`: actual non-leaf PIC call
    wrappers forwarding every character representation to their checked
    classifiers. Locale words are ignored. Each has an exact four-word
    memory snapshot and full ABI restoration; shared unary-call lemmas
    provide the argument and return translation.
  - `ispunct`: checks the graphical interval, conditionally composes the
    `isalnum` proof, and returns the exact ASCII punctuation predicate.
    Its exact memory snapshot records two or four stack-word writes according
    to the input, with every 32-bit character representation covered.
  - `tolower_l`, `toupper_l`: compose both return sites of their existing
    case-conversion callees, with the exact four-word stack snapshot, every
    character/locale word, and full ABI restoration.
  - `iswblank_l`: composes the already non-leaf `iswblank` proof, including
    its PIC-thunk and `isblank` calls. The exact memory snapshot contains eight
    word writes in a 64-byte nested stack footprint.
  - `ispunct_l`: composes the non-leaf conditional `ispunct` contract. Six or
    eight stack-word writes are retained according to the graphical test;
    the original argument, saved registers and return address survive both paths.
  - `iswcntrl_l`: forwards all character and locale words to the checked
    wide-control classifier, with an exact four-word snapshot and full ABI frame.
  - `strcoll_l`, `wcscoll_l`: compose `strcmp` and `wcscmp`, respectively,
    and state their exact lexical byte difference / signed wide ordering.
    This binary ignores the locale word. The seven-word memory snapshot
    includes both callee register saves in the 40-byte nested footprint.
    Original-string prefix transport derives callee preconditions and returns
    the result in original memory without a caller length or stop witness.
  - `wcschr`: conditional `wcslen` call for a NUL needle and a direct loop
    for all other 32-bit character patterns. The result identifies the first
    match or first NUL in original memory, with no input length/stop witness.
    The exact snapshot distinguishes two/four effective stack-word writes;
    the zero path's extra argument re-store is proved idempotent. A checked
    signed-shift/scaling lemma reconstructs the pointer without a length bound.
  - `wcsrchr`: composes `wcslen` and checks the descending scan's last-match
    or complete-absence result in original memory. The first-NUL index comes
    from execution. The contract covers all needle representations, a
    non-wrapping wide input object and the six-word nested stack snapshot.
    All three saved registers and the complete ABI frame are restored. A
    zero-needle corollary identifies the first-NUL pointer. Generic backwards
    cursor lemmas separate live reads from the exhausted position.
  - `strrchr`: composes actual `strlen` and `memrchr` calls, derives the
    terminator-inclusive count from a non-NULL, non-wrapping input object,
    and transports the last-match result to original memory. The exact ten-word
    write sequence tracks reused argument/return slots and both callee saves;
    the full ABI frame is restored without a caller length or match witness.
  - `bcmp`: nested PIC-thunk and `memcmp` calls, exact first-byte difference,
    zero iff equal regions, all seven stack-word writes and the full ABI frame.
  - `iswblank`: PIC-thunk and `isblank` calls, exact tab/space predicate for
    every wint_t representation, four stack-word writes and the full ABI frame.
  - `iswdigit`, `iswxdigit`, `iswcntrl`: exact wide-character classifications,
    including the additional Unicode control ranges, with full ABI returns.
  - `wcslen`: first zero in the four-byte address orbit, no input length
    witness, exact signed-pointer-difference result and agreement with the
    mathematical character count when the difference is representable.
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
- `strchrnul` verifies the optimized first-match-or-NUL scan, its zero-needle
  `strlen` call, all four saved registers and conditional 48-byte call frame.
- `strchr` composes `strchrnul`, checks the returned byte and distinguishes the
  first match from absence, with an exact conditional 80-byte nested frame.
- `wctrans` recognizes exactly `toupper` and `tolower` through composed
  `strcmp` calls, returning descriptors 1/2 or zero, with a conditional memory
  snapshot and the full ABI frame.
- `wctrans_l` composes that lookup for every locale word, preserving original
  name bytes and the exact 72-byte nested stack snapshot.
- `wctype` verifies all 12 fixed classification names, first-byte call
  avoidance and repeated `strcmp` calls. Its first matching descriptor or zero
  result is stated over original input memory, with exact call-history writes.
- `wctype_l` composes that lookup for every locale word, with original-name
  result transport and an exact 88-byte nested stack snapshot parameterized
  by the comparison history derived from execution.
- `strcasecmp` composes all four `tolower` call sites and both callee return
  sites. It proves the ASCII-folded first-difference result in original memory
  and collapses overwritten stack slots to the exact final argument/return pair.
- `strcasecmp_l` composes that comparison for every locale word, transporting
  both original string prefixes and the exact result through an 80-byte frame.
  Its snapshot includes twelve effective word writes.
- `strncasecmp` composes four actual `tolower` calls and the EAX PIC thunk.
  Its execution-derived stopping index is below the full32-bit count; zero
  count reads no input. Exact memory includes the optional saved count and
  overwritten call words. No extra count or pointer-wrap bound is assumed.
- `strncasecmp_l` forwards all three arguments and ignores every locale word.
  It preserves the original-memory bounded result and exact96-byte nested frame.
- `index` and `rindex` compose the completed first/last-byte searches. Original
  memory determines the first match or execution-derived NUL/last match;
  exact nested stack frames are112/72 bytes. All character words are accepted.
- `strcoll` and `wcscoll` retain both thread-locale loads, compose the checked
  locale wrappers and prove original-memory lexical comparisons. Exact72-byte
  snapshots record the fetched locale word with no restrictions on its value.
- Every correctness theorem supports an arbitrary containing program extending
  its lift (and the linked thunk/callee lifts for the call wrappers).
  Completed return contracts include the saved return address, stack pop, memory frame, callee-saved registers, and access-permission frame.
- Independent kernel recheck passed for all 82 completed functions;
  their 164 public correctness/return contracts passed the logical-assumption audit.
- Native checks against the exact musl ELF pass, including string alignments,
  first/last mismatch positions, signed wide ordering, zero counts, 32/64-bit
  first-set-bit results, wide fills with surrounding canaries, and 64-bit
  absolute values returned in EDX:EAX, wide-string lengths and wide-character
  classification over the Unicode range and WEOF representations, locale-word
  boundary patterns, ASCII punctuation and both case conversions, optimized
  forward byte searches on all alignments, and bounded string lengths before,
  at and after the terminator.
- Provenance checker validated 84 lifts and 1124 reachable instructions against
  ELF disassembly (hash, global addresses, instruction sizes, complete coverage).
  These include 82 exported routines and two exact-byte-pinned internal PIC
  thunks. The full lifting script reproduced all 84 files byte-for-byte in a fresh
  output directory, without modifying the checked sources.
- Assumption audit found only Picinae's pre-existing
  `FunctionalExtensionality.functional_extensionality_dep` axiom; no admitted
  functional-correctness theorems. This is not a claim of an axiom-free foundation.

## Next steps

1. Verify `strncat`: compose the proved `strlen`, then bounded copying and NUL
   write. Shared byte-copy and exact stack support compile; native checks pass.
   Caller invariants are being checked. See `WORKLOG.md`.
2. Extend non-leaf string coverage (`strcpy` / `strcat` and related wrappers)
   by verifying the required callees and then composing their contracts.
3. Refine bounded-search preconditions to protect only the prefix through
   the first stop, without introducing a caller-provided length witness.
4. Add termination/access-safety results for selected completed loops while
   preserving their current machine-level functional contracts.

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
- Every exported routine in the last fully validated checkpoint has correctness
  and return contracts. Preparatory lifts and active work are tracked in
  `WORKLOG.md`. Future non-leaf targets must include contracts for their callees;
  a lift alone is not a correctness result.
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
- `wcsrchr` requires the original wide input through its first NUL to be a
  non-wrapping object with base at least four and no overlap with the 32-byte
  call frame. The unsigned backwards stop comparison needs these address
  conditions; no artificial signed-length bound is imposed. The six actual
  word writes and restoration of EDI/ESI/EBX are part of the return contract.
- `wcschr` protects its original string through the first NUL from the
  32-byte nested-call frame. The nonzero-needle path changes two stack words;
  the NUL path changes four and re-stores its unchanged first argument. Input
  pointers and returned pointers follow the model's wrapping address semantics.
- `strcoll_l` / `wcscoll_l` protect both input strings through their first
  NUL from the 40-byte nested-call stack region. This is expressed by a prefix
  predicate over original memory, not a supplied length or termination witness.
  The proof transports nonzero prefixes back to original memory before deriving
  the callee's two-save-slot disjointness. Locale words are ignored by this ELF.
- `bcmp` requires both compared regions to avoid the 36-byte nested-call stack
  footprint. Its exact memory snapshot has seven word writes; `iswblank` has
  four writes in its 32-byte call footprint and no buffer nonoverlap premise.
- `strnlen` requires the input region to avoid its 52-byte nested-call frame
  and address zero. In the wrapping machine model, a match can itself have
  address zero; excluding that invalid C-object address prevents the wrapper
  from discarding a real match. The empty input region still permits NULL.
  `wcsnlen` applies the same distinction to its 4*n-byte wide input region.
- The search contracts conservatively protect the full bounded input region
  from stack writes, even when an early match would permit a shorter protected
  prefix. Relaxing this without introducing a caller length witness is future work.
- `memchr` requires input disjointness from its 20-byte frame. The four saves
  persist after return, together with an optional endpoint word if the word
  setup path ran. The scan needs no match witness or alignment premise.
- `wcslen` and `wcsnlen` use SAR on a signed pointer difference. Its full machine theorem
  covers the complete four-byte address orbit; the mathematical count corollary
  requires a representable signed byte difference (fewer than 2^29 characters).
  The main machine-level theorems do not impose that extra count restriction.
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
- A callee's implicit exit at an absent instruction is insufficient for call
  composition inside a larger program: the caller's code exists there.
  `closed_invs` asserts False at foreign frontiers, with checked extension and
  `may_call` lemmas. Only the explicit callee RET supplies a postcondition.
- For optimized searches, an endpoint index with a multiple-of-four gap is
  enough to justify word skips. The byte tail can handle any remaining count;
  no invariant about alignment or proximity to the end is needed for correctness.
- Repeated-byte multiplication can be proved lane by lane using quotient and
  remainder decompositions; combine XOR lane identities with the existing
  checked zero-byte mask before reasoning about memory scans.
- Exported weak aliases can have empty `objdump --disassemble=name` output.
  Resolve the ELF symbol bounds, then disassemble that exact address interval;
  retain hash, instruction-size and full reachable-coverage checks.
- To derive a string callee's precondition after caller stack writes, first
  transport the callee's observed nonzero prefix back to original memory by
  induction. Original-memory nonoverlap then protects the next character,
  including a terminator, without assuming the answer in the caller contract.
- Represent a backwards cursor by one plus its current element index. Zero
  then denotes exhaustion before the base; place a cut after the pointer stop
  test so a character-read invariant always has an in-object index. The
  nonmatching suffix records that no later element matches.
- Arithmetic right shift followed by scaling can reconstruct a pointer even
  when the intermediate signed length does not equal the natural count.
  Prove the byte-offset identity over bits before imposing any length bound.
- An apparent write outside the local frame can be an idempotent argument
  re-store. Establish the load's original value and use `setmem_getmem` before
  adding an unnecessary buffer disjointness condition.
- When a callee itself writes to its stack, translate its reference memory
  through the caller frame before applying RET. Preserve both the outer CALL's
  return word and the caller's saved registers across every inner write.
- A conditional callee needs a conditional exact memory snapshot even when its
  enclosing locale wrapper is straight-line code.
- Descending-stack word separation can be reduced to differences of depths;
  keep store expressions out of `lia` and prove the modular arithmetic once.
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

- Reused call slots can be modeled exactly with `i386_call_pair.v`: the last
  argument/return pair shadows all previous pairs, avoiding a growing call
  history in the final contract. Preserve original input reads before using
  the stopped second-string byte in the snapshot.
- A generic callee continuation can return `nextinv'` for every trace tail.
  Returning the `nextinv` wrapper would add a fresh execution premise at each
  callback. Internal continuations must still be discharged at every actual
  caller site; public contracts retain only the architectural/string premises.
