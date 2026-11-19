# Codex i386 verification

This directory follows [the CoqEtTu assignment](../README.md). Function lifts,
specifications, proofs, and shared Rocq libraries are under `x86/`.
The completed set contains 82 function proofs with correctness and ABI-return
contracts; 82 exported functions and two internal PIC thunks have reproducible
lifts. See [ROADMAP.md](ROADMAP.md) for coverage, assumptions and outstanding work.

Build with Rocq 9.1.1 from the repository root:

```sh
make -C coqettu/codex core   # if the Picinae prerequisites are not built yet
make -C coqettu/codex
make -C coqettu/codex check # independently recheck compiled proof terms
make -C coqettu/codex smoke # execute checks against the exact 32-bit musl ELF
```

Each Rocq compiler/checker process has an 8 GB virtual-memory limit. No changes to
the repository-wide `_CoqProject` are needed. The default target typechecks every selected lift and shared proof library.
`check` also verifies the binary hash, global instruction addresses and sizes,
and coverage of every instruction reachable in the disassembly of each lift.
It writes an inventory to `.build/lift_manifest.json`. These checks do not
establish semantic correctness of the lifter.

`x86/audit.v` prints the logical assumptions of the completed correctness and
return theorems. This diagnostic script is loaded directly for the audit,
without compiling a duplicate copy. The audit inventory must cover both contracts
for every function proof source. They use Picinae's existing functional-extensionality
axiom;
they do not depend on admitted function proofs.

`smoke` requires a compiler with i386 code generation and permission to execute
i386 system calls. It uses musl itself as the program interpreter, disables
compiler builtins, and checks the completed function families, alignment cases,
boundary values, signed wide-character ordering, string mismatch positions,
backwards byte searches, 32/64-bit first-set-bit functions, wide fills with
surrounding canaries, 64-bit absolute values returned in EDX:EAX, wide-string
lengths, bounded byte-string lengths, optimized forward byte searches,
and wide classifications across the Unicode range plus WEOF.
The native checks passed in this workspace; they complement the proofs.

To reproduce the lifts:

```sh
bash coqettu/codex/lift.sh
```

Set `GHIDRA_INSTALL_DIR` to use another Ghidra installation, and optionally set
`COQETTU_GHIDRA_PROJECT_DIR` / `COQETTU_GHIDRA_PROJECT_NAME`. Set
`COQETTU_LIFT_OUTPUT_DIR` to reproduce into a fresh directory for comparison.
The script checks the binary hash, uses strict global-address lifting, requires
a fresh lift for every expected function, and rejects Ghidra post-script
exceptions. It also runs `lift_support.sh`, which checks the internal
`pc_thunk_bx` and `pc_thunk_ax` at their fixed addresses against each thunk's exact four instruction bytes.
The default project is under `/tmp`; its loss does not lose any proof source.

The shared lifter's committed source is pinned in `lifter_base/` with commit and
file hashes, so concurrent changes elsewhere do not change these lifts. The
Codex-local adapter recognizes Ghidra's exact register-to-register BSF32 graph
and replaces its backward branch with 32 guarded iterations. Other backward
branches remain rejected. `make -C coqettu/codex adapter-check` checks recognition,
rejection cases and scan behavior. The `ffs` family lifts use this adapter;
their functional proofs are tracked separately in the roadmap.

The i386 GS-base name adapter maps only Ghidra's reviewed `GS_OFFSET` register
at register-space0x114 with width32 to Picinae's existing `R_GS_BASE`. The local
SLEIGH definition exports that register as the GS linear base. Malformed layouts
are rejected; other registers and architectures retain their strict behavior.
The adapter does not change GS loads or assume locale data. The saved p-code
fixture and rejection tests are under `tests/`; all eight adapter tests pass.

For each completed function, `*_correct` gives the invariant-based partial
correctness theorem for any containing program; `*_returns` states the result,
memory/register frame, saved return address, and ESP adjustment after RET.
Neither theorem claims termination or successful access to concrete machine
memory. The lifted IL and Ghidra's instruction semantics remain trusted inputs.

The `bcmp`, `iswblank`, `ispunct`, `strnlen`, `wcsnlen` and locale-wrapper contracts compose existing callee proofs.
Their containing programs must include the caller, PIC thunk and callee lifts.
`i386_calls.v` closes callee invariants at foreign code addresses so a missing
callee instruction cannot be mistaken for a successful return. Their exact
stack-memory snapshots include the nested return-address writes.

`wcslen` derives its first-NUL index from execution. Its exact result accounts
for the binary's signed pointer subtraction and arithmetic shift. A separate
corollary proves agreement with the character count when the byte difference
is representable as a signed 32-bit value; no length bound is a caller premise
of the machine-level correctness theorem.

`memchr` covers the initial byte scan, four-byte XOR/mask scan, bounded byte
tail, and restoration of all four saved registers. Its exact stack-memory
snapshot includes an optional endpoint word. `strnlen` composes that theorem;
it requires its input region to avoid the nested-call stack frame and address
zero so that the wrapper's NULL test cannot discard a real match. Its zero bound
still permits a NULL pointer, and no terminator or length witness is assumed.

The current non-leaf coverage includes the bounded-length wrappers, ASCII
punctuation classification, 12 ASCII locale classifiers, two locale case
converters, and `iswdigit_l`, `iswxdigit_l`, `iswblank_l`, `iswcntrl_l`. Their actual CALL
instructions are verified by composition with the PIC thunk and existing callee
contracts. `i386_unary_call.v` supplies shared argument-copy, return-address and
stack-frame lemmas. Locale words are ignored by this binary; the predicates and
converters cover every character bit pattern. `tolower_l` and `toupper_l`
compose both return sites of their callees. `iswblank_l` verifies a nested
non-leaf callee and all eight stack-word writes in its 64-byte footprint.
`ispunct_l` accounts for six or eight nested stack-word writes according to the
character's graphical range. `wcsnlen` handles both `wmemchr` return sites and
states its exact signed-shift result, with a separate count-agreement corollary.

`strcoll_l` and `wcscoll_l` compose the checked byte and wide-string comparators.
This musl binary ignores their locale word and uses lexical comparison.
`i386_binary_call.v` supplies the two-argument stack snapshots and a prefix
transport proof: characters through the first NUL retain their original values
across caller stack writes. The contracts protect each string through its first
NUL from the 40-byte nested frame, with no input length or stop witness. Exact
memory includes all seven caller/callee stack-word writes.

`wcschr` verifies both the nonzero-character scan and the NUL-search path that
calls `wcslen`. Its first-stop result is stated over original memory, with no
caller length or stop witness. The input through its first NUL avoids the
32-byte call frame. The exact memory snapshot distinguishes two and four
effective stack-word writes; the additional store of the unchanged first
argument is proved idempotent. `i386_wsearch.v` proves that scaling the exact
signed `wcslen` result by four reconstructs the byte offset for every machine
representation, so this contract needs no signed-length bound.

`wcsrchr` composes `wcslen` with a descending last-match scan. Its contract
requires a base address of at least four and a non-wrapping input object through
its first NUL, disjoint from the 32-byte nested frame. These conditions support
the binary's unsigned pointer stop test. The six-word memory snapshot accounts
for three saved registers, the PIC return, copied pointer and callee return.
`i386_backward.v` supplies stride-independent cursor and exhaustion lemmas.
No input length or stop witness is required, and a separate corollary identifies
the first-NUL pointer returned for a zero needle.

`strrchr` composes `strlen` and `memrchr`, deriving the reverse-search bound
from execution. `strchrnul` covers byte alignment, the combined zero/XOR word
mask, byte tail and the zero-needle `strlen` call. Both state first/last-match
results over original memory, exact nested stack writes, and the full ABI frame.

`strchr` composes `strchrnul`, then checks the returned byte to distinguish a
match from an absent needle. Its exact snapshot includes the nested 80-byte
frame, and the result and full ABI return are stated over original memory.

`wctrans` recognizes the ELF's exact `toupper` and `tolower` names through
composed `strcmp` calls, returning descriptors 1 and 2 respectively, or zero.
Its precondition models the fixed static bytes, and its memory snapshot
includes conditional argument and return-address overwrites.

`wctrans_l` composes the nested name lookup for every locale word. It preserves
recognition over original memory and records the exact 72-byte nested stack
snapshot, including both conditional comparisons and both PIC calls.

`wctype` verifies the fixed 12-name table, first-byte call avoidance, repeated
`strcmp` calls and the first matching descriptor or zero. The result uses
original input bytes; an execution-derived comparison history specifies exact
stack overwrites. `i386_named_string.v` relates finite static-name equality to
an executed comparator's zero result without assuming an input stop witness.

`wctype_l` composes the classification-name lookup for every locale word, with
original-name result transport and the exact 88-byte nested stack snapshot.
Its comparison history is derived from execution. Current milestones and the
next non-leaf comparison task are recorded in [WORKLOG.md](WORKLOG.md).

`strcasecmp` composes all four actual `tolower` call sites and both callee
returns. It states the exact ASCII-folded first-difference result over original
strings. Shared overwrite lemmas collapse the reused argument/return slots to
the terminal second-byte argument and its final saved return address.

`strcasecmp_l` forwards both strings and ignores every locale word. Its
80-byte nested snapshot records twelve effective word writes. Prefix and
stopping-byte transport relate the nested comparison and exact result to the
wrapper's original memory. Native checks cover every byte pair on all
alignments, mixed-case prefixes, early NULs, input preservation and ten locale
representations.

`strncasecmp` proves the full32-bit bounded comparison, with an execution-derived
stop, exact folded-byte difference and optional count/call-slot writes. Count0
reads neither input. `strncasecmp_l` composes it through a96-byte nested frame
for every locale word; no caller length or stopping witness is required.

`index` and `rindex` compose the first/last-byte searches through112/72-byte
nested frames. Their results use original input memory and all32-bit character
representations, including NUL. Exact snapshots preserve the original return
address and complete ABI frame.

`strcoll` and `wcscoll` retain both GS loads and the fetched locale word in the
exact snapshot. Their checked callees ignore the locale and establish lexical
comparison in original memory through the72-byte nested frame. No locale-value
restriction or additional thread-layout premise is assumed for these partial
correctness contracts.
