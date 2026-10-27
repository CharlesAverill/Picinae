# Lifted GMP routines: contracts and invariant addresses

The lifts are from `libgmp.so.10.5.0`, SHA256
`2d6d19962673262eba388911974a90de5b7ac14d4da32a1c9666264a4e0a71e3`.
Addresses below are the actual addresses in the lifted programs, not offsets.
`B = 2^64`; `A(k)` and `U(k)` denote the natural numbers represented by the
first `k` little-endian limbs in the original input memories. A limb is eight
bytes. Counts are in limbs, while pointer offsets are in bytes.

The [GMP low-level function manual](https://gmplib.org/manual/Low_002dlevel-Functions)
describes the operand representation, carry/borrow return values, overlap
rules, and increasing-address copying. `add_nc`, `sub_nc`, and `add_n_sub_n`
are internal interfaces: their extra carry inputs, chunk size, and return
encoding here are determined from these lifts, not inferred from public
`mpn_add_n` documentation.

## Checked status

The lifted IL partial-correctness proofs are complete under the contracts
below. Refinement to the original ELF's dynamic-linking behavior remains open.

* `copyi_functional_correctness` in `amd64_gmp_copyi_proof.v` proves the full
  `satisfies_all` contract for the lifted copy routine, under `models` and
  `forward_safe`, including `n=0` and valid forward overlap.
* The four lifts contain 80 generated, kernel-checked step lemmas: 4 for copy,
  31 each for addition and subtraction, and 14 for the wrapper.
* `LimbArrays` in `Picinae_theory.v` supplies a reusable memory/natural-number
  model, prefix-copy facts, and carry/borrow equations.
* `amd64_gmp_specs.v` formalizes the complete addition/subtraction invariant
  address maps, including the additional instruction cuts below.
* `amd64_gmp_lemmas.v` proves the hardware carry/borrow equations, buffer
  extension, unread-suffix preservation, prefix composition, and prefix commit.
* `amd64_gmp_nc_proof.v`, `amd64_gmp_nc_vcs.v`, and
  `amd64_gmp_nc_control.v` prove every addition/subtraction verification
  condition: entry dispatch, all arithmetic cuts, tail stores, the nonfinal
  four-limb cycle, the final block, remainder dispatch, and returns.
* `nc_functional_correctness` and `nc_plain_functional_correctness` in
  `amd64_gmp_nc_correctness.v` prove the full standalone `satisfies_all`
  arithmetic contracts for both operations. Named specializations expose
  `add_nc`, `sub_nc`, `add_n`, and `sub_n`. Their preconditions are initial
  typing and argument registers, `0<n`, `8*n<=2^64`, `cin<=1` for the carry
  entries, and `forward_safe` from the destination to each source. These
  contracts stop before RET. Stronger call-ready theorems now conjoin ABI
  and outside-output memory-frame guarantees in `amd64_gmp_nc_preservation.v`
  and `amd64_gmp_copyi_preservation.v`.
* `amd64_gmp_linked.v` supplies a typed linked IL program with three assumed
  PLT jump bindings. Checked program/invariant transport and
  `amd64_gmp_family_proofs.v` establish the stronger leaf results in one fixed
  invariant family. This assumes the stated bindings; it is not a verified
  ELF linkage analysis. The original ELF's three PLT entries, GOT slots and
  relocation symbols have now been identified; the open
  [linking-model gap](roadmap.md#linking-model-gap-open) concerns the
  runtime resolved GOT targets, load-address/binding configuration,
  interposition, resolver choices and establishing stable GOT values.
  `amd64_gmp_plt_got.v` proves indirect/direct PLT step and whole-trace
  equivalence under explicit resolved-GOT predicates, then transfers the
  wrapper postcondition to the GOT-based IL program conditionally.
  Normal lazy binding can update GOT data without changing PLT instructions;
  the current fixed-stub model omits GOT reads and resolver execution. Its
  memory frames therefore do not cover resolver writes.
* `amd64_gmp_calls.v` proves local composition for all seven concrete wrapper
  CALL sites, including their PLT jumps and actual callee RET instructions.
  Caller-continuation obligations remain explicit premises. Input-snapshot
  bridge lemmas handle the stack push under memory separation assumptions.
* `amd64_gmp_wrapper_specs.v` now formalizes the wrapper address map as
  `wrapper_property`, including the three chunk routes, different committed
  prefix lengths between calls, the scratch sum, saved stack, and memory frame.
  The final wrapper theorem proves preservation of this complete invariant map.
* `amd64_gmp_wrapper_lemmas.v` checks chunk composition, input extraction,
  scratch commit, prologue saved cells and frame, and metadata preservation.
  `amd64_gmp_wrapper_machine.v` connects the signed CMP/JG and CMOVG expressions
  to mathematical index comparisons and `min(170,n-k)` under signed bounds.
* `amd64_gmp_wrapper_control.v` checks the linked-program epilogue and the
  zero-count entry/scratch dispatch. `add_n_sub_n_zero_correctness` in
  `amd64_gmp_wrapper_zero.v` proves whole-function correctness for `n=0`
  through all alias routes. `wrapper_exit_post` extracts the arithmetic,
  restored ABI, and outside-output/stack memory guarantee.
* `wrapper_vc_add_tail`, `wrapper_vc_sub_tail`, and `wrapper_vc_scratch_tail`
  check all three actual loop back edges and final return encodings. Their
  premises are the relevant callee-return invariants.
* Positive-length entry, alias dispatch and metadata initialization are checked
  in `amd64_gmp_wrapper_init.v`, `amd64_gmp_wrapper_entry.v` and
  `amd64_gmp_wrapper_dispatch.v`, reaching all three loop-header invariants.
* All seven argument setups are checked in the three `wrapper_*_header.v`
  modules, `amd64_gmp_wrapper_second_calls.v`, and
  `amd64_gmp_wrapper_copy_setup.v`. Their callbacks receive a current type
  model, exact memory/register/argument packets, and proved leaf preconditions.
  The predicates in `amd64_gmp_wrapper_call_conditions.v` establish count,
  carry, alias safety, return-cell separation and source protection from the
  CALL push. `amd64_gmp_wrapper_call_bridge.v` invokes the existing checked
  CALL/PLT/RET adapters from these packets.
* `amd64_gmp_wrapper_return_support.v` composes CALL's pushed-cell write with
  the callee output frame, preserves metadata/saved stack and original inputs,
  and appends returned arithmetic chunks. All seven return-state certificates
  are proved in `amd64_gmp_wrapper_first_returns.v`,
  `amd64_gmp_wrapper_scratch_first_return.v`,
  `amd64_gmp_wrapper_second_returns.v`,
  `amd64_gmp_wrapper_scratch_second_return.v` and
  `amd64_gmp_wrapper_copy_return.v`.
* `add_n_sub_n_functional_correctness` in
  `amd64_gmp_wrapper_correctness.v` proves whole-function partial correctness
  in `gmp_linked`, including zero and positive counts and all three alias
  routes. `add_n_sub_n_post_at_return` exposes both arithmetic equations,
  encoded return value, restored ABI and memory frame at the root pre-RET
  point. All seven call continuations are discharged; the public theorem
  requires the trace entry and `wrapper_pre`, and asserts no termination.
  This completes the IL proof while leaving the ELF linking-model gap open.

All added `.v` files are included in `_CoqProject`. `make -j2` passed,
and an independent `rocqchk -silent -R . Picinae` check of
`Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_preservation`,
`Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_preservation`, and
`Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_calls`, the wrapper zero theorem and all three
wrapper tail modules, including their dependencies, passed. The expanded
independent check of positive entry/dispatch, three header modules,
second-call setups and the call bridge also passed, together with normal
compiler checks and assumption inspection. Independent checking rooted at the
complete wrapper theorem passed. The added GOT bridge also passed normal
compilation and independent checking, including its dependencies.
The GOT trace-equivalence theorem uses no axioms. The whole-function and
transferred GOT wrapper theorem assumptions
report only the existing `FunctionalExtensionality.functional_extensionality_dep`
axiom.
There are no `Admitted`, `Abort`, or added axioms in the proof files.
Regenerate the steps after building Picinae with
`python3 Examples/libgmp_so_10_5_0/generate_gmp_steps.py` (or pass one function name).
The compiler backend caches temporary declarations using `-vos`, checks each
new lemma with `-vok`, then checks the entire resulting source with the normal
compiler before updating a lift. No skipped proof is accepted as final output.

## `__gmpn_copyi`

Inputs: `RDI=d`, `RSI=p`, `RDX=n`. The postcondition is the exact memory
`copied m d p n`: overwrite precisely `8*n` bytes at `d` with the original
`8*n` bytes at `p`. There is no specified return value (the C function is
void). The exit point is immediately before `RET`.

`copyi_regs` says the first `k` limbs have been copied, `RSI=p+8*k`, and
`RDI=d+8*k-8`, with register addresses reduced modulo `B`. `forward_safe`
says a completed destination prefix never overlaps the unread source suffix.
The proved `forward_safe_ordered` lemma supplies this property when both
regions fit in the address space and either `d<=p` or `p+8*n<=d`. This includes
identical pointers and downward overlap.

| Address | Natural-language invariant |
| --- | --- |
| `0x15b186` | Entry memory and the three input registers have their specified values. |
| `0x15b190` | Exactly `k` limbs have been copied; at least four remain; `RDX=n-k-4`. The four-limb block has not yet been loaded. |
| `0x15b1bc` | Exactly `k` limbs have been copied; between zero and three remain; `RDX=(n-k)-4` modulo `B`. |
| `0x15b1cf` | The optional odd limb has been copied; zero or two limbs remain; `RDX=2147483646+(n-k)/2`. Its low bit selects the two-limb tail. |
| `0x15b1e2` | All `n` limbs are copied, with the exact memory frame expressed by `copied`. |

The large positive constant in the second tail invariant records the
zero-extended 32-bit shift of the underflowed counter. Treating this as a
64-bit shift would give the wrong invariant. The copy proof also covers
`n=0`, though GMP's general public `mpn` contract normally requires `n>0`.

## `__gmpn_add_nc` and `__gmpn_sub_nc`

Inputs: `RDI=d`, `RSI=u`, `RDX=v`, `RCX=n>0`, `R8=cin` where `cin<=1`.
Addition produces `R + B^n*RAX = A(n)+U(n)+cin`; subtraction produces
`R+U(n)+cin = A(n)+B^n*RAX`. In both cases `RAX<=1`. These equations use
natural-number arithmetic, so subtraction does not silently truncate an
underflow to zero. The embedded ordinary `add_n`/`sub_n` entries have `cin=0`.

`nc_invset` in `amd64_gmp_specs.v` shares a single address map: every subtract
address is the corresponding add address plus `0x260`. `nc_prefix` expresses
the arithmetic equation for the committed output prefix together with zero,
one, two, or four pending result limbs in R8--R11. CF is the carry/borrow at
the end of that combined prefix. `unread` preserves the original input
suffixes, allowing the invariant to describe exact in-place operations.
The register-pointer and preloaded-limb facts accompany these equations.

| Addition address | Subtraction address | Natural-language invariant |
| --- | --- | --- |
| `0x1284e0` | `0x128740` | Carry-input entry, original memory and six input registers. |
| `0x128500` | `0x128760` | Ordinary entry, original operands and count, zero initial carry/borrow. |
| `0x128517` | `0x128777` | A correct committed prefix; one to three remaining limbs; RAX is the remainder count; CF is the incoming carry/borrow for the tail. |
| `0x128527` | `0x128787` | Two or three limbs remain; R8 contains the first input limb; RAX is the remainder minus one. |
| `0x128532` | `0x128792` | Two-limb tail, first result limb pending in R8, second input limb in R9; RAX=0. |
| `0x128540` | `0x1287a0` | Three-limb tail, first two input limbs preloaded; RAX=1. |
| `0x12854b` | `0x1287ab` | Three-limb tail, first two result limbs pending, third input limb in R10. |
| `0x128594` | `0x1287f4` | Correct prefix of a multiple of four limbs; first two input limbs preloaded; RCX counts further four-limb blocks; ZF records whether RCX is zero; RAX=n mod 4. |
| `0x128560` | `0x1287c0` | Nonfinal four-limb block, all four input limbs preloaded. |
| `0x128567` | `0x1287c7` | Nonfinal block, first two results pending, last two input limbs preloaded. |
| `0x12856f` | `0x1287cf` | Nonfinal block, all four results pending, CF is the outgoing block carry/borrow. |
| `0x12859e` | `0x1287fe` | Final full block, all four input limbs preloaded, RCX=0. |
| `0x1285a9` | `0x128809` | Final block, first two results pending; RSI has advanced by four limbs. |
| `0x1285b1` | `0x128811` | Final block, all four results pending; RSI has advanced; RDX is about to advance. |
| `0x1285ca` | `0x12882a` | Full blocks committed, zero to three limbs remain, RAX is that count plus one before DEC. |
| `0x128526`, `0x12853f`, `0x12855d`, `0x1285d4` | `0x128786`, `0x12879f`, `0x1287bd`, `0x128834` | Full output arithmetic equation and carry/borrow returned in RAX, immediately before RET. |

The additional instruction cuts make the transient register states explicit:

| Addition address | Subtraction address | Natural-language invariant |
| --- | --- | --- |
| `0x12851e` | `0x12877e` | One-limb tail, input in R8, RAX=0, arithmetic not yet performed. |
| `0x128521` | `0x128781` | One-limb tail result pending in R8; CF is its outgoing carry/borrow. |
| `0x128524` | `0x128784` | One-limb result committed; full output equation holds with CF; RAX=0. |
| `0x12852f` | `0x12878f` | Two-limb tail, both inputs preloaded, RAX=0. |
| `0x128536` | `0x128796` | Two-limb tail, both results pending. |
| `0x12853d` | `0x12879d` | Two-limb result committed; full output equation holds with CF; RAX=0. |
| `0x128544` | `0x1287a4` | Three-limb tail, all inputs preloaded, RAX=1. |
| `0x128547` | `0x1287a7` | Three-limb tail, first result pending; last two inputs intact. |
| `0x12854f` | `0x1287af` | Three-limb tail, all three results pending. |
| `0x12855a` | `0x1287ba` | Three-limb result committed; full output equation holds with CF; RAX=1 before SETC. |
| `0x128563` | `0x1287c3` | Nonfinal full block, first result pending; remaining inputs intact. |
| `0x12856b` | `0x1287cb` | Nonfinal full block, first three results pending; R11 is the final input. |
| `0x1285a2` | `0x128802` | Final full block, all inputs preloaded; RSI has advanced by four limbs. |
| `0x1285a5` | `0x128805` | Final full block, first result pending; three inputs remain preloaded. |
| `0x1285ad` | `0x12880d` | Final full block, first three results pending; R11 is the final input. |
| `0x1285d2` | `0x128832` | No tail remains; full output equation holds with CF; RAX=0 before ADC. |

The checked whole-function theorems require `forward_safe` for each source,
which ensures that stores preserve `unread`. Exact aliasing and nonwrapping
ordered/disjoint regions satisfy this contract under the appropriate bounds;
`forward_safe_ordered` supplies the ordered/disjoint specialization. The NC
invariant sets above are now proved inductive under those theorem hypotheses.

## `__gmpn_add_n_sub_n`

Inputs: `RDI=sum`, `RSI=diff`, `RDX=u`, `RCX=v`, `R8=n`.
The output is the pair `(A+U mod B^n, A-U mod B^n)`, with return value
`2*addition_carry + subtraction_borrow`. The outputs must not overlap each
other. The source/output alias cases select three different chunk loops.
Every iteration processes `q=min(170,n-k)` limbs. Pointer increments are
`0x550=170*8`, and the scratch buffer holds 170 limbs.

The concrete `wrapper_pre` contract requires `n+170<2^63`, `8*n<=2^64`,
nonwrapping arrays and stack, disjoint outputs, exact-or-disjoint source/output
aliases, and separation of all four arrays from the stack footprint
`[initial_RSP-0x5b0, initial_RSP)`. The footprint includes the pushed CALL cell
and excludes the caller's return cell. These assumptions define the currently
formalized contract. Whole-function partial correctness under this contract is
proved for `gmp_linked`; refinement to the original ELF linkage remains open.

At every chunk boundary retain the original input snapshots, the two correct
output prefixes, both carry/borrow values, the unread suffixes, the saved
callee registers, and the caller's return address. Keep stack metadata and
scratch-buffer writes disjoint from live operands and the saved stack.
The loop index increments by 170 even on a short final chunk: use
`min(index,n)` for the committed prefix, rather than claiming index<=n.

| Address | Natural-language invariant |
| --- | --- |
| `0x15c360` | ABI entry, original operands, count, stack and callee-saved registers. |
| `0x15c448` | Sum destination aliases an input; saved parameters and stack frame are established. |
| `0x15c508` | Both output destinations alias input regions; scratch-buffer route is required. |
| `0x15c3b8` | Sum destination is independent of both inputs; both prefixes of length `k` are correct; R14 is the chunk index; sum carry at [RSP], difference borrow at [RSP+8]. Addition may run first. |
| `0x15c480` | Difference destination is independent of both inputs; both prefixes are correct; R13 is the index; difference borrow at [RSP], sum carry at [RSP+8]. Subtraction must run first. |
| `0x15c538` | Both output regions alias inputs; both prefixes are correct; R13 is the index; compute sum into the stack scratch buffer before overwriting an input with the difference. |
| `0x15c3ef` | First loop's addition returned; RAX is the new sum carry; the current sum chunk is committed and the inputs needed by subtraction remain available. |
| `0x15c420` | First loop's subtraction returned; both chunks committed; RAX is the new borrow. |
| `0x15c4b7` | Second loop's subtraction returned; RAX is the new borrow; inputs needed by addition remain available. |
| `0x15c4e8` | Second loop's addition returned; both chunks committed; RAX is the new sum carry. |
| `0x15c568` | Third loop's sum is in scratch; RAX is its new carry; original input chunk is still available. |
| `0x15c597` | Third loop's difference is committed; scratch sum remains intact; RAX is the new borrow. |
| `0x15c5b1` | Scratch sum has been copied to its destination; both current chunks are committed. |
| `0x15c432` | Full two-output postcondition, encoded return value, stack frame ready to unwind. |
| `0x15c443` | Full two-output postcondition, restored caller stack and callee-saved registers, before RET. |
| `0x10c030` | External addition call: RDI/RSI/RDX/RCX/R8 form the chunk's add-with-carry contract. |
| `0x10b8f0` | External subtraction call: the analogous subtract-with-borrow contract. |
| `0x10bbe0` | External copy call: RDI/RSI/RDX form the scratch-copy contract. |

The last three addresses have **no instructions in the supplied wrapper
lift**. Generated wrapper step lemmas therefore stop there as explicit
external boundaries. Proving a call's input contract is not equivalent to
proving the wrapper's final functional correctness. The linked IL proof now
also composes callee execution, call/return linking, and the chunk invariants
above.
