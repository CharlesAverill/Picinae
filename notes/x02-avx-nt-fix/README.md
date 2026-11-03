# x02-avx-nt-fix — DONE

Assigned branch: `llm-proofs/x02-avx-nt-fix`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-78795c90`.
Author model: **Astra**. Final proof model: **Sol**.

The original `nt_seg_1285` and `memmove_avx_correct_nt` statements now have
kernel-checked `Qed` proofs. Both report only the inherited dependent functional
extensionality assumption, with no admitted dependency. Full `.vo` target
builds, the two nonvacuity witnesses, source audit and original statement checks
all succeeded. No new admissions, Axioms or Parameters remain in unit artifacts.

## Changes and corrections

Restored the authoritative `initial-repair.v.txt` and `nt-stores-attempt.v.txt`
archives from the reviewed author checkpoint; the archives are untouched.
The main proof source is byte-for-byte the author's full attempted snapshot.
Its historical header describes that author's initial attempt; this record
supplies the subsequent successful Sol validation and final-producer evidence.

The only correction required to validate that attempt is in
`cpy_store16_inputs_satisfiable`: `split; vm_compute; reflexivity` produces
inequalities and failed with `Cannot find a relation to rewrite`. Replaced it
with `split; change (2^64) with 18446744073709551616; lia`. No helper statement,
public statement, invariant or precondition was weakened or changed.

`cpy_store16` uses sixteen loads from one pre-store memory snapshot. `nt_adv4`
advances all four 128-byte rows in the copied-set invariant. The instruction
segment abstracts the first eight stores after 33 instructions, and all sixteen
after eight more, before stepping branch/arithmetic instructions. The successful
full target validates both the memory abstraction and these instruction slices.
The four-page invariant still covers **all j<nk 14 d n and i<32**.

Added `amd64_memmove_avx_nt_witness.v` with a closed concrete entry witness:
d=65536, s=131072, n=32768, rsp=0, initial memory=0, hence both tunables zero.
It includes a modeled register store and every public numeric/nonoverlap/input
premise. It witnesses inputs, not termination. The existing helper witness
covers an empty copied set and the first row of all four pages: its largest
offset bound is 12416<=n, with concrete n=16384 and separated buffers; selecting
store/load addresses d+o and s+o satisfies all modular address equations.

The first extra witness attempt was interrupted in its typing tactic; the next
two were interrupted in direct conversion of zero-memory loads at large concrete
addresses. Their exact source snapshots and real exit-1 diagnostics are retained.
The final witness proves zero-valued registers against a symbolic bit width,
then treats only three nonzero 64-bit registers numerically. A closed
`nt_zero_memory_load` lemma avoids computing enormous concrete bit masks.
All interruptions targeted only this unit's witness compiler, never another
unit. No main proof compiler was interrupted, and the cap was never raised.

`21-final-statements.log` compares both original theorem declarations and
`nk`, `nr`, `done2`, `done4`, `nt_exit`, `nt_invs` byte-for-byte against pinned
origin: the public-statement/predicate diff is empty. All six existing clean
tail segments, `nt_adv2` and `cpy_store8` are also byte-for-byte unchanged.
The generated `memmove_avx_amd64.v` is unchanged. Root Dune adds only the
store-helper and witness modules beyond the reviewed author's target closure.

## Scope and limitations

`memmove_avx_correct_nt` is sequential lifted-IL partial correctness for System V
AMD64, with 64-bit RDI=d, RSI=s, RDX=n, RSP=rsp and memory m at address 0:

- `nov d s n` (nonoverlapping modular byte regions);
- `d+n < 2^64`, `s+n <= 2^64`;
- `16448 <= n`;
- the little-endian 8-byte threshold at `0x31a3f8` strictly below n and the
  threshold at `0x3215a0` at most n.

The exit immediately before RET at 1261/1757 requires RAX=d, unchanged RSP,
original source bytes copied to every destination offset i<n, and unchanged
bytes outside destination[0,n). The separate imported frame preserves RBX,
RBP and R12–R15 at endstates; nwc and welltyped are queried separately.
No extra CPU or DF hypothesis was added: this sequential IL theorem assumes
AVX availability/binary-lift fidelity and does not establish ISA availability.
It does not cover all sizes, overlapping memmove, termination, executing RET
with a separated return slot, cache effects, non-temporal ordering, faults,
concurrency, or lifter refinement.

Inherited target: Ubuntu amd64 glibc 2.35-0ubuntu3.12, libc SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
`__memmove_avx_unaligned_erms`, Ghidra address `0x2a0840`, image base `0x100000`,
Ghidra 11.4.2 / pcode2coq. Read-only e01 evidence (`05-e01-scope.log`) matches all
351 boundaries/lengths while preserving 24 PREFETCHT0-as-NOP annotations.
This does not turn the IL result into a validated binary/lifter theorem.

## Successful validation and raw assumptions

All proof compiler/Dune/query invocations use read-only
`/home/charles/code/friends/.toolchains/arm-validation/picinae-env`, virtual memory
13000000 KiB, stack 65536 KiB, `PROOF_MEMORY_KB=13000000`, and Dune
`--cache=disabled -j1`. Exactly one proof compiler runs at a time.
`06-resource-cap.log`, `07-resource-cap.log` and `09-witness-resource.log` record
inherited limits. No installations, shared environment changes or host changes.

Commands are captured by `tools/record-command.sh`, with stdout/stderr and true
exit codes. Scripts invoked by those recorded commands are preserved here.

- `02-repair-build.log`: exit **0**, fresh full
  `dune build --cache=disabled -j1 --display short Examples/claude/amd64_memmove_avx_nt_proof.vo`,
  including its full dependency closure and store helper.
- `15-final-targets-build.log`: exit **0**, `build.sh` requests both
  `Examples/claude/amd64_memmove_avx_nt_proof.vo` and
  `Examples/claude/amd64_memmove_avx_nt_witness.vo`; witness compiled to full `.vo`.
- `16-assumptions.log`: exit **0**, `assumptions.sh` invokes
  `tools/print-assumptions.sh` serially for all 18 queried constants. This is
  the **verbatim raw Print Assumptions output**, including full Check output.
- `19-assumptions-check.log`: exit **0**, exact checks of all 18 assumption sets.
- `18-source-audit.log`: exit **0**, global audit against pinned origin.
- `20-unit-source-audit.log`: exit **0**, all three unit `.v` files: current/new
  suspicious-token totals both empty, compared with the two original admissions.
- `21-final-statements.log`: exit **0**, public/segment/predicate/lift comparisons.
- `22-validated-objects.log`: exit **0**, source/full `.vo` hashes and diff check.

For **each** of `memmove_avx_correct_nt`, `nt_seg_1285`, all six tail segments,
and `memmove_avx_welltyped`, the exact assumption output is:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

For **each** of `nt_adv4`, `nt_adv2`, `cpy_store8`, `cpy_store16`,
`cpy_store16_inputs_satisfiable`, `nt_entry_inputs_satisfiable`,
`nt_zero_memory_load`, `memmove_avx_nwc`, and
`memmove_avx_preserves_callee_saved`, the exact output is:

```
Closed under the global context
```

Functional extensionality is inherited from the reviewed e00/baseline library;
it is not a newly introduced assumption. Neither original NT admission remains
as a transitive assumption. The baseline author `.vo` that contained admissions
was never copied or accepted as proof evidence in this worktree.

## Local history and publication

Initial prepared HEAD was exactly e00 with sole parent pinned origin, and the
initial worktree was clean before notes were created. Exact read-only fork-name
check succeeded with no result (`01-fork-name.log`) before renaming only prepared
`t3/avx-nt-fix` to the assigned branch. Fast-forward to the reviewed author
checkpoint succeeded. Original author branch/worktree are untouched.

Allowed ancestry only:
`49956416928e5b6bb3928b54ae33e3b81091f006`
-> `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`
-> `2d201cd4983ab0649f8d8a813158f40a7b1dbf55`
-> this continuation's own local commit.

No fork history, other unit branches, worktrees, pushes, PRs, comments or remote
writes. Network and Git metadata required authorized sandbox escalations.
The final commit SHA/clean status/merge-base/full log/diff stat are captured after
commit under the sole permitted external evidence destination:
`/home/charles/code/friends/.refs/picinae-llm-proofs/units/x02-avx-nt-fix/`.

The precommit whitespace check reports trailing spaces emitted verbatim by
`/proc/*/limits`, process cmdlines and one Rocq `Check` line in raw `.log`
artifacts. These logs are intentionally preserved byte-for-byte. The final
staged whitespace check excludes only this unit's `.log` files; source,
scripts, snapshots and prose pass unchanged.
