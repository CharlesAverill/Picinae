# x02-avx-nt validation record (work in progress)

Assigned branch: `llm-proofs/x02-avx-nt`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-90e22f1a`.
Origin base: `49956416928e5b6bb3928b54ae33e3b81091f006`.
Sole prerequisite: `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`.
The initial working tree was clean on prepared branch `t3/90e22f1a`.
HEAD was already the prerequisite; no merge/import was needed. Its sole parent
was the origin base. The first sandboxed network check failed DNS; the repeated
read-only check outside the sandbox succeeded with no branch result. Only the
prepared branch was renamed; the sandbox initially prevented the Git metadata
write, and the authorized retry succeeded. See `fork-name-check.log`,
`rename.log`, and `ancestry-before.log` (the latter includes the newly created
notes directory as untracked; the initial status before notes was empty).

No dependency installs, remote writes, or shared environment changes.
All compiler/query commands use the shared toolchain read-only, virtual memory
limit 13000000 KiB, stack 65536 KiB, and Dune `--cache=disabled -j1`.

The baseline lexical audit identifies exactly two admissions in assigned scope:
`nt_seg_1285` and `memmove_avx_correct_nt`. Lexical results do not certify
transitive assumptions. Baseline compilation and assumptions queries must be
read with their actual exit codes; a successful baseline build alone cannot
certify those admitted declarations.

The generated `memmove_avx_amd64.v` is unchanged. Its inherited provenance is
Ubuntu amd64 glibc 2.35-0ubuntu3.12, libc SHA256
`9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9`,
symbol `__memmove_avx_unaligned_erms`, Ghidra address `0x2a0840`, image base
`0x100000`, lifted with Ghidra 11.4.2 and pcode2coq. This unit does not revalidate
that binary or the lifter. CPU instruction availability, cache effects,
non-temporal ordering and termination are outside the sequential lifted IL
partial-correctness model.

## Outcome: PARTIAL — policy handoff to Sol

Charles's steering arrived while the baseline build was running: one Astra
proof attempt only, stop after its first full-build failure, preserve the
statement and best attempt for a NEW gpt-6.1-sol xhigh/priority fixer delegate.
No repair iteration or proof compiler was started after the failure below.
No active compiler was killed and no memory limit was raised.

1. `01-baseline-build.log`: **exit 0**, full `.vo` target
   `Examples/claude/amd64_memmove_avx_nt_proof.vo`, using the original NT source
   from e00/base. The explicit dependencies also produced full `.vo` files.
   This success does NOT discharge the two original admissions.
2. `02-baseline-assumptions.log`: **exit 0**, exact `Check` and
   `Print Assumptions` output from `tools/print-assumptions.sh` for ten constants.
3. `03-initial-repair-build.log`: **exit 1**, same full NT `.vo` target,
   the first and only repair attempt. It failed in
   `amd64_memmove_avx_nt_stores.v:149:21-32`:
   `Error: Cannot find a relation to rewrite.`
   The failing line is `split; vm_compute; reflexivity.` in
   `cpy_store16_inputs_satisfiable`. This is a tactic failure, not an OOM.
   Compilation traversed `cpy_store16`'s Qed before that diagnostic, but the
   helper file did **not** produce a `.vo`. Neither `nt_adv4` nor the repaired
   `nt_seg_1285` nor the main theorem was reached by this build. These are
   unvalidated attempts, not completed helpers or certified new theorems.
4. `04-source-audit.log`: post-packaging global source audit against the pinned
   base. The two admissions in assigned scope have been removed by retaining
   the exact statements with `Abort`, not by proving them.

The final source keeps the existing proved helpers and tail segments and
retains the two missing theorem statements as explicitly aborted declarations.
Those names are therefore **not exported constants** in the final source.
The final packaging was not proof-built after the failed attempt, in accordance
with the stop-and-handoff instruction. The successful baseline `.vo` and its
assumptions log must not be mistaken for validation of the packaged source.
There is no resulting main-theorem assumptions certificate; there is no proved
main theorem to query. No new Axiom/Parameter/admission was added.

## Exact baseline assumptions

The full declarations and raw output are in `02-baseline-assumptions.log`.
The reported dependency sets are:

- `memmove_avx_correct_nt`: the axiom `memmove_avx_correct_nt` itself.
- `nt_seg_1285`: the axiom `nt_seg_1285` itself.
- `nt_adv2`, `cpy_store8`: `Closed under the global context`.
- `nt_seg_1117`, `nt_seg_1125`, `nt_seg_1210`, `nt_seg_1613`,
  `nt_seg_1621`, `nt_seg_1706`: each reports exactly:

```
Axioms:
FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
  (forall x : A, f x = g x) -> f = g
```

Thus the six completed baseline segments do not transitively rely on either
NT admission. Functional extensionality is inherited and documented in e00;
it is not concealed or claimed absent.

## Statement and coverage preserved

`memmove_avx_correct_nt` is the existing `satisfies_all` partial-correctness
statement over `nt_invs` and `nt_exit` for the unchanged lifted program, with:
entry at address 0; a state modeling `x64typctx`; 64-bit ABI inputs RDI=d,
RSI=s, RDX=n, RSP=rsp and initial memory m; `nov d s n`; `d+n < 2^64`;
`s+n <= 2^64`; `16448 <= n`; the 8-byte little-endian threshold at
`0x31a3f8` strictly below n and the stop threshold at `0x3215a0` at most n.
There is no added four-page-excluding condition or altered size restriction.
The required postcondition at the two pre-RET sites 1261 and 1757 is RAX=d,
RSP=rsp, destination bytes equal to the original source bytes for i<n, and
unchanged bytes outside the destination interval. Separate existing nwc,
welltyped and callee-saved frame theorems are imported from the small proof.
The unproved segment statement still handles every j<nk 14 d n and i<32
under the original `done4` invariant, with no excluded inner iterations.
No new functional coverage is established by this partial unit.

## Fixer handoff files

- `initial-repair.v.txt`: exact full attempted NT replacement, including
  original main script with Qed, proposed `nt_adv4`, and `nt_seg_1285` attempt.
- `nt-stores-attempt.v.txt`: exact failed helper file (line numbers preserved).
- `nt-adv4-attempt.v.txt`, `nt-seg-1285-attempt.v.txt`: focused excerpts.
- `generate-store-helper.py`, `prepare-four-page-attempt.py`: preparation
  scripts preserved as provenance, not commands to blindly rerun; the full
  `.v.txt` snapshots are authoritative (the helper snapshot also has the
  concrete satisfiability witness added after generation).

For the new Sol delegate, restore the two `.v.txt` snapshots to their matching
`Examples/claude/*.v` paths and add only the helper's explicit Dune module.
Inspect/fix the witness tactic diagnostic before considering deeper loop
issues. Keep theorem statements unchanged unless genuinely wrong, and explain
any necessary correction. The intended memory strategy in the draft is:
abstract the first eight stores after 33 instructions, then all sixteen stores
after eight more instructions, before stepping the branch/advance instructions.
Neither that instruction-count match nor its memory-term normalization has yet
been compiler-validated. Full target success, nonvacuity evidence, main and
critical-segment assumptions queries, and the source audit remain required.
