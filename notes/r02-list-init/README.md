# r02-list-init — PARTIAL Astra author handoff

State: **PARTIAL**, not DONE. Initial author: OpenAI gpt-6-astra,
xhigh/priority. Final proof producer: **none**; Astra did not complete the
target. Request a NEW gpt-6.1-sol xhigh/priority fixer through the coordinator.
No subagent was created and no second Astra proof/compile cycle occurred.

Branch: `llm-proofs/r02-list-init`.
Worktree: `/home/charles/.t3/worktrees/Picinae/t3-ba16f2da`.
Reviewed prerequisite: `4ff26413448da4d8f064b0273ac5472cc9de7e5a`.
Implementation checkpoint: `38f9034a3b4f8b5bff8f546a4e9afd28d23056b1`.
The subsequent evidence-only commit records its post-commit ancestry audit.
Status immediately after the implementation commit was clean; the only new
file during that recorded audit was the audit log itself. Final handback
reports the evidence commit SHA and checks clean status again.

## Build and exact failure

The complete statements and one-shot initial proof were written before any
compiler invocation and preserved verbatim in `initial-attempt.v.txt`.
`dune-initial.log` records the only full build, exact command, complete compiler
stdout/stderr and true exit status **1**:

```sh
/home/charles/code/friends/.toolchains/arm-validation/picinae-env \
  bash --noprofile --norc -e -c 'ulimit -v 2000000; ulimit -s 65536; dune build --cache=disabled -j1 --display short Examples/FreeRTOS/armv6m_vListInitialise_proof.vo'
```

Diagnostic, verbatim:

```text
Goal at < 64 >
Goal at < 84 >
File "./Examples/FreeRTOS/armv6m_vListInitialise_proof.v", line 183, characters 35-45:
Error: Found no subterm matching "s0 R_R0" in the current goal.
```

The failure is inside `list_init_correct`, at the initial attempt's
`unfold list_init_post. psimpl. rewrite R0.` No repair was attempted.
Core prerequisites, the unchanged generated map and the accepted list model
compiled successfully as dependencies of this failed command. There is **no
successful full target command** for this unit, and no main correctness result.

Eight prefix proofs reached Qed before the error: `list_init_nwc`,
`list_init_welltyped`, `list_init_register_frame`, `list_init_swap_zero`,
`list_init_stores_image`, `list_init_post_layout_frame`,
`list_init_entry_witness`, `list_init_concrete_entry_witness`.
They are retained unchanged. They do not constitute a successful target build.
The failed `list_init_correct` and unchecked `list_init_at_bx`,
`list_init_return_step`, `list_init_return_witness` are preserved as exact
statements with Abort. Their complete original scripts remain in the archive.
The resulting handoff file has not been recompiled. The preservation checker
compares every definition/import/statement after stripping comments and proof
bodies, and verifies twelve declarations and four Aborts.

## Proposed specification and remaining gaps

The actual eleven-instruction finite map is used, not a replacement function.
Entry is 0x40 and BX LR is at 0x54. Exact stores occur in order at offsets
4, 8, 12, 16, 0. The memory expression `list_init_stores` reflects that order;
its helper equates it to r00 `empty_image` through disjoint word-store swaps.

The proposed `list_init_correct` is `satisfies_all` under a welltyped entry,
R0=p, nonnull p, p mod 4=0, p<2^32, p+20<=2^32, and writable permissions for
all twenty bytes. Original memory is arbitrary within `memsize 32`.
The post specifies exact original-memory-based empty_image, R0=p,
R2=0xffffffff, R3=0 and N/Z/C/V=0/1/0/0. The target layout is count=0,
index=p+8, sentinel value=0xffffffff and sentinel next/previous=p+8.
No owner/container fields are invented in the embedded 12-byte sentinel.

`list_init_at_bx` is intended to extract that post from an actual `exec_prog`
trace ending at BX, exposing both the layout and ALL original bytes outside
the 20-byte object. The global register frame preserves R0/R1, R4-R12,
SP/LR, permission maps and temporaries. No stack access/alignment premise or
read permission is needed. No callee/scheduler/TCB/IRQ/CPU-tunable assumptions
are used. The finite immutable map ignores A_EXEC, as inherited from e05.

The entry witnesses range over every supported p and bounded original memory
m; they give a typed writable state, not r00's zero-permission state. A concrete
p=4096, LR=257 witness is included. Permissions are symbolic N.ones (2^32)
and proved using bitvector lemmas without evaluating a huge bitmap.

The proposed separate ordinary return step uses the actual 0x54 instruction,
LR mod 2=1 and LR<0xfffffff0, producing Addr (LR & 0xfffffffe) with the state
unchanged. This explicitly excludes exception-return encodings. The return
script and its witness were not reached by the compiler.

The fixer must retain statements unless genuinely wrong and explain every
change. It must complete the main functional proof, actual-trace extraction,
ordinary-return and return-witness proofs; build the full target under the
same cap; and run transitive assumptions queries. No termination, asynchronous
execution, hardware exception return, whole-kernel or binary/lifter refinement
claim is made. Official FreeRTOS V11.1.0 and ELF SHA256 remain the inherited
provenance boundary documented in the proof header and unchanged manifest.

## Audit and history

The source audits against `49956416928e5b6bb3928b54ae33e3b81091f006` pass:
unit CURRENT/NEW totals `{}`, repository NEW totals `{}`. Unrelated baseline
seven Admitted, one admit and 89 module-interface Parameters remain unchanged.
These lexical results do not certify transitive assumptions.
`assumptions-status.txt` explains why there is no raw Print Assumptions output:
the target failed and the helper would trigger a prohibited second build.
Inherited `FunctionalExtensionality.functional_extensionality_dep` is recorded
honestly as an existing baseline assumption, not claimed absent from this unit.

Initial HEAD was exactly e00 `71470bffba65392adf1873a3df9f0cf0ca4f1ac9`,
sole parent the pinned origin. Initial status was clean. The first network
collision lookup failed DNS in the sandbox; the recorded authorized retry
succeeded with no remote branch. Only the prepared local branch was renamed.
Sandbox Git metadata writes failed read-only; the authorized retry performed
that rename and the explicit approved fast-forward to r00. No automatic
approval rejection occurred. The before-audit shows only new evidence files
as untracked, because they were created after the initial clean observation.

`audit-ancestry.sh` checks all eleven exact approved prerequisite commits plus
only supplied own unit commits, pinned merge-base, protected source identity,
and the narrow file scope. No fork history, r01, e19, r06, ffsl, or unrelated
validation history was imported. Root dune adds only this proof module.
No installs, toolchain changes, host package operations, remote writes,
publication, shared campaign edits or changes to another branch/worktree.
