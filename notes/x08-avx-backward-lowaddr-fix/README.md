# x08 AVX backward low-address repair

State: PARTIAL — stopped on Charles's explicit wrap-up order; no full x08 certificate.

Initial author: OpenAI gpt-6-astra, xhigh/default. Iterative fixer: OpenAI
gpt-6.1-sol, xhigh/default. Final proof producer is not certified yet.
Branch: llm-proofs/x08-avx-backward-lowaddr-fix.
Worktree: /home/charles/.t3/worktrees/Picinae/t3-48b8f09f.

The prepared worktree was initially clean at e00
71470bffba65392adf1873a3df9f0cf0ca4f1ac9, sole parent pinned origin
49956416928e5b6bb3928b54ae33e3b81091f006. The read-only fork branch-name
check initially failed sandbox DNS; its network-enabled retry succeeded
with no result (remote-branch-check.log). The exact authorized source
checkpoint a0cf00cf530b9785dba569f9accf05421a36dbb3 was imported with
git merge --ff-only. The first sandbox merge attempt failed to write
ORIG_HEAD in git metadata outside the writable root; the authorized retry
succeeded. Only the prepared t3/48b8f09f branch was renamed. No other
branch or remote was changed.

The original Astra evidence in notes/x08-avx-backward-lowaddr is preserved
unchanged, including initial-attempt.v.txt and initial-full-build.log.
The generated map and accepted x04 proof remain unchanged. All 26 original
declarations (19 results, seven definitions) are preserved verbatim apart
from whitespace/comments; audit-declarations.py verifies entire statements
and definition bodies. This fixer restored every archived proof script.

Every compiler/query uses the mandatory shared resource-run.py gate with
unit x08-avx-backward-lowaddr-fix and memory_kib=4000000, the read-only
picinae-env wrapper, stack 65536, cache disabled, and Dune -j1. No compiler
runs concurrently inside this unit. Admission waits are not proof failures.
Logs are captured with tools/record-command.sh and retain exact commands,
stdout/stderr and real exit codes. No dependencies were installed, no
shared toolchain/configuration was modified, and no other processes were
signalled. No push, PR, remote write, campaign edit or subdelegation.


## Wrap-up result

Charles ordered immediate wrap-up with no further proof/build retries.
The third build was still waiting for admission and was stopped by signalling
only this unit's exact gate PID 785321; stop.log records the command.
build-03.log records the cancelled attempt (exit 143); no compiler was
admitted for it. No other unit process was signalled.

build-01.log and build-02.log both report exit 1, without a memory-cap
failure. The entire dependency closure, including accepted x04, built at
4000000 KiB in build 01. Build 02 passed the original YMM5/YMM6/YMM7
load-address failure after deriving explicit nonwrap equalities S32/S64/S96
from BIG and SW. It then failed on the saved-tail address's redundant
outer modulo at original repaired line 212. The final repair adds
N.mod_mod before addr_tail_w; this change has NOT been compiled.

Every original statement and definition is retained. The eleven originally
completed helper scripts remain Qed. The main theorem and seven subsequent
unchecked results are Abort, with no new admissions/axioms/parameters.
All restored scripts and current repairs are preserved in
repaired-attempt.v.txt. The original Astra archive and evidence, generated
map, accepted x04 proof and Dune selection are unchanged.

The target module has no successful full .vo build. There is no new x08
Print Assumptions output. Do not claim the main theorem, at_ret, actual
RET-step/after_ret, typed/permission/entry witnesses or cursor examples
are certified. The existing eleven Qed helper scripts have been processed
before the main failure but do not constitute a full module certificate.
The preserved inherited x04 FE-only assumptions evidence is not a new x08
certificate.

Next step, only if authorized to resume: restore repaired-attempt.v.txt,
validate the final tail-address normalization, then repair the loop,
functional/frame/RET and permission witnesses; obtain full gated .vo and
all transitive Print Assumptions. The statements retain 256<n,
s<d<s+n, 0<d<128 and both nonwrapping ranges, all possible gaps, unchanged
original-source/frame and wrap-aware cursor scope. No termination,
physical accessibility or independently validated binary provenance claim.
