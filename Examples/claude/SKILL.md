---
name: Picinae-glibc-proofs
description: Writing machine-checked Picinae correctness proofs for functions lifted from a production C library (glibc), including how to turn a man page into a formal spec, how to structure invariants, and how to keep symbolic execution from exhausting memory or the kernel checker.
---

# Proving lifted glibc functions in Picinae

This skill is for proving functional-correctness theorems about real,
optimized machine code lifted into Picinae (e.g. glibc's hand-written AVX2
string/memory routines).  It assumes the binary is already lifted to a
Picinae IL `program` (see the Ghidra-to-Picinae lifter skill) and type-checks
(`Picinae_typecheck`).  The hard part is not the control-flow reasoning —
Picinae's Floyd–Hoare machinery handles that — it is (a) stating a faithful
spec, (b) choosing invariants that are both provable and not vacuous, and
(c) keeping the symbolic state small enough that tactics and the `Qed` kernel
check finish.

Build every file with a memory cap so a runaway tactic fails fast instead of
swapping the machine to death:

```
ulimit -v 8000000      # 8 GB; raise to ~13 GB only for a known-heavy file
rocq c -R ../.. Picinae -R . Picinae.Examples.claude <file>.v
```

## 1. From man page to formal spec

Write the spec *before* the proof, in a header comment, and as a Coq
`Definition`.  The header should quote the man page's SYNOPSIS / RETURN VALUE,
name the binary (path, sha256, symbol, image base), name the lifter, and give
an English input/output spec in ABI terms (which register holds what on
entry, what RAX/memory hold on return, and the frame).

Turning prose into a predicate:

- **Name the "stop index" explicitly.** Most string functions are "scan to the
  first position satisfying P".  Make `K` (or `n`, or `L`) a universally
  quantified parameter of the theorem and define the predicate that pins it
  down: everything before `K` fails P and is in-bounds, and `K` is the first
  success.  Examples in this tree: `slen` (strlen), `fhit`/`scmp` (strchr /
  strcmp first differing-or-terminating byte), `cspn`/`spn` (strspn/strcspn).
  Then the output is a function of `K` and the bytes at `K`.
- **Prove the stop index exists** from the obvious precondition when you can
  (`fhit_of_slen`: a NUL-terminated string has a first hit at or before its
  terminator).  This keeps callers from having to supply it.
- **State the frame.** "returns the length" also means "writes no memory" and
  "preserves callee-saved registers".  Add the generic theorems
  (`*_nwc` no-write-code, `*_welltyped`, `*_preserves_callee_saved`,
  `*_preserves_memory`) — they are cheap (`noassign_prog_same` +
  `prove_noassign`) and catch lifting mistakes.
- **Write the spec over the model's objects.** Bytes are `m Ⓑ[a]`
  (`= getmem 64 LittleE 1 m a`), addresses are taken mod `2^64` (`a ⊕ k`).
  Use `a ⊕ k` in the spec, not `a + k`, so it matches what stepping produces.
- **Record where the binary disagrees with its man page** as its own theorem
  plus a concrete counterexample, and confirm it against the running libc
  (this tree found `sigisemptyset` ignoring signals ≥ 33 and `a64l` not
  sign-extending).  A crash-freedom property can never express this; a
  functional spec can.
- **Add a precondition only when the code needs it**, and document it in the
  header.  memcpy's loop theorem needs `64 <= d`; strcmp's short-string
  theorem needs the first difference within 32 bytes and the pointers ≥ 128
  bytes from a page end.  A precondition that excludes a code path lets you
  cut that path with a `False` invariant (see §2).

## 2. Invariants and cut points

Proofs use `satisfies_all prog Invs exit trace` with `prove_invs`, then one
subgoal per invariant address (`destruct_inv`).  Each subgoal assumes the
invariant at its address and symbolically executes to the next invariant.

Rules that repeatedly mattered:

- **Put a cut at every join and every loop head**, one instruction before each
  `CALL`, and at every return site.  Without a cut at a join, the live paths
  and their symbolic states multiply and blow up memory.
- **`False` invariants for unreachable entries.** When a precondition excludes
  a path (a size class memcpy won't take, a page-straddle path a precondition
  rules out), give that path's entry address `Some False` and discharge it
  from the precondition.  This is how you scope a theorem to one strategy of a
  multi-strategy function.
- **Abstract the state at a cut to forget expensive values.** A cut's
  invariant should mention only what later steps need.  If the concrete value
  in a register/memory is huge and irrelevant, state the invariant with a
  fresh existential and a *property* of it instead of the value.  This is the
  single most effective OOM control for loops (see §3, the "post-store cut").
- **Each callee contract must assume EVERY conjunct of the callee's entry
  invariant**, or a one-state trace refutes the contract and your theorem is
  vacuously true.  Always pair a contract with a `*_satisfiable` witness
  exhibiting code that meets it; if the only witness you can build is a
  non-returning stub, say so — it is weak evidence.
- **Return sites.** Each callee's post-condition at a call-site return address
  records `mem Ⓠ[sp] = site`; discharge wrong-site goals with
  `getmem_setmem` + `mod_small` + `discriminate`, not by conversion.

## 3. Keeping memory under control (the #1 practical issue)

Picinae memory is one big symbolic term; many ordinary tactics *expand* it
and run out of RAM. Symptoms: a tactic that should be instant takes 60 s+ and
2–7 GB, or `Fatal error: out of memory`.

Do:

- **Never let `lia`/`nia` see a memory term.** Their preprocessing unfolds
  `getmem`/`setmem` and explodes. Always `clear - <only the arithmetic hyps>`
  (a whitelist, not a blacklist) before `lia`. A hypothesis like
  `n <= m Ⓠ[0x3215a8]` must be cleared or `set ... ; clearbody` first.
- **Use syntactic tactics near symbolic memory**, not conversion-based ones.
  Plain `reflexivity`, `assumption`, `contradiction`, non-linear `match goal`
  patterns, and `rewrite` with a lemma whose memory argument is a unification
  variable all expand memory. Use `constr_eq`-guarded versions:
  ```
  Ltac sassumption := match goal with H: ?T |- ?G => constr_eq T G; exact H end.
  Ltac sreflexivity := match goal with |- ?a = ?b => constr_eq a b; reflexivity end.
  ```
- **`discriminate` with a memory equation in context can hang** head-normalizing
  a load; clear memory hyps first.
- **Apply lemmas with explicit arguments, or `refine` the fully-applied
  instance.** `eapply cpy_store`/`rewrite cpy_load` with the memory or offset
  left as an evar can OOM; the same step with every argument explicit is
  instant, because no unification touches the memory term.
- **Hide a genuinely-needed big value behind `set (X := ...) in *; clearbody X`**
  (e.g. a threshold read `m Ⓠ[...]`, or scast values in a register you no
  longer need precisely).
- **Prove per-instruction / per-iteration facts once over an ABSTRACT memory**,
  then apply them. A lemma stated `forall M, cpy m M ... -> cpy m (one store on M) ...`
  builds its term over a variable `M` (cheap) and `apply`s structurally at the
  call site. This is how `cpy_store8` and `nt_adv2` avoid building a giant
  concrete term during their own proofs.
- **Step everything, then prune once — do not prune after every step.** A
  `step_prune` that runs `bc_norm; discriminate/lia` after each `x64_step`
  turned a 23 s stepping phase into 10 minutes; step with `repeat x64_step`
  first, then refute dead paths.
- **Refute a dead path from one branch condition plus one bound** (`refute`),
  after excluding any hypothesis mentioning `getmem`.

Loop bodies with many vector stores are the worst case. A 4-store aligned
loop steps fine (~3 GB); 8 stores crosses the 8 GB cap; 16 stores needs more.
Two options, in order of preference:
1. State the loop-head invariant so the stored memory is **abstract** (an
   existential `cpy` fact), and prove the one-iteration advance with an
   abstract-memory lemma (`nt_adv2`). The stepping still peaks high because
   `repeat x64_step` carries the concrete stores through the loop's branch
   instructions; if that peak fits in RAM, raise `ulimit` for that file.
2. If it does not fit, step the stores, then make the post-store memory
   opaque before stepping the branch instructions. Note that `repeat x64_step`
   does **not** stop at a mid-body invariant the way it stops at a loop head,
   so a mid-body cut alone does not bound the peak — you must step manually to
   the post-store point and `set ...; clearbody` there.

## 4. Kernel check (`Qed`) time

Tactics can finish in seconds while `Qed` runs for 30+ minutes. The cause
found here: the kernel unfolds `N.ltb x <power-of-two literal>` inside an
`if` (branch conditions comparing a size against `2^7`, `2^8`, …). A
`Strategy` declaration in `Picinae_core.v` covers some cases. If a proof's
tactics are fast but `Qed` is not, **leave it `Admitted` with a
`QED-SLOW` note** rather than spending the session on it; come back later.
(This tree leaves `pthread_mutex_lock`, `__memset_avx2`, `isinfl`, `rand_r`
that way.) Record the trigger in the note.

## 5. SIMD / AVX2 instructions

Lifted AVX2 lane instructions (VPCMPEQB, VPMINUB, VPMOVMSKB, TZCNT) produce
32-lane terms; VPMOVMSKB alone is ~200 IL moves. Do **not** step them with
`x64_step`.

- Enable the lifter's canonical-temporary numbering so every occurrence of an
  instruction lifts to an identical statement.
- Write a **whole-instruction lemma per instruction shape** in a shared file
  (`amd64_avx2.v`): a Coq generator convertible to the lifted statement, and a
  lemma `exec_stmt archtyps s <gen> c' s' x -> x = None /\ ... reset_temps s s' = update s dst y`
  proved once by induction over the lanes. Confirm convertibility with a
  near-instant `reflexivity` on `prog s addr = Some (len, gen)`.
- Step such an instruction with `eapply NIStep; [reflexivity|reflexivity|];
  intros ... XS; apply <lemma> in XS; ...`. A per-address dispatch tactic
  (`sl_simd`/`sc_simd`: `lazymatch` on the current address, each arm a
  specific instruction lemma) plus `repeat (first [dispatch | x64_step])`
  drives a whole function. **`vm_compute` the address before matching**, or
  hex/decimal forms won't match.
- **Invert expression evaluation with hand-written lemmas, not `inversion`.**
  `inversion` on `eval_exp` normalizes arithmetic (e.g. `8*i` into a `match`),
  which then won't rewrite. Use `ev_var`/`ev_binop`/`ev_extract`/… that peel
  one layer and leave the arithmetic alone.
- Relate masks to bytes once: bit `8j+7` of a VPCMPEQB-vs-zero result is
  "byte j is zero"; VPMOVMSKB bit `j` is bit `8j+7`; TZCNT of the mask is the
  first set bit (model it as `N.iter (w+1) tz_step (0,x)` and prove
  `tz_result`). The SARX page-cross path needs an arithmetic-shift argument
  (`ashiftr_spec`); the 64-bit TZCNT over two 32-bit masks needs a split
  lemma.
- **Signed-comparison branches force the flags into the proof.** A `JG`/`JL`
  after a `CMP` cannot be handled by abstracting OF/SF away (the usual
  `ignore_vars` trick drops `AF`/`PF` only). Recover the signed relation from
  the lifted `OF`/`SF`/`ZF` bit-expressions; often `OF` simplifies to a
  single bit `b .& (b .^ 1) = 0`, and `slt w x 0` reduces to `2^(w-1) <=? x`
  via `toZ_sign`.

## 6. Lifter soundness (know your trusted base)

The lift is in your trusted base. Bugs there make a proof true of the IL but
not the binary. This tree's lifter needed fixes for: partial-register writes
(must merge into the base register, not clobber it), exact varnode widths and
1-bit flag widths, `BOOL_NEGATE` = `xor 1`, `LZCOUNT`, intra-instruction
branches (BSF/TZCNT scan loops as bounded `Rep`), AVX/AVX2 user-ops spelled
out byte-by-byte, per-lane vector writes merged into one `Move`, `LOCK` as a
no-op (atomicity assumed, not modeled), and static-memory hypotheses off
(their `SMCorrect` check costs gigabytes). When a proof of a plausible fact
is impossible, suspect the lift before the logic.

## 7. Workflow

- Build in the background while writing the next proof; monitor memory.
- Iterate with `ulimit`-capped batch compiles where all other segments are
  `admit`; dump a goal with `match goal with |- ?G => idtac G end` and dump a
  context by reverting the non-memory hypotheses.
- Commit only when asked. Keep unfinished work and slow-`Qed` theorems
  `Admitted` with a note rather than blocking.
- Never `pkill -f <pattern>` (it matches the calling shell); kill by PID or
  `pkill -x rocqworker`.
