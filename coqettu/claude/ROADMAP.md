# Claude — musl 1.2.6-r6 x86_64 verification roadmap

Target: `alpine_musl/x86_64/lib/libc.musl-x86_64.so.1`
(sha256 `cc3e0200…4714647`, Ghidra image base 0x100000).
All artifacts live in `x86_64/`:

| Path | Contents |
|---|---|
| `x86_64/lift.sh '<regex>'` | lift functions (global addressing) from the private Ghidra project `~/research/ghidra_projects/coqettu_claude` (the binary is imported under its symlink-target name `ld-musl-x86_64.so.1`; same bytes) |
| `x86_64/programs/<fn>_amd64.v` | generated Picinae programs (do not edit) |
| `x86_64/lib/x64_common.v`, `x64_memcpy_sets.v`, `x64_fill_sets.v` | bit/byte lemmas and the `cpy`/`fil` written-offset sets (copied from Claude's own earlier glibc work in `Examples/claude`, plus fill-chain tactics) |
| `x86_64/lib/x64_abi.v` | callee-saved frame, `bc_norm` (branch conditions), `x64_step'` (REP instructions), syntactic `conj_tac`, memory-safe `mlia64` |
| `x86_64/lib/x64_compose.v` | **composition**: `satisfies_all_pmono_ext`, `call_leaf_ni`, `stack_frame` lemmas, `updateall2_lub` |
| `x86_64/lib/x64_haszero.v` | musl's HASZERO word trick: `haszero_bytes(_msub)`, `haszero2_bytes`, `nilfree_add8` |
| `x86_64/lib/x64_jmpbuf.v` | jmp_buf layout, write/read-back/frame lemmas |
| `x86_64/lib/x64_ctype.v` | character-class arithmetic (`or32_range`, `range_check`) |
| `x86_64/lib/x64_signed.v` | 32-bit signed compare flags (`s32_norm`, `flags_finish`) |
| `x86_64/tools/` | `check_lift.py` (lift completeness vs objdump), `merge_lift.py` (merge Ghidra-split fragments), `define_missing.py` (Ghidra script), `gen_ctype.py`, `gen_misc.py` (proof generators) |
| `x86_64/proofs/<fn>_proof.v` | specification + proof, with the header of `../proof_header_template.v` |
| `x86_64/rc.sh <file> [GB]` | compile one file with a memory cap |
| `x86_64/Makefile` | `make` builds everything |

Logical paths: `-R ../../.. Picinae -R . CoqEtTu`.

## Solved

| Function | Kind | File | Notes |
|---|---|---|---|
| `memset` | hand-written asm (`src/string/x86_64/memset.s`) | `proofs/memset_proof.v` | full functional correctness, any `prog ⊇ memset`, no wrap precondition; Qed ≈ 5 min |
| `setjmp` | asm | `proofs/setjmp_proof.v` | exact memory post (`jmpbuf_write`), RAX=0, frame; `setjmp_ret_target` (the RET step) |
| `longjmp` | asm | `proofs/longjmp_proof.v` | post at the final indirect JMP; `longjmp_jump_target` (the JMP step goes to the saved pc) |
| setjmp ∘ longjmp | composition | `proofs/setjmp_longjmp_proof.v` | `setjmp_returns_twice`: fake return = real return except RAX = val?val:1 ≠ 0 |
| `strlen` | C, word-at-a-time HASZERO | `proofs/strlen_proof.v` | no length precondition; uses `haszero_bytes` (lib/x64_haszero.v) |
| `strcmp` | C byte loop | `proofs/strcmp_proof.v` | stop index K; EAX = s1[K]-s2[K] (`strcmp_sign`) |
| `memcmp` | C byte loop (Ghidra-split lift, merged) | `proofs/memcmp_proof.v` | `memcmp_result` |
| `strchrnul` (+ call to `strlen`) | C, HASZERO(w)\|HASZERO(w^k), **calls strlen** | `proofs/strchrnul_proof.v` | first caller/callee composition: strlen's standalone contract is used via `call_leaf_ni` (lib/x64_compose.v); precondition `stack_ok` only for c=0 |
| `strchr` (→ strchrnul → strlen) | C, **3-level composition** | `proofs/strchr_proof.v` | uses strchrnul's contract (incl. its `stack_frame` memory frame); precondition `str_ok` (terminated, off the 48 stack bytes) |
| `stpcpy` | C, HASZERO word **copy** loop | `proofs/stpcpy_proof.v` | exact `copied` memory post; precondition `cpy_ok` (terminated source, non-overlapping L+1 bytes); `word_bound`, `src_byte` |
| `strcpy` (→ stpcpy) | C, composition | `proofs/strcpy_proof.v` | uses stpcpy's `copied` post; precondition adds that neither string overlaps the 16 stack bytes |
| `strnlen` (→ memchr) | C, composition | `proofs/strnlen_proof.v` | uses memchr's `stack_frame`; preconditions: object not at NULL/not wrapping, off 40 stack bytes; s need not be terminated |
| `strncmp` | C byte loop | `proofs/strncmp_proof.v` | `strncmp_result` incl. n = 0 |
| `ispunct` (→ isalnum) | C, composition | `proofs/ispunct_proof.v` | exact for every 32-bit int |
| `stpncpy` (→ memset, asm) | C, 3 copy loops + zero fill | `proofs/stpncpy_proof.v` | **C → hand-written asm composition**; `upto` copy predicate; precondition `stpncpy_ok` (pairwise-disjoint areas, n < 2^63) |
| `strncpy` (→ stpncpy → memset) | C, 3-level composition | `proofs/strncpy_proof.v` | pairwise-disjoint areas incl. 32 stack bytes |
| `wcsnlen` (→ wmemchr) | C, composition | `proofs/wcsnlen_proof.v` | SAR result exact under 4n < 2^63 |
| `swab` | C byte-pair loop, signed `JG` exit | `proofs/swab_proof.v` | `swb` pair-swap predicate; negative n (as ssize_t) copies nothing; JG flag lemma `jg1_64` (lib/x64_signed.v) |
| `l64a` | C, static buffer + digit table | `proofs/l64a_proof.v` | digit count k <= 6 exact; `l64a_digits`: with musl's table in memory the bytes are the radix-64 characters |
| `strcat` (→ strlen, → strcpy → stpcpy) | C, two calls, one composite | `proofs/strcat_proof.v` | strlen's result identified with dst's length by `nilfree_unique`; frames through three stack stores (`push3_frame`) |
| `strncat` (→ strlen) | C, call + bounded append loop | `proofs/strncat_proof.v` | K = strnlen(src, n) existential; `cpb` copy predicate; saved R12/RBP/RBX re-read through the copy frame |
| `wcsncpy` (→ wmemset) | C, word copy loop + call | `proofs/wcsncpy_proof.v` | 32-bit word copy predicate `wcp`; wmemset's `wfil` frame covers the copied prefix (`out_fill`) |
| `wcsrchr` (→ wcslen) | C, call + backward scan with unsigned pointer compare | `proofs/wcsrchr_proof.v` | last occurrence (incl. the terminator); precondition 4 <= s, no wrap, so `p-4 < s` terminates as in C |
| `wcpncpy` (→ wcsncpy → wmemset, → wcsnlen → wmemchr) | C, two composite calls | `proofs/wcpncpy_proof.v` | wcsnlen's K identified with wcsncpy's K (`len_unique`); 64 stack bytes across both callees |
| `srand`, `rand`, `rand_r` | C, static / caller seed | `proofs/prng_proof.v` | exact LCG update of the seed; rand_r's tempering proved bit by bit (`bb32`, per-bit `btauto`; psimpl splits `12345+z` into `57+z` under masks, handled by `low12_bits`) |
| `wmemcpy` | C word copy loop | `proofs/wmemcpy_proof.v` | (helper session) `wmoved` post: the n words at d equal src's, every byte outside d's 4n bytes unchanged; precondition `wmemcpy_ok` (disjoint areas, 4n < 2^63); copy predicates `wcpf`/`wcpb` in `lib/x64_wcopy.v` |
| `wmemmove` | C, 3 paths (d = s, backward, forward loop) | `proofs/wmemmove_proof.v` | (helper session) **overlap allowed**, precondition only 4n < 2^63: the frames of `wcpf`/`wcpb` are exactly the words written so far, so the next source word is intact iff d is >= 4n (forward) / < 4n (backward) bytes past s mod 2^64 (`wcpf_src`, `wcpb_src`) |
| `wcscpy` | C do-while word copy | `proofs/wcscpy_proof.v` | (helper session) precondition `wcscpy_ok m d src L` (L nonzero words + zero word, disjoint 4(L+1) bytes); post copies L+1 words (`wmoved`) |
| `wcsncmp` | C, signed compare (SETG/CMOVL), entry = loop head, two RETs | `proofs/wcsncmp_proof.v` | (helper session) `wcsncmp_result`: K = n -> 0, else `wcmp` l[K] r[K] |
| `wmemcmp` | C (Ghidra-split lift, merged with FUN_00134f2c) | `proofs/wmemcmp_proof.v` | (helper session) `wmemcmp_result` (`weq_prefix`, no stop at zero words) |
| `memchr` | C, alignment + HASZERO(w^k) word loop + 2 tail loops | `proofs/memchr_proof.v` | precondition: buffer disjoint from the 8 bytes below RSP (RBX spill) |
| `wcslen` | C | `proofs/wcslen_proof.v` | RAX = (4k mod 2^64) >>> 2; `wcslen_ret`: = k when 4k < 2^63 |
| `wcscmp` | C, signed compare (SETL/CMOVG) | `proofs/wcscmp_proof.v` | result exactly -1/0/1; flags via `lib/x64_signed.v` |
| `wcschr` (→ wcslen) | C, composition | `proofs/wcschr_proof.v` | c=0 precondition includes 4L < 2^63 (wcslen's SAR) |
| `wmemchr` | C (Ghidra-split lift, merged) | `proofs/wmemchr_proof.v` | |
| `memrchr` | C, backward pointer walk | `proofs/memrchr_proof.v` | last occurrence |
| `wmemset` | C memory fill (2x unrolled) | `proofs/wmemset_proof.v` | word-level fill predicate `wfil`; precondition 4n ≤ 2^64 |
| labs llabs imaxabs htonl ntohl htons ntohs | C | `proofs/intops_proof.v` (generated by `tools/gen_misc.py`) | abs: exact incl. LONG_MIN; byte swaps by `bitblast_upto` |
| 15 `<ctype.h>` functions | C arithmetic | `proofs/ctype_proof.v` (generated by `tools/gen_ctype.py`) | isalpha isdigit isalnum isupper islower isspace isxdigit isprint isgraph iscntrl isblank isascii toupper tolower toascii; exact result for **every** 32-bit int |

## Open problems / next steps

1. `fegetround` (asm, MXCSR only): the shared lifter models MXCSR as 64-bit
   while Ghidra's p-code treats it as 32-bit; needs a private lifter fix.
2. Remaining lifted but unproved: `strlcpy`, `memccpy`, `strcspn` (helper
   session working on these), `wcscat`, `wcpcpy` (now possible via
   `wcscpy_correct`), `wcsncat`, `a64l` (calls strchr; needs a per-step
   relational spec over the digit table), `bzero` (tail-jumps to memset:
   needs a tail-call composition rule, since the callee's RET is the
   caller's exit).
5. Dedupe `wsame_prefix`/`wcmp`/`dword_load_off` (copied into
   wcsncmp_proof.v) and move `cmovl_wrap` into lib/x64_signed.v.
3. `abs` (lift fails welltyped), `ffs*` (BSF unsupported by the shared lifter;
   it also aborts the rest of a batch), SSE/x87 functions (the lifter emits
   Nop for XMM/x87 instructions, so those lifts are unsound).
4. Proof-time: `stpncpy` (~6 min) and `strcat` (several minutes) are the
   slowest files; most of strcat's time was two `mlia64` calls in the big
   post-call context (now replaced by `qslot`) and its `Qed` (~100 s).

## Lessons learned

* (helper session) Under `all:` with several goals, a `match goal` pattern
  naming local hypotheses/variables (`s1`, `m`, `n`, `k`) fails at
  interning; use `?x` metavariables or `_`.
* (helper session) `exact (H E)` with the wrong orientation of a memory
  (dis)equality unifies two getmem terms and blows up; orient syntactically.
* (helper session) The CMOVL-taken result shape makes `flags_finish` OOM;
  `cmovl_wrap` (in wcsncmp_proof.v / wmemcmp_proof.v) rewrites it first.
* A `Qed`/tactic OOM in a straight-line proof came from `f_equal` (and plain
  `reflexivity`) comparing `1 + K*x` with `K*x + 1` where x is a memory read:
  conversion evaluates.  Rewrite to syntactic equality, then `sreflexivity`.
* Bit-level equalities (rand_r's tempering): enumerate the 32 bits, rewrite
  testbits to leaves, evaluate constant testbits/comparisons, then `btauto`;
  destructing every leaf blows up exponentially.

* **No arithmetic decision procedure in the big post-call context.**  After a
  call, the context holds dozens of hypotheses with `mod 2^64` terms (RSP,
  addresses, frames); `mlia64`/`lia` there took 100+ s or ran out of memory
  even though `arith_only` drops memory hypotheses.  Every address fact
  (slot vs slot `qslot`, slot vs buffer `slot_safe`, store vs prefix
  `prefix_store_noverlap`, ...) is a 2-line lemma proved in an empty
  context; inside the theorem use `exact (lemma ... eq_refl)` or
  `clear - H1 H2; lia`.  Likewise `exact R8`/`assumption` against a goal
  about a different register OOMed (unification unfolds getmem): use
  `sassumption`.
* A string's length is unique (`nilfree_unique`): a callee's strlen result
  can be identified with the caller's precondition length after transferring
  `nilfree` through the caller's stack stores.

* **Lifter aborts a whole batch on one unsupported instruction.** BSF (in
  `ffs*`) has an intra-instruction loop the shared lifter rejects; the
  exception kills the script and every function after it in the batch is
  silently missing.  Lift such functions separately.  `abs` lifts but fails
  its `welltyped` check (set aside in `scratch/abs_amd64.v.bad`).
* **Callee frames.** A callee that writes below its RSP must export
  `stack_frame m m' rsp F` (bytes outside [rsp-F, rsp) unchanged) so callers
  can re-read saved registers, return addresses and their data after the
  call (`stack_frame_get8`, `stack_store_frame`).  Small address-arithmetic
  side conditions (e.g. `str_frame_off`) belong in standalone lemmas: inline
  `lia` with dozens of hypotheses timed out.

* **Never let `reflexivity`/`assumption`/`lia` see a memory term.**
  `conj_tac` (lib/x64_abi.v) now closes leaves only syntactically
  (`sreflexivity`/`sassumption`), and `mlia64` runs `arith_only` (clears every
  hypothesis mentioning memory) before `lia`.  A disequality hypothesis like
  `k mod 2^64 <> e mod 2^64` also makes lia explode; clear it after use.
  The OOMs in memchr came from exactly these.
* `rc.sh` pipes through `grep --line-buffered` so a killed run still shows
  how far it got; wrap experiments in `timeout`.

* **Composing standalone contracts (lib/x64_compose.v).** Picinae's
  `perform_call` needs every function's invariants in one shared family.  To
  reuse an independently proved contract instead, `call_leaf_ni` applies
  `exec_subroutine` with the callee's invariant set *closed* (`close_invs`:
  False outside the callee's code), which is justified by
  `satisfies_all_pmono_ext`: before exiting, a callee never leaves its own
  code (Picinae's `effinv` already demands False there).  Side conditions are
  mechanical (the caller has no invariants inside the callee; callee
  invariants/exits depend only on the trace head).  Put a caller invariant on
  the CALL instruction, `x64_step` once, then apply `call_leaf_ni`.  After
  the call, `models_after_steps` with an explicit trace split restores
  `models`.  Callee postconditions must state memory (and stack) frames.
* `x64_step` substitutes `s R = e` hypotheses into the state, which can
  replace a variable `k` by `s' R_RAX` in the goal; prefer `rewrite` over
  `subst` afterwards.

* **Lift completeness.** Ghidra sometimes splits a function (e.g. it treats
  memcmp's leading `jmp` as a tail call into `FUN_001344ac`), and pcode2coq
  then lifts only the first piece — the program silently lacks most of the
  function and any theorem about it is vacuous on those paths.  Always run
  `tools/check_lift.py` (compares lifted addresses against objdump over the
  symbol's extent); repair with `OUT=... ./lift.sh 'FUN_...'` and
  `tools/merge_lift.py`.  (`setjmp` is flagged only because the hidden
  function after it has no dynamic symbol.)
* C code in proof headers: `(*w)` opens and `*)s` closes a Rocq comment —
  write `( *w)`, `(void * )`.
* `x ⊕ 0xfefefefefefefeff` is normalized by psimpl into `x ⊖ ONES`;
  `haszero_bytes_msub` is stated in that form.

* **Lifter soundness — XMM and x87 status/control registers are dropped.**
  The shared `tools/ghidra-lifter` emits `Nop (* Unmodeled Regs: R_XMM1_DA … *)`
  for SSE lanes and for `FPUSTATUSWORD`/`FPUCONTROLWORD`/x87 env registers.
  Such lifts (`fabs`, `fabsf`, `fabsl`, `sqrt`, `floorl`, `feclearexcept`,
  `fetestexcept`, `fegetenv`, `fesetenv`, `fesetround`'s tail) are
  **unsound** and were deleted.  Always `grep Unmodeled programs/*.v` after
  lifting.  Fixing this needs a Claude-private copy of the lifter that maps
  XMM lanes onto `R_YMMn` slices.
* **MXCSR width mismatch.** Picinae's `x64typctx` gives `R_MXCSR` 64 bits,
  Ghidra writes 32 (LDMXCSR), so `feraiseexcept` does not typecheck.  Not
  fixed (would change the shared `Picinae_amd64.v`).
* **REP string instructions** lift to `Seq (Seq (If (RCX=0) (Jmp next) Nop) …) (Jmp self)`.
  Picinae's `x64_step` does not split an `If` nested that deep and leaves an
  unresolved `exitof a x`; use `x64_step'` from `lib/x64_abi.v`, with the
  loop invariant at the REP instruction itself.
* **Branch-condition normalization must prune as it splits.** Case-splitting
  all 12 flag tests of memset's comparison chain before discarding
  contradictory cases made 4096 copies of the symbolic memory and ran out of
  memory; `bc_norm` now `discriminate`s each branch right after splitting.
* The lifted IMUL broadcast simplifies to `c mod 2^8 * 0x0101010101010101`;
  `rep_ok`/`bytes_are_rep` prove "every byte is c" for such constants by
  evaluation over all 256 bytes.
