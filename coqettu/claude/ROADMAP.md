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
| `x86_64/lib/x64_tail.v` | **tail calls and store-dependent exits**: `tail_leaf(_ni)`, `call_leaf_g(_ni)` (callee invariants may rule out caller exits), `tail_leaf_g_ni` (callee exits land on caller invariants) |
| `x86_64/lib/x64_haszero.v` | musl's HASZERO word trick: `haszero_bytes(_msub)`, `haszero2_bytes`, `nilfree_add8` |
| `x86_64/lib/x64_jmpbuf.v` | jmp_buf layout, write/read-back/frame lemmas |
| `x86_64/lib/x64_ctype.v` | character-class arithmetic (`or32_range`, `range_check`) |
| `x86_64/lib/x64_signed.v` | 32-bit signed compare flags (`s32_norm`, `flags_finish`), `shr63`, `jg1_64` |
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
| `bzero` (tail → memset) | C, JMP into hand-written asm | `proofs/bzero_proof.v` | **tail-call composition** `tail_leaf` (lib/x64_tail.v): bzero's exits are memset's RETs; memset's post implies bzero's |
| `index` (tail → strchr → strchrnul → strlen) | C, JMP | `proofs/index_proof.v` | tail call into a 3-level composite |
| `bcmp` (tail → memcmp) | C, JMP | `proofs/bcmp_proof.v` | `bcmp_nonzero`: result 0 iff the n bytes agree |
| `strrchr` (→ strlen, tail → memrchr) | C, call + tail call | `proofs/strrchr_proof.v` | memrchr's result transferred from the spilled frame to m (`memrchr_result_transfer`); precondition `srch_ok` |
| `rindex` (tail → strrchr) | C, JMP | `proofs/rindex_proof.v` | tail call into a function whose own exit is a tail call |
| `wcscat` (→ wcslen, → wcscpy) | C, two calls | `proofs/wcscat_proof.v` | uses the helper session's `wcscpy_correct` |
| `wcpcpy` (→ wcscpy, → wcslen) | C, two calls | `proofs/wcpcpy_proof.v` | RAX = d + 4L |
| `wcsncat` (→ wcslen) | C, call + word append loop | `proofs/wcsncat_proof.v` | reuses `wcpf`/`wcpf_store` (lib/x64_wcopy.v) with the post-call frame as base memory |
| `strcasecmp` (→ tolower ×4) | C, loop with two calls per iteration + two after | `proofs/strcasecmp_proof.v` | stop index K (`ceq`/`cstop`); the loop memory is abstracted to `frm` (unchanged above the frame, saved registers in their slots), which every return-address store preserves (`frm_ra`) |
| `strncasecmp` (→ tolower ×4) | C, as strcasecmp with an end pointer | `proofs/strncasecmp_proof.v` | n = 0 returns 0; otherwise K < n with K = n-1 or cstop; precondition only on the first n bytes (no termination needed) |
| `strcoll_l` (tail → strcmp), `wcscoll_l` (tail → wcscmp) | C, JMP | `proofs/strcoll_l_proof.v`, `proofs/wcscoll_l_proof.v` | musl collates bytewise / by code point in every locale |
| `a64l` (→ strchr → strchrnul → strlen) | C, loop with a call per digit | `proofs/a64l_proof.v` | relational spec: digit indices `kf i` (first occurrence in the table, `dig`), stop at 6 digits / NUL / non-digit (`nodig`); RAX = sign extension of `acc kf j` (`or_shift32`); loop memory abstracted as `frm96` across strchr's frame |
| 14 ctype `*_l` (tail → isalnum … toupper, ispunct) | C, JMP | `proofs/ctype_l_proof.v` (generated by `tools/gen_ctype_l.py`) | the plain function's post relative to the wrapper's entry state; ispunct_l tails into a composite |
| `strxfrm_l` (→ strlen, → strcpy → stpcpy) | C, call + conditional call | `proofs/strxfrm_l_proof.v` | RAX = strlen(src); copy only when it fits (L < n); psimpl merges the overwritten return-address store, so each call site's memory has its own frame lemma (`frameA`, `frameC`) |
| `wcsxfrm_l` (→ wcslen, → wmemcpy) | C, call + one of two calls | `proofs/wcsxfrm_l_proof.v` | three paths (fits / n = 0 / truncate with a terminating zero word); `wxfrm_res` states the written words; uses the helper session's `wmemcpy_correct` |
| `basename` (→ strlen) | C, call + two loops writing in place | `proofs/basename_proof.v` | NULL/"" → "."; else trailing slashes (`trail`) overwritten with NULs (`zf`), RAX = start of the last component; memory spec relative to the spilled frame (`mb`) |
| `wcsspn` (→ wcschr → wcslen) | C, loop with a call per character | `proofs/wcsspn_proof.v` | set membership stated through wcschr's result (`inset`/`notin`); precondition 0 < c with no wrap (else a match at address 0 would make wcschr return NULL); loop memory `frm64` |
| `wcscspn` (→ wcschr → wcslen, 2 tail calls → wcslen) | C, tail calls + loop with a call per character | `proofs/wcscspn_proof.v` | **store-dependent exit**: wcslen's RET is wcscspn's exit only when RSP = entry RSP (`wcscspn_exit s0`), because the same RET is internal to the wcschr call; composed with the new `call_leaf_g_ni`/`tail_leaf_g_ni`; `wcscspn_pre_static` makes `destruct_inv` usable |
| `wcspbrk` (→ wcscspn) | C, call + LEA + CMOVZ | `proofs/wcspbrk_proof.v` | RAX = NULL when s[K] = 0, else s + 4K with s[K] in the set; 80-byte frame; transfer lemmas `cspre_agree`/`inset_agree` move wcscspn's post from the call-time memory to m |
| `dirname` (→ strlen) | C, call + three loops, five returns, one in-place NUL | `proofs/dirname_proof.v` | shapes all-'/' → "/", A B → ".", S A B → "/", P S A B → s with s[h+1] = 0 (`allsl`/`nosl`/`trail`); "." and "/" checked as bytes 2e 00 / 2f 00 in the binary; reuses basename's `bn_ok`, `trail`, `outside32` |
| `wcstok` (→ wcsspn → wcschr → wcslen; → wcscspn → wcschr/wcslen) | C, two calls, saved-pointer state, two stores | `proofs/wcstok_proof.v` | s = NULL resumes from *p (`ts`); post: K1 delimiters skipped (`spanpre`), then NULL with *p = 0, or token t = s1+4K1 of length K2 (`cspre`) with the delimiter after it overwritten by 0 and *p = t+4K2+4 (or *p = 0 at the end); precondition: p and the strings outside the 96-byte frame, p disjoint from s1 (restrict); 96-byte frame `frm96` across both calls (their frames coincide) |
| `remque` | C, two guarded pointer stores | `proofs/remque_proof.v` | functional spec `remque_mem` follows the C abstract machine's re-reads after the first store (the stores may alias the element) |
| `strcasestr` (→ strlen, → strncasecmp → tolower) | C, call + loop with a call per position | `proofs/strcasestr_proof.v` | L = 0 returns h (hoisted); `imatch` = strncasecmp(h+i, n, L) = 0 (unique stop index, `ncase_unique`); 80-byte frame `frm80`; precondition: h's Lh+L+1 bytes outside the frame (strncasecmp may read L bytes past any h+i) |
| ldiv lldiv imaxdiv | C, CQO; IDIV | `proofs/divs_proof.v` | RAX/RDX = ofZ 64 (Z.quot/Z.rem (toZ 64 num) (toZ 64 den)); the lift models IDIV as 128-bit SDIVIDE/SMOD without the #DE fault, so the result is meaningful under C's den <> 0 / no-overflow precondition; `cqo_join` shows CQO's RDX:RAX is scast 64 128 |
| `__rand48_step` (hidden, FUN_0015c18f), `nrand48`/`jrand48` (→ step), `lrand48`/`mrand48` (tail → nrand48/jrand48) | C, 48-bit LCG; call; tail | `proofs/rand48_proof.v` | v = c + X*A on the dword+word encodings (`ld48`, `r48v`); RAX = (v mod 2^48) >> 17, resp. sign-extended low 32 bits of (v mod 2^48) >> 16; state words updated (`r48_out16`); precondition: s and __seed48+3 outside the 16-byte frame (`n48_ok`). seed48/srand48/lcong48 call memcpy (blocked) |
| iswdigit iswxdigit iswcntrl iswblank + `_l` variants | C; JMP wrappers (iswblank_l → iswblank → isblank nested) | `proofs/wctype_proof.v` (generated by `tools/gen_wctype.py`) | iswdigit/iswxdigit are instruction-identical to isdigit/isxdigit: specs and scripts reused; iswcntrl reuses the isdigit script with its own ranges |
| `iswspace` (→ wcschr → wcslen), `iswspace_l` (tail) | C, call with a .rodata table | `proofs/iswspace_proof.v` | precondition `spc_ok`: memory holds the 22-word table at 0x173360 (checked against the binary bytes); RAX = [w <> 0 and w ∈ spaces]; 48-byte frame |
| `strcasecmp_l`, `strncasecmp_l` | C, JMP into strcasecmp / strncasecmp | `proofs/case_l_proof.v` | callee post restated for the wrapper's entry state |
| `explicit_bzero` (→ memset) | C, call | `proofs/explicit_bzero_proof.v` | precondition: the buffer is off the 16 bytes below rsp (the inner return address) |
| cfgetospeed cfgetispeed dirfd telldir ns_get16 | C field reads | `proofs/fieldget_proof.v` | ns_get16 = `getmem 64 BigE 2` (`be16` via `getmem_split`) |
| inet_netof inet_lnaof inet_makeaddr | C, sign test + CMOVA | `proofs/inet_legacy_proof.v` | classful specs on the 32-bit host-order value; `bc_norm` splits the CMOVA cases; `mk_eq` (bitwise) for makeaddr |
| posix_spawnattr_{destroy,getflags,setflags,getpgroup,setpgroup,get/setschedparam,get/setschedpolicy} | C accessors | `proofs/spawnattr_proof.v` | exact memory update per accessor; setflags: EINVAL (22) iff the sign-extended short exceeds 0xff (`sc16`); sched ones return ENOSYS (38). getsigdefault/getsigmask copy 128 bytes with SSE (unsound lift, not proved) |
| `posix_spawnattr_init` | C, REP STOSQ (42 qwords) | `proofs/spawnattr_init_proof.v` | cut at the REP instruction with a `fil` invariant (as memset); post `filled m M attr 0 336` |
| `wmemcpy` | C word copy loop | `proofs/wmemcpy_proof.v` | (helper session) `wmoved` post: the n words at d equal src's, every byte outside d's 4n bytes unchanged; precondition `wmemcpy_ok` (disjoint areas, 4n < 2^63); copy predicates `wcpf`/`wcpb` in `lib/x64_wcopy.v` |
| `wmemmove` | C, 3 paths (d = s, backward, forward loop) | `proofs/wmemmove_proof.v` | (helper session) **overlap allowed**, precondition only 4n < 2^63: the frames of `wcpf`/`wcpb` are exactly the words written so far, so the next source word is intact iff d is >= 4n (forward) / < 4n (backward) bytes past s mod 2^64 (`wcpf_src`, `wcpb_src`) |
| `wcscpy` | C do-while word copy | `proofs/wcscpy_proof.v` | (helper session) precondition `wcscpy_ok m d src L` (L nonzero words + zero word, disjoint 4(L+1) bytes); post copies L+1 words (`wmoved`) |
| `wcsncmp` | C, signed compare (SETG/CMOVL), entry = loop head, two RETs | `proofs/wcsncmp_proof.v` | (helper session) `wcsncmp_result`: K = n -> 0, else `wcmp` l[K] r[K] |
| `wmemcmp` | C (Ghidra-split lift, merged with FUN_00134f2c) | `proofs/wmemcmp_proof.v` | (helper session) `wmemcmp_result` (`weq_prefix`, no stop at zero words) |
| `memchr` | C, alignment + HASZERO(w^k) word loop + 2 tail loops | `proofs/memchr_proof.v` | precondition: buffer disjoint from the 8 bytes below RSP (RBX spill) |
| `wcslen` | C | `proofs/wcslen_proof.v` | RAX = (4k mod 2^64) >>> 2; `wcslen_ret`: = k when 4k < 2^63 |
| `wcscmp` | C, signed compare (SETL/CMOVG) | `proofs/wcscmp_proof.v` | result exactly -1/0/1; flags via `lib/x64_signed.v` |
| `wcschr` (→ wcslen) | C, composition | `proofs/wcschr_proof.v` | c=0 precondition includes 4L < 2^63 (wcslen's SAR); invariant at wcslen's RET 0x13c3a1 (RSP = entry − 32) so callers that also tail-call wcslen can tell the two RETs apart |
| `wmemchr` | C (Ghidra-split lift, merged) | `proofs/wmemchr_proof.v` | |
| `memrchr` | C, backward pointer walk | `proofs/memrchr_proof.v` | last occurrence |
| `wmemset` | C memory fill (2x unrolled) | `proofs/wmemset_proof.v` | word-level fill predicate `wfil`; precondition 4n ≤ 2^64 |
| labs llabs imaxabs htonl ntohl htons ntohs | C | `proofs/intops_proof.v` (generated by `tools/gen_misc.py`) | abs: exact incl. LONG_MIN; byte swaps by `bitblast_upto` |
| 15 `<ctype.h>` functions | C arithmetic | `proofs/ctype_proof.v` (generated by `tools/gen_ctype.py`) | isalpha isdigit isalnum isupper islower isspace isxdigit isprint isgraph iscntrl isblank isascii toupper tolower toascii; exact result for **every** 32-bit int |

## Open problems / next steps

1. `fegetround` (asm, MXCSR only): the shared lifter models MXCSR as 64-bit
   while Ghidra's p-code treats it as 32-bit; needs a private lifter fix.
2. Remaining lifted but unproved: `strlcpy`, `memccpy`, `strcspn` and the
   strspn/strpbrk/strsep/strtok family (helper session; its WIP is in
   scratch/h_*.v and stopped on 11-16 — h_strcspn.v fails at one `erewrite
   getmem_frame_mem` that leaves the memory as an evar; left untouched, the
   files are the helper's).  Also lifted, unproved: ns_get32, ns_put16,
   ns_put32 (BSWAP/ROL: need a byte-level spec lemma), div, memmove, bcopy.
6. `strcoll`/`wcscoll`: their first instruction reads the thread pointer
   FS:[0]; the shared lifter emits `Nop (* Unmodeled Regs: R_FS_OFFSET *)`
   and then loads from an unassigned temporary, so the lift fails
   `welltyped` (scratch/strcoll_amd64.v.bad, wcscoll_amd64.v.bad).  A
   private lifter fix modeling FS_OFFSET as a register would unlock them
   (then: tail into strcoll_l/wcscoll_l, which are proved).
8. `memcpy` is musl's C memcpy compiled with SSE (MOVDQU/MOVUPS/PSHUFD for
   the 16-byte and misaligned-shift loops), which the shared lifter emits as
   Nop: the lift is unsound (scratch/memcpy_amd64.v.bad).  This also blocks
   `memmove` (its forward path JMPs to memcpy) and `bcopy` (JMP memmove);
   their lifts are in programs/ for when memcpy is unblocked.
7. `div` (int): lifted, and a proof script ran (CDQ join lemma analogous
   to `cqo_join`, result packing via `lor_shl`), but the kernel check at Qed does not
   finish in 40 min: the first three steps (MOV, CDQ, IDIV ESI) already
   cost 38 s, and SHL/OR over the symbolic 64-bit SDIVIDE/SMOD results blow
   up even when those are `remember`ed.  Needs a cheaper decomposition (e.g.
   a hand-proved step lemma for IDIV ESI).
5. Dedupe `wsame_prefix`/`wcmp`/`dword_load_off` (copied into
   wcsncmp_proof.v) and move `cmovl_wrap` into lib/x64_signed.v.
3. `insque` (its NULL-prev path zeroes the node with PXOR/MOVUPS, emitted as
   Nop by the shared lifter; the lift fails `welltyped`, set aside as
   scratch/insque_amd64.v.bad), `abs` (lift fails welltyped), `ffs*` (BSF unsupported by the shared lifter;
   it also aborts the rest of a batch), SSE/x87 functions (the lifter emits
   Nop for XMM/x87 instructions, so those lifts are unsound).
4. Proof-time: `stpncpy` (~6 min) and `strcat` (several minutes) are the
   slowest files; most of strcat's time was two `mlia64` calls in the big
   post-call context (now replaced by `qslot`) and its `Qed` (~100 s).

## Lessons learned

* **Tail calls (lib/x64_tail.v).** `tail_leaf` is `exec_subroutine` with the
  callee's invariants closed off outside its code, like `call_leaf`, except
  that the caller has invariants/exits exactly at the callee's exits and
  `may_call`'s implication there is "callee post implies caller post".  A
  wrapper's postcondition is the callee's, restated for the wrapper's entry
  state (they agree on RSP and the callee-saved registers).  Tail calls
  compose (rindex → strrchr → memrchr).
* **Shared callee, two roles (lib/x64_tail.v `call_leaf_g`).** wcscspn
  tail-calls wcslen and also calls wcschr, which calls wcslen.  wcslen's RET
  is then both wcscspn's exit and an internal point of the wcschr call, and
  `may_call` is universal over traces, so no address-only exit works.  Fix:
  (1) make the exit depend on the store (`RSP =? s0 RSP`) and the invariant
  there `if RSP =? s0 RSP then Some post else None`; (2) give the inner
  callee (wcschr) an invariant at that RET (its RSP is lower); (3) use
  `call_leaf_g`, whose CALLER premise may use the callee's invariant
  (`post_or_true (Invs2 t) -> Invs1 t = None /\ xp1 t = false`), and
  `tail_leaf_g_ni`, whose callee exits may land on caller invariants (it
  also turns a CALL into a cut at the callee's RET, which is how wcschr got
  its new invariant).  `destruct_inv` cannot decide `RSP =? s0 RSP`; first
  rewrite PRE with a lemma replacing the exit/invariant by static versions
  (the precondition there is None either way).
* **OOM from unification in a big context.**  `apply`/`rewrite` with `_`
  arguments over memory terms (e.g. `rewrite (r48v_frame m xi lc _ _ H1 H2)
  in A, B, C`, `apply (stack_store_frame _ ...)`) can exhaust memory after a
  CALL composition; give all arguments, or state a tiny lemma (`frame16`)
  and `exact` it.  Before stepping CDQE/sign-extension over a large symbolic
  value, `remember` it (`remember (r48v m xi lc) as V eqn:EV in *`).
* **Kernel time at Qed is not the tactic time.**  Bisect a hanging `Qed` by
  closing the goal early with a scratch-only `Axiom BISECT_AX: forall P, P`
  after k steps (never in proofs/).  `simpl in PRE` on a post whose
  argument is `p ⊕ 4*k` unfolds `4*k` into a `match`: shield it with
  `set (bb := ...) in PRE` around the simpl.
* `x64_step` stops at a cut but otherwise runs into the callee's code; when
  the callee entry is not a cut of the caller, step a fixed number of times
  (`x64_step. x64_step. ...`) and then apply call_leaf/tail_leaf.
* A `set (X := mem ...)` hides the memory from psimpl: a RET that reads the
  return address through `X` leaves an unresolved jump target.  Unfold the
  abbreviation (or prove the read as a lemma and rewrite it) before stepping.

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
