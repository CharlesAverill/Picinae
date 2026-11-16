# Grok Bot (agent coqettu) — ROADMAP

Assignment: musl-1.2.6-r6 (Alpine) **aarch64** —
`coqettu/alpine_musl/aarch64/lib/libc.musl-aarch64.so.1`
(sha256 4723e4ca…141e). All artifacts live in `grok-bot/aarch64/`.

## Layout (grok-bot/aarch64)
- `ghidra/` — our own Ghidra project `musl_aarch64` (binary imported + auto-analysed
  with Ghidra 12.0; program name `ld-musl-aarch64.so.1`, image base 0x100000).
- `lift.sh '<regex>'` — headless lift with pcode2coq (`--globalAddressing --typeCheck`)
  into `lifted_raw/` (all raw lifter output, untouched).
- `lifted/` — the lifted programs actually used by proofs (copies from lifted_raw).
- `lib/GrokCommon.v` — shared lemmas/tactics (bounds, cbz/cbnz branch-condition
  normalisation, modular address facts, msub, nilfree/mem_eq, AAPCS64 callee-saved list + tactic).
- `lib/GrokStep.v` — `grok_step` (arm8_step that also splits an `if` nested inside one
  instruction's statement list, needed for `ccmp`) and `splits`.
- `lib/GrokBits.v` — byte_of, haszero/hasbyte word-at-a-time lemmas, splat, xor bytes.
- `lifter/` — patched copy of pcode2coq (see lifter/README_GROK.md); `lifted_raw_upstream/` holds
  upstream-lifter outputs for comparison.
- `headers/<fn>.txt` + `tools/finalize.py` — turn a scratch proof into `proofs/<fn>_proof.v` with the
  standard header (PROVENANCE, Model line) and frame theorems.
- `chk.sh` — compile single files with the project flags (8 GB cap); `scratch/` — work in progress.
- `proofs/<fn>_proof.v` — spec + header + proofs; `proofs/Assumptions.v` prints axioms.
- `picinae/` — symlinks to the pre-built Picinae .v/.vo in `~/research/picinae-llm`
  (used instead of `-R ~/research/picinae-llm` so coqc never scans other agents' dirs).
- `make` builds everything (8 GB ulimit); `make assumptions` re-runs the axiom audit.

## Solved (fully machine-checked, no Admitted, no new axioms)
Entry = Ghidra address (ELF vaddr + 0x100000). Every proof file also has the frame theorems
`<fn>_preserves_memory`, `<fn>_preserves_callee_saved` (AAPCS64 X19–X29, SP, Z8–Z15),
`<fn>_preserves_x30`, `<fn>_welltyped`, `<fn>_nwc` (composed proofs — wcsnlen, strnlen, wcschr,
strchrnul, strchr — instead state X29/X30/SP/memory in the post and `<fn>_preserves_other_callee_saved`).

| function | entry | file | main theorem (+ extras) |
|---|---|---|---|
| wcslen | 0x15fc18 | proofs/wcslen_proof.v | wcslen_partial_correctness (+ result_small, post_unique) |
| memcmp | 0x15e2a8 | proofs/memcmp_proof.v | memcmp_partial_correctness (+ result_sign, result_nonzero) |
| strcmp | 0x15eca4 | proofs/strcmp_proof.v | strcmp_partial_correctness (+ result_sign) |
| wcscmp | 0x15fb00 | proofs/wcscmp_proof.v | wcscmp_partial_correctness (+ result_sign); needs BOOL_NEGATE fix |
| strlen (word-at-a-time) | 0x15efa8 | proofs/strlen_proof.v | strlen_partial_correctness (+ post_unique) |
| memchr (word-at-a-time) | 0x15e1ec | proofs/memchr_proof.v | memchr_partial_correctness (first match or NULL) |
| tolower | 0x11f2d0 | proofs/tolower_proof.v | tolower_partial_correctness (all 2^32 inputs) |
| toupper | 0x11f2e8 | proofs/toupper_proof.v | toupper_partial_correctness |
| abs | 0x15cf94 | proofs/abs_proof.v | abs_partial_correctness (X0 = ofZ 32 \|toZ 32 j\|) |
| labs | 0x15d388 | proofs/labs_proof.v | labs_partial_correctness |
| llabs | 0x15d3a4 | proofs/llabs_proof.v | llabs_partial_correctness |
| wmemchr | 0x1601d0 | proofs/wmemchr_proof.v | wmemchr_partial_correctness (lift = Ghidra FUN_001601d8) |
| wmemcmp | 0x1601f8 | proofs/wmemcmp_proof.v | wmemcmp_partial_correctness (unsigned wchar_t, ±1/0) |
| wcsncmp | 0x15fd34 | proofs/wcsncmp_proof.v | wcsncmp_partial_correctness (uses grok_step for ccmp) |
| strncmp | 0x15f110 | proofs/strncmp_proof.v | strncmp_partial_correctness (+ result_value) |
| wcsnlen (+ wmemchr callee) | 0x15fdb4 | proofs/wcsnlen_proof.v | wcsnlen_partial_correctness, wmemchr_correct_in_wcsnlen (+ result_small, preserves_other_callee_saved); first caller/callee composition via perform_call |
| strnlen (+ memchr callee) | 0x15f1c0 | proofs/strnlen_proof.v | strnlen_partial_correctness, memchr_correct_in_strnlen (+ preserves_other_callee_saved) |
| wcschr (+ wcslen callee) | 0x15fab4 | proofs/wcschr_proof.v | wcschr_partial_correctness, wcslen_correct_in_wcschr (+ preserves_other_callee_saved); c=0 path via wcslen, lemma ashiftr2_shl2 |
| strchrnul (+ strlen callee) | 0x15ebf4 | proofs/strchrnul_proof.v | strchrnul_partial_correctness, strlen_correct_in_strchrnul (+ chrnul_test, preserves_other_callee_saved) |
| ffs | 0x13b294 | proofs/ffs_proof.v | ffs_partial_correctness (W0 = 1 + lowest set bit, or 0); rbit checked by reflection (lib/GrokBitRefl.v); needs LZCOUNT fix |
| ffsl | 0x13b2ac | proofs/ffsl_proof.v | ffsl_partial_correctness (64-bit input) |
| ffsll | 0x13b2c8 | proofs/ffsll_proof.v | ffsll_partial_correctness (64-bit input) |
| strchr (+ strchrnul + strlen callees) | 0x15ebcc | proofs/strchr_callees.v, proofs/strchr_proof.v | strchr_partial_correctness, strchrnul_correct_in_strchr, strlen_correct_in_strchr (+ preserves_other_callee_saved); 3-level composition; needs lifter fix 3 (UXTB) |
| wmemset | 0x160294 | proofs/wmemset_proof.v | wmemset_partial_correctness (memory = wset m p c n, store chain) |
| wmemcpy | 0x16022c | proofs/wmemcpy_proof.v | wmemcpy_partial_correctness (memory = wcpy m d q n, sequential copy, exact even with overlap) |
| wcscpy | 0x15fb2c | proofs/wcscpy_proof.v | wcscpy_partial_correctness (copy through terminator; wcpy/wnz over intermediate memories) |
| swab | 0x15f9d8 | proofs/swab_proof.v | swab_partial_correctness (floor(n/2) pairs for signed n ≥ 0, none for n < 0); signed b.gt via lib/GrokSigned.v gt1_test |
| wmemmove | 0x16024c | proofs/wmemmove_proof.v | wmemmove_partial_correctness (d=q / backward bcpy / forward wcpy by the binary's unsigned test; lemmas addr_shl2_mod, bk_addr for psimpl's `msub 62 j 1 << 2`) |
| wcsrchr (+ wcslen callee) | 0x15fe20 | proofs/wcsrchr_proof.v | wcsrchr_partial_correctness, wcslen_correct_in_wcsrchr (+ preserves_other_callee_saved); precondition wpre (4 <= p, string does not wrap); callee invariants carry X19/X20 |
| isdigit | 0x11ee64 | proofs/isdigit_proof.v | isdigit_partial_correctness (X0 = 1 iff c mod 2^32 in 0x30..0x39, all 2^32 inputs; generated by tools/gen_ctype.py, lemma ls_test in lib/GrokCtype.v) |
| isupper | 0x11ef00 | proofs/isupper_proof.v | isupper_partial_correctness (X0 = 1 iff c mod 2^32 in 0x41..0x5a, all 2^32 inputs; generated by tools/gen_ctype.py, lemma ls_test in lib/GrokCtype.v) |
| islower | 0x11ee8c | proofs/islower_proof.v | islower_partial_correctness (X0 = 1 iff c mod 2^32 in 0x61..0x7a, all 2^32 inputs; generated by tools/gen_ctype.py, lemma ls_test in lib/GrokCtype.v) |
| isprint | 0x11eea0 | proofs/isprint_proof.v | isprint_partial_correctness (X0 = 1 iff c mod 2^32 in 0x20..0x7e, all 2^32 inputs; generated by tools/gen_ctype.py, lemma ls_test in lib/GrokCtype.v) |
| isgraph | 0x11ee78 | proofs/isgraph_proof.v | isgraph_partial_correctness (X0 = 1 iff c mod 2^32 in 0x21..0x7e, all 2^32 inputs; generated by tools/gen_ctype.py, lemma ls_test in lib/GrokCtype.v) |
| isascii | 0x11ee30 | proofs/isascii_proof.v | isascii_partial_correctness (X0 = 1 iff c mod 2^32 <= 0x7f; same generator) |
| imaxabs | 0x15d36c | proofs/imaxabs_proof.v | imaxabs_partial_correctness (same code and spec as labs) |
| ldiv | 0x15d394 | proofs/ldiv_proof.v | ldiv_partial_correctness (X0 = sdiv64, X1 = srem64; den = 0 case included) + ldiv_semantics (toZ = Z.quot / Z.rem when den <> 0 and no INT64_MIN/-1 overflow; lib/GrokDiv.v); generated by tools/gen_div.py |
| lldiv | 0x15d3b0 | proofs/lldiv_proof.v | lldiv_partial_correctness + lldiv_semantics (identical code to ldiv) |
| imaxdiv | 0x15d378 | proofs/imaxdiv_proof.v | imaxdiv_partial_correctness + imaxdiv_semantics (identical code to ldiv) |
| sigemptyset | 0x15221c | proofs/sigemptyset_proof.v | sigemptyset_partial_correctness (X0 = 0, memory = 8-byte store of 0 at set; _NSIG = 65); tools/gen_sigset.py |
| sigfillset | 0x152228 | proofs/sigfillset_proof.v | sigfillset_partial_correctness (X0 = 0, 8-byte store of 0xfffffffc7fffffff: signals 32..34 excluded) |
| sigismember | 0x152330 | proofs/sigismember_proof.v | sigismember_partial_correctness (X0 = bit (sig-1) of word at set if (sig-1) mod 2^32 < 64, else 0; lib/GrokSig.v) |
| pthread_equal | 0x162f00 | proofs/pthread_equal_proof.v | pthread_equal_partial_correctness (X0 = 1 iff X0 = X1, 64-bit) |
| ns_get16 | 0x143f4c | proofs/ns_get16_proof.v | ns_get16_partial_correctness (X0 = getmem BigE 2 at src); rev16 network vs revbytes by reflection (lib/GrokBytes.v) |
| ns_get32 | 0x143f5c | proofs/ns_get32_proof.v | ns_get32_partial_correctness (X0 = getmem BigE 4 at src) |
| ns_put16 | 0x143f68 | proofs/ns_put16_proof.v | ns_put16_partial_correctness (memory = setmem BigE 2 dst src) |
| ns_put32 | 0x143f74 | proofs/ns_put32_proof.v | ns_put32_partial_correctness (memory = setmem BigE 4 dst src) |
| div | 0x15d170 | proofs/div_proof.v | div_partial_correctness (X0 = sdiv32 \| srem32 << 32, packed div_t) + div_semantics (Z.quot/Z.rem, 32-bit; lib/GrokDiv.v) |
| isalpha | 0x11ee18 | proofs/isalpha_proof.v | isalpha_partial_correctness (X0 = 1 iff c mod 2^32 in 'A'..'Z' or 'a'..'z'; (c\|32) test via lib/GrokCtype2.v alpha_or32, finite check below 128) |
| isalnum | 0x11edec | proofs/isalnum_proof.v | isalnum_partial_correctness (two paths; digits or letters) |
| isxdigit | 0x11f29c | proofs/isxdigit_proof.v | isxdigit_partial_correctness (two paths; 0-9, A-F, a-f) |
| iscntrl | 0x11ee50 | proofs/iscntrl_proof.v | iscntrl_partial_correctness (X0 = 1 iff c mod 2^32 < 0x20 or = 0x7f); ccmp stepped with grok_step |
| isblank | 0x11ee3c | proofs/isblank_proof.v | isblank_partial_correctness (X0 = 1 iff c mod 2^32 in {0x20, 0x09}) |
| isspace | 0x11eee8 | proofs/isspace_proof.v | isspace_partial_correctness (X0 = 1 iff c mod 2^32 = 0x20 or in 0x09..0x0d) |
| iswdigit | 0x11f0c8 | proofs/iswdigit_proof.v | iswdigit_partial_correctness (identical code to isdigit; wctype man page) |
| iswxdigit | 0x11f270 | proofs/iswxdigit_proof.v | iswxdigit_partial_correctness (identical code to isxdigit) |
| insque | 0x1513fc | proofs/insque_proof.v | insque_partial_correctness (memory = insque_mem: the C code's loads/stores in order, aliasing modelled) |
| remque | 0x151424 | proofs/remque_proof.v | remque_partial_correctness (memory = remque_mem, same style) |
| stpcpy | 0x15e950 | proofs/stpcpy_proof.v | stpcpy_partial_correctness (full: aligned word path + byte paths; memory = bcp mem d q (k+1), sequential byte copy, no non-overlap precondition; X0 = d+k; word store = 8 byte copies when (q-d) mod 8 = 0, haszero_none' in lib/GrokStr.v) |
| strcpy (+ stpcpy callee) | 0x15eccc | proofs/strcpy_proof.v | strcpy_partial_correctness, stpcpy_correct_in_strcpy, strcpy_preserves_other_callee_saved (X0 = d; memory = bcp over the saved-frame memory; X19/X29/X30 = values read back from the frame) |
| wcpcpy (+ wcscpy, wcslen callees) | 0x15fa04 | proofs/wcpcpy_proof.v | wcpcpy_partial_correctness, wcscpy_correct_in_wcpcpy, wcslen_correct_in_wcpcpy, wcpcpy_preserves_other_callee_saved (X0 = d + 4L, L = wcslen of src on the final memory; two sequential calls via perform_call 1 then 0) |
| bcmp (tail call to memcmp) | 0x15e0e8 | proofs/bcmp_proof.v | bcmp_partial_correctness (memcmp_post: 0 iff all n bytes equal, else the nonzero byte difference), bcmp_preserves_callee_saved |
| wcscat (+ wcslen, wcscpy callees) | 0x15fa80 | proofs/wcscat_proof.v | wcscat_partial_correctness, wcslen_correct_in_wcscat, wcscpy_correct_in_wcscat, wcscat_preserves_other_callee_saved (X0 = d; memory = wcpy over the frame memory at d+4L) |
| htonl | 0x141de8 | proofs/htonl_proof.v | htonl_partial_correctness (X0 = revbytes (x mod 2^32) 4; bit-reflection proof with GrokBitRefl reify_bx/bbnd) |
| ntohl | 0x1443bc | proofs/ntohl_proof.v | ntohl_partial_correctness (same code/spec as htonl) |
| htons | 0x141df0 | proofs/htons_proof.v | htons_partial_correctness (X0 mod 2^16 = revbytes (x mod 2^16) 2, X0 < 2^32) |
| ntohs | 0x1443c4 | proofs/ntohs_proof.v | ntohs_partial_correctness (same code/spec as htons) |
| toascii | 0x11f2c8 | proofs/toascii_proof.v | toascii_partial_correctness (X0 = c mod 128) |
| strncat | 0x15f0b4 | proofs/strncat_proof.v | strncat_partial_correctness (precondition strncat_pre: strings, frame, non-overlap) |
| wcsncat | 0x15fcdc | proofs/wcsncat_proof.v | wcsncat_partial_correctness (precondition wcsncat_pre: wide strings, frame, non-overlap; calls wcslen) |
| wcsncpy | 0x15fd70 | proofs/wcsncpy_proof.v | wcsncpy_partial_correctness (precondition wcsncpy_pre: source length, frame, non-overlap; calls wmemset) |
| strcat | 0x15eb98 | proofs/strcat_proof.v | strcat_partial_correctness (precondition strcat_pre: strings, frames, non-overlap) |

`make` (in aarch64/) rebuilds all of these; `proofs/Assumptions.v` (last full CLEAN build `make clean; make -j3` 07:11–07:48 CST Nov 16, BUILD_EXIT=0, 70 Print Assumptions covering the 58 functions through remque: 65 report only functional_extensionality_dep, 5 closed. Incremental make 07:53–07:59 BUILD_EXIT=0 with stpcpy/strcpy/wcpcpy: 76 prints, 71 only functional_extensionality_dep, 5 closed. Incremental make 08:00:44–08:04:32 CST BUILD_EXIT=0 with bcmp/wcscat: 80 prints, 75 only functional_extensionality_dep, 5 closed. Latest: incremental make 08:06:14–08:08:41 CST, BUILD_EXIT=0, 84 Print Assumptions covering all 69 functions: 79 report only functional_extensionality_dep, 5 closed; log aarch64/build_logs/make.log. Incremental make with strcat 09:24:58–09:36:15 CST BUILD_EXIT=0. make 10:29:09–10:33:18 CST BUILD_EXIT=0 (85 prints, strcat confirmed). make 10:34:09–10:38:07 CST BUILD_EXIT=0 (86 prints, toascii). make 11:05:28–11:16:00 CST BUILD_EXIT=0 (87 prints, strncat). targeted build 11:26:32–11:31:24 CST (wcsncat, 88 prints). NEWEST: targeted build 11:37:26–11:40:20 CST (coqc proofs/wcsncpy_proof.v then proofs/Assumptions.v, both exit 0; other .vo unchanged), 89 Print Assumptions covering 74 functions (incl. wcsncpy): 84 report exactly one axiom, functional_extensionality_dep, 5 closed; log aarch64/build_logs/assumptions.log) prints only
`functional_extensionality_dep` (inherited from Picinae) for every main theorem.

## In progress / next
- Composition recipe (done for wcsnlen): one invariant family; caller = id 1, callee = id 0 with the
  caller's X19/X20/X29 added to every callee invariant; callee memory = `frame_mem` (explicit
  `mem [Ⓠ sp⊖32 := x29] [Ⓠ sp⊖24 := raddr] ...`, NOT generalize_frame, so the restoring ldp's
  simplify); post-call: `perform_call 0` + `destruct_inv`.
- (done) strnlen (0x15f1c0) = wrapper around memchr: needs a combined caller+callee invariant set
  (perform_call, see Picinae Examples/arm8_strcasecmp_proof.v). Plan: one invariant family with
  memchr points as id 0 carrying the caller's X19/X20/X29 and stack frame; re-run the memchr
  proof script on it. Same pattern then gives wcsnlen (wmemchr), wcschr (wcslen).
- (done 05:38) strchr: Qed. The "remaining open goals" at Qed was a hidden second goal: strchrnul has
  two RETs (0x15ec40, 0x15eca0), so destruct_inv after perform_call gives 2 goals; a plain
  `destruct PRE` + bullets handled only the first. Fix: `all: destruct PRE ...; [case1 | case2]`.
- (done 06:17) wcsrchr.
- (done 06:35-06:42) ldiv/lldiv/imaxdiv (+ Z.quot/Z.rem semantics), sigemptyset, sigfillset,
  sigismember, pthread_equal.
- (done 06:46) ns_get16/32, ns_put16/32 (lib/GrokBytes.v: bperm_check reflection + setmem_big_little).
- (done 06:51) div (32-bit; packed div_t in X0).
- (done 06:58) isalpha/isalnum/isxdigit.
- (done 07:01) iscntrl/isblank/isspace (ccmp: arm8_step gets stuck, grok_step works).
- (done 07:03) iswdigit, iswxdigit.
- (done 07:08) insque, remque.
- (done 07:28) stpcpy Qed (lib/GrokStr.v: bcp/bnz copy model, frame8, haszero_none/haszero_none').
- (done 07:44) strcpy Qed (composition with stpcpy via perform_call).
- (done 07:51) wcpcpy Qed (3 ids: wcslen 0, wcscpy 1, wcpcpy 2; second call after first: `do 4 arm8_step` from the callee RET).
- (done 07:57) bcmp; (done 08:00) wcscat.
- (done 08:06) htonl/htons/ntohl/ntohs (make 08:08 OK).
- (done 09:20, coqc Qed) strcat (0x15eb98, proofs/strcat_proof.v; ids strlen 0, stpcpy 1, strcpy 2, strcat 3)
  WITH AN EXPLICIT PRECONDITION strcat_pre (approved 08:51): d/q strings of lengths Ld/Lq, dest range and
  src range below sp-80 (below both stack frames), written range disjoint from src (overlap is UB in C).
  Post: mem = bcp F (d+Ld) q (Lq+1), X0 = d, SP/X29/X30/X19 restored. New lib/GrokFrame.v
  (getmem_setmem_below/above, bcp_read_above/below: reads disjoint from stores). first_zero_unique
  lemma gives strlen/copy length = Ld/Lq. Proof term large (coqc ~4 min).
- PARKED (10:30) memccpy (0x15e128, scratch/memccpy.v, debug copy scratch/memccpy_dbg.v; ~50 min spent).
  Entry, aligned-prefix (0x15e140) and byte-loop (0x15e1c0) cases and the word-loop exit cases go through.
  Exact obstacle: the word-loop step case at 0x15e194 (no byte = c in the 8-byte word, branch "MARK 10").
  (a) generic `lia`/`modeq` on that goal's large context (K8 constants, N.land masks, 2^64) runs coqc out
  of memory (Fatal error after ~9 min, again 'Out of memory' at the KK/land_mask8 side goal); replaced
  by targeted lemmas (land_mask8 with explicit bound, clear-before-lia).
  (b) the remaining sub-step, proving k ≠ K from the branch hypothesis BC (displayed `k ⊖ k0 = n - k0 .& ~7`),
  fails: `rewrite msub_small`/`rewrite (x ⊖ y = x - y)` find no matching subterm and `transitivity (k - k0)`
  reports "variable k not found", i.e. the displayed names/terms in the goal after `apply BC` are not the
  context's k/k0 (needs inspection with Set Printing All). Each attempt costs ~2.5 min compile to reach it.
- PARKED (10:30) memset restricted path n <= 96 (scratch/memset.v, ~25 min). Done: lib/GrokFill.v compiles
  (zsplat_check reflection for the `dup v0.16B,w1` splat, read_in/read_out byte reads through overlapping
  stores, byte_mod/splat_mod); the splat expression produced by psimpl is proved splat (checked in
  scratch/splat_test.v). Blockers: (1) without an invariant after the dup, symbolic execution of the
  256-bit Z0 expression ran coqc out of memory after 15 min; (2) with Z0 abstracted at 0x118404, the
  entry-step goal printed as `splat_bytes (...) c 16` does not match the pattern `splat_bytes ?t ?y ?nb`
  ("No matching clauses for match" / "No applicable tactic", scratch/memset.v line 53-54), so the solver
  that works standalone cannot be applied (probably a hidden beta-redex/let from the invariant); (3) the
  post cases (stores of 8/4/2/1/16-byte splats, tbz bit tests on n) were never reached within a run;
  each compile 40 s to several minutes. memcpy/memmove/strlcpy/strncpy/bzero/mempcpy depend on this.
- Build logs now in aarch64/build_logs/ (earlier runs used /tmp/grok_make.log).
- rand_r: psimpl narrows the tempering expression into a large mixed-width term (getmem of 1/3/4 bytes);
  needs a mod-2^32 normalisation lemma set. Parked.
- (done 10:37) toascii.
- (done 11:16, make OK) strncat (0x15f0b4; ids strlen 0, strncat 1) with explicit precondition strncat_pre
  (d string of length Ld; K = min(n, strnlen q) nonzero bytes then K = n or q[K] = 0; all touched bytes
  below sp-48; written range disjoint from read range; justified by C UB for overlapping objects).
  Post: mem = (bcp C (d+Ld) q K)[d+Ld+K := 0], X0 = d, X19-X21/X29/X30/SP restored. ~20 min.
  Proof term large: coqc ~6.5 min.
- done 11:31 wcsncat: proofs/wcsncat_proof.v (wcslen re-proved in wcsncat_prog; new wcpy_read_above/below disjointness lemmas; 4-byte loop invariant at 0x15fd08), Qed, no admits; ~2.5 min coqc.
- done 11:40 wcsncpy: proofs/wcsncpy_proof.v (wmemset re-proved in wcsncpy_prog carrying X19/X29; new wset_read_above lemma; loop invariant at 0x15fd8c, join invariant at 0x15fd9c before the call), Qed, no admits; ~45 s coqc. Imports wcpy_read_above/below from wcsncat_proof.
- NEXT (11:41): awaiting direction;
  strpbrk needs strcspn (unproved);
  memset-dependent ones (strlcpy/strncpy/stpncpy, mempcpy/bzero) wait on memset; strrchr (strlen + tail-call to memrchr; memrchr NEON-vectorised, see below).
- memrchr (0x15e83c) is GCC-auto-vectorised (tbl/zip/cmeq/umaxp on q regs, constants loaded
  from .rodata 0x16ed20..) for n > 14 with 16-aligned end; scalar loop otherwise. Blocks strrchr.
  Option: theorem restricted to the scalar path, or model the NEON ops.
- memset / memcpy / memmove (hand-written asm) — see open problems.

## Open problems / blockers
- **Lifter bug 3 (fixed locally, 04:50): uxtb in `cmp w2,w1,UXTB` dropped** — a narrow p-code read
  (unique,off,1) of a 4-byte temp was emitted as the whole temp; strchr then compared the byte
  with c mod 2^32 instead of c mod 256. See lifter/README_GROK.md item 3. Re-lifting all proved
  functions: only strchr_armv8.v changed. lifted_raw/ refreshed with the fixed lifter.
- **Lifter bug 1 (fixed locally): BOOL_NEGATE lifted as bitwise NOT** — `cset`/`csinv` results
  were 0xfe/0xff instead of 0/1 (e.g. upstream wcscmp lift returns 254 on equal strings).
  Fixed in `aarch64/lifter/` (our copy); upstream `tools/ghidra-lifter` is NOT modified.
- **Lifter bug 2 (fixed locally): LZCOUNT (clz) lifted as width − popcount(x)** — wrong unless
  the set bits are contiguous from bit 0 (64-bit clz(0x8000000000000001) = 0, upstream gives 62).
  Fixed to width − OP_BITWIDTH(x) (N.size). Affects ffs.
- **memset is not soundly lifted**: `mrs x5, dczid_el0` → Nop ("Unmodeled Regs: R_DCZID_EL0")
  and `dc zva` → Nop (CALLOTHER). A full-correctness theorem for memset would be unsound over
  the ZVA path. Plan: either restrict the theorem to inputs that never reach the ZVA path
  (False invariant there; e.g. c mod 256 ≠ 0 or n < threshold) or hand-model `dc zva` as a
  64-byte (per DCZID) zeroing store and `mrs` as `Unknown`.
- memrchr also contains CALLOTHER Nops (not yet examined).
- **Ghidra splits some functions** (e.g. wmemchr: the loop head 0x1601d8 became FUN_001601d8).
  Always check that a lift covers every instruction of the symbol (a False goal after stepping
  means control left the lifted program). Lift `FUN_<addr>` and use that when needed.

## Lessons learned
- Never `pkill -f make...`: the box is shared with other agents; at 06:18 a broad `pkill -f "make -f Makefile.coq"` / `pkill -f "^make$"` was run to restart my build and may have hit another agent's make. Kill only PIDs recorded at launch.
- Header C text: `(wchar_t *)p` contains `*)` and closes the comment (wcsrchr, 06:18); grep headers for `(\*` and `\*)` before assembling.
- Hidden goals at Qed ("remaining open goals", none visible): a callee with several RETs makes destruct_inv after perform_call produce one goal per RET; use `all: destruct ...; [..|..]`, and debug with `Show Existentials`/goal counts (05:38).
- Bit networks (rbit): psimpl turns the lifted mask/shift network into a huge expression and
  rewriting testbit lemmas over it per bit times out (>12 min). Reify it instead
  (GrokBitRefl.reify_bx → bx AST) and decide "bit j = input bit 63-j" by vm_compute
  (brev_check, ~1 s). Reusable for any and-const/or/shift/mod-2^n network.
- **Audit pitfall (found 03:4x):** wcsncmp_proof.v had a helper lemma (wmem_eq_succ) ending in
  `all: admit. Admitted.` although its proof was complete; `make` succeeded and only
  `Print Assumptions` revealed it (listed as an axiom). Fixed to Qed. Always grep for
  `admit|Admitted` and read the whole Assumptions output, not just the first lines.
- eapply of a callee theorem whose extra ∀-parameters (caller's c, x29) are not determined by
  unification leaves shelved evars → `clear -` silently does nothing and Qed fails with
  "proof term is not complete"; use `eapply thm with (c:=c) (x29:=x29)`.
- psimpl writes loaded addresses as `p + 4*k` (no mod) because getmem reduces mod 2^64;
  state nilfree-style predicates with plain `+`, registers with `⊕`.
- Loop counters: bound them (k < 2^62 for 4-byte stride) and wrap k to 0 when the scan has
  covered the whole address space; this keeps the invariant inductive without assuming a
  string length. For length-bounded loops (memchr, wmemchr) carry `n < 2^64` in the invariant.
- `split` closes `x = x` goals; `repeat split; assumption` is often enough after stepping.
- `cbz/cbnz w` branch conditions appear as `negb ((x >> 0) mod 2^32 =? 0) = b`;
  `cbnz32_true/false` in GrokCommon normalise them.
- Word-at-a-time tests: the add of 0xfefe…feff appears as `msub 64 x 0x0101…01`, `~x` as
  `x .^ (2^64-1)`. GrokBits.haszero_test_zero / hasbyte_test_zero turn a zero test into
  "no byte is zero / equals c".
- Ltac closers like `first [ ... ]` over goals whose order after `repeat arm8_step` is hard to
  predict are more robust than bullets.
- `ccmp` is lifted with an internal conditional jump nested as `Seq (Seq (If ..) ..) ..`;
  plain `arm8_step` leaves it unevaluated (goal becomes a stuck `nextinv` with `XS: exec_stmt ...`).
  Use `grok_step`.
- `repeat split` also introduces and splits under `∀ i, i < k -> A /\ B` definitions (e.g. a
  conjunctive mem_eq); use `splits` (only syntactic `/\`) for such specs.
- Spec pitfall: `∃ k, A ∨ B` parses as `∃ k, (A ∨ B)`; parenthesise disjunctions in posts.
- Header pitfall: C code such as `HASZERO(*w)` contains `(*`, which OPENS a nested Coq comment
  ("Unterminated comment"); write `w[0]` instead.
- Header pitfall: C casts such as `(wchar_t *)s` contain `*)` and close the Coq comment;
  tools/finalize.py rejects such headers.
- `cp` is aliased to `cp -i` in the shell; use `command cp -f`.
- Background jobs started with `&` inside a tool call are killed when the call returns; run
  long builds as their own backgrounded call.
- Picinae's own proofs depend on `functional_extensionality_dep`; that is the only axiom
  reported by `Print Assumptions` (not added by us).
