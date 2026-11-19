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
| strcasecmp (+ tolower code) | 0x15ea9c | proofs/strcasecmp_proof.v | strcasecmp_partial_correctness (precondition strcasecmp_pre: two strings below the frame; X0 = msub 32 (tolower l[k]) (tolower r[k]) at the first stop index) |
| strncasecmp (+ tolower code) | 0x15f004 | proofs/strncasecmp_proof.v | strncasecmp_partial_correctness (n = 0 RET: X0 = 0, nothing changed; else precondition strncasecmp_pre, X0 = msub 32 (tolower l[k]) (tolower r[k]) at the first stop index k < n) |
| index (tail call to strchr) | 0x15e124 | proofs/index_proof.v | index_partial_correctness (strchr's invs2/exits2, via lib/GrokTail.v tailcall_satisfies_all) |
| wcsspn (+ wcschr scan loop) | 0x15fe6c | proofs/wcsspn_proof.v | wcsspn_partial_correctness (precondition wcsspn_pre: both wide strings below the 48-byte frame, wcslen(s) < 2^61, accept != NULL; X0 = k, the first index whose wide char is 0 or not in accept), wcsspn_preserves_other_callee_saved |
| wcscspn (+ wcschr, wcslen code) | 0x15fb44 | proofs/wcscspn_proof.v | wcscspn_partial_correctness (precondition wcscspn_pre: both wide strings below the 48-byte frame, wcslen(s) < 2^61, s, reject != NULL; X0 = k, the first index whose wide char is 0 or in the set; empty set: direct tail call to wcslen, memory unchanged), wcscspn_preserves_other_callee_saved |
| wcspbrk (+ wcscspn, wcschr, wcslen code) | 0x15fdf0 | proofs/wcspbrk_proof.v | wcspbrk_partial_correctness (precondition wcspbrk_pre: strings below sp-80; X0 = s+4k if s[k] != 0 (in the set) else NULL; wcscspn re-proved in wcspbrk_prog as wcscspn_in_wcspbrk and composed with perform_call), wcspbrk_preserves_other_callee_saved |
| atoi (lift = FUN_0015cfb0) | 0x15cfa8 | proofs/atoi_proof.v | atoi_partial_correctness (no precondition; X0 = atox_result 32 m s i n: white-space prefix i, optional sign, n digits, musl negative accumulator mod 2^32) |
| atol (lift = FUN_0015d01c) | 0x15d014 | proofs/atol_proof.v | atol_partial_correctness (no precondition; X0 = atox_result 64 m s i n: white-space prefix i, optional sign, n digits, musl negative accumulator mod 2^64) |
| atoll (lift = FUN_0015d088) | 0x15d080 | proofs/atoll_proof.v | atoll_partial_correctness (no precondition; X0 = atox_result 64 m s i n: white-space prefix i, optional sign, n digits, musl negative accumulator mod 2^64) |
| strcat | 0x15eb98 | proofs/strcat_proof.v | strcat_partial_correctness (precondition strcat_pre: strings, frames, non-overlap) |

`make` (in aarch64/) rebuilds all of these; `proofs/Assumptions.v` (last full CLEAN build `make clean; make -j3` 07:11–07:48 CST Nov 16, BUILD_EXIT=0, 70 Print Assumptions covering the 58 functions through remque: 65 report only functional_extensionality_dep, 5 closed. Incremental make 07:53–07:59 BUILD_EXIT=0 with stpcpy/strcpy/wcpcpy: 76 prints, 71 only functional_extensionality_dep, 5 closed. Incremental make 08:00:44–08:04:32 CST BUILD_EXIT=0 with bcmp/wcscat: 80 prints, 75 only functional_extensionality_dep, 5 closed. Latest: incremental make 08:06:14–08:08:41 CST, BUILD_EXIT=0, 84 Print Assumptions covering all 69 functions: 79 report only functional_extensionality_dep, 5 closed; log aarch64/build_logs/make.log. Incremental make with strcat 09:24:58–09:36:15 CST BUILD_EXIT=0. make 10:29:09–10:33:18 CST BUILD_EXIT=0 (85 prints, strcat confirmed). make 10:34:09–10:38:07 CST BUILD_EXIT=0 (86 prints, toascii). make 11:05:28–11:16:00 CST BUILD_EXIT=0 (87 prints, strncat). targeted build 11:26:32–11:31:24 CST (wcsncat, 88 prints). targeted build 11:37:26–11:40:20 CST (wcsncpy, 89 prints). targeted build 12:41:24–12:48:28 CST (strcasecmp, 90 prints). targeted build 12:58:57–13:05:35 CST (strncasecmp, 91 prints). NEWEST: targeted builds 14:40:16–14:50:37 CST (chk.sh proofs/wcscspn_proof.v, ~10 min) and 14:59:46–15:09:51 CST (proofs/wcspbrk_proof.v ~7.6 min, then proofs/Assumptions.v), all exit 0; 100 Print Assumptions covering 80 functions (incl. wcscspn, wcspbrk) plus the GrokTail lemma: 92 report exactly one axiom, functional_extensionality_dep, 8 closed; log aarch64/build_logs/assumptions.log (copy of wcspbrk_build.log). PREVIOUS: targeted build 14:11:05–14:15:49 CST Nov 16 (chk.sh proofs/wcsspn_proof.v ~149 s, then proofs/Assumptions.v, both exit 0; other .vo unchanged), 95 Print Assumptions covering 78 functions (incl. wcsspn) plus the GrokTail lemma: 89 report exactly one axiom, functional_extensionality_dep, 6 closed; log aarch64/build_logs/assumptions.log. PREVIOUS: targeted build 13:11:46–13:13:27 CST (chk.sh lib/GrokTail.v, proofs/index_proof.v, proofs/Assumptions.v, all exit 0; other .vo unchanged), 93 Print Assumptions covering 77 functions (incl. index) plus the GrokTail lemma: 88 report exactly one axiom, functional_extensionality_dep, 5 closed; log aarch64/build_logs/assumptions.log) prints only
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
- done 12:48 strcasecmp: proofs/strcasecmp_proof.v; tolower's code is stepped through symbolically at each of the 4 call sites (invariants at the return addresses 0x15eae0/0x15eaec/0x15eb00/0x15eb0c); lemmas TLF/TLT tie the csel branches to tolower_spec. ~4 min coqc.
- 12:30 target scan (verification-target-finding skill): rand_r (straight-line LCG + tempering) parked-for-now: psimpl rewrites the tempering into a large partially-reduced xor/shift term, proving it equal to a clean temper() spec needs bit-level lemmas (not quick). memrchr is NEON-vectorised (skip for now). index/rindex are single tail branches into the composed strchr/strrchr proofs (needs a trace-suffix composition lemma). Candidates next: strncasecmp (same shape as strcasecmp), wcsspn/wcspbrk (call wcschr).
- BLOCKER 12:30: ./lift.sh now fails with "Corrupt file" (java.io.IOException) on ghidra/musl_aarch64; the project files (gpr, .rep/idata) were re-created 12:19–12:25 CST, not by this session, and the import looks incomplete (db 10 MB). Already-lifted functions are unaffected; new lifts (iswprint, iswcntrl, srand, rand, iswblank) need the project re-imported.
- done 13:05 strncasecmp: proofs/strncasecmp_proof.v (reuses ceq/TLF/TLT/TL32 from strcasecmp_proof; the cmn/ccmp k = n-1 test closed by lia after grok_step), ~5 min coqc.
- 13:07 scan of remaining already-lifted targets: atoi/atol/atoll lifts are truncated (Ghidra function boundary: only 2 instructions), index/rindex/wcswcs are single tail branches (need a trace-suffix composition lemma over satisfies_all), wcspbrk needs unproved wcscspn, strpbrk/strsep need strcspn (calls memset), bsearch/lfind/lsearch call function pointers, strdup/wcsdup call malloc. wcsspn (calls wcschr, which has its own frame and calls wcslen) is feasible but needs wcschr+wcslen re-proved inside wcsspn_prog with X19-X21 carried and strings below both frames.
- done 13:13 lib/GrokTail.v: tailcall_satisfies_all — if Invs/xp depend only on the newest trace element (true of make_invs/make_exits), a0 has no invariant/exit, p s a0 = Jmp a1 for all s, and a target theorem gives satisfies_all for every trace starting at a1 under a store predicate P closed under pointwise equality, then satisfies_all holds for every trace starting at a0 under P. Proof: coinductive nextinv'_retail (nextinv' only sees the trace head) + exec_prog_split + unterminated_untail. Qed, no new axioms.
- done 13:13 index: proofs/index_proof.v (one apply of tailcall_satisfies_all with strchr_partial_correctness), ~1 s coqc.
- rindex (b strrchr) and wcswcs (b wcsstr) wait for their targets: strrchr and wcsstr are not proved yet (strrchr = __memrchr(s, c, strlen(s)+1), memrchr NEON-vectorised; wcsstr is large).
- NEXT (13:14): awaiting direction (wcsspn, or more tail-call wrappers once targets are proved);
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

- (13:18 CST Nov 16) Session stopped for a system shutdown at Garry's request while starting wcsspn (scratch work, if any, is unfinished and unregistered). Resume with wcsspn (calls wcschr -> wcslen; 45-min cap). Ghidra project in aarch64/ghidra reports "Corrupt file" on import since 12:19-12:25 CST; awaiting Garry before re-importing.
- done 14:15 CST Nov 16 wcsspn: proofs/wcsspn_proof.v, Qed, no admits (~149 s coqc), 78 functions. wcsspn_prog = wcsspn + wcschr lifts; wcschr is not re-proved as a callee theorem: since w1 != 0 at the bl, wcschr always takes its scan loop, so a single invariant family (outer head 0x15fe90, wcschr loop head 0x15fae0 carrying wcsspn's X19-X21/frame, X30 = 0x15fea0) covers both, and wcslen is unreachable (the cbnz-false branch is a contradiction). Precondition is read-only: strings below sp-48. Scratch: aarch64/scratch/wcsspn_{base,try,header}.v/.txt.
- done 14:50 CST Nov 16 wcscspn: proofs/wcscspn_proof.v, Qed, no admits (~10 min coqc). wcscspn_prog = wcscspn + wcschr + wcslen lifts (lifted/wcscspn_armv8.v copied from lifted_raw, lifted 12:25; Ghidra not used). One invariant family: entry, general loop 0x15fb70, wcschr loop 0x15fae0 with one disjunct per call site (X30 = 0x15fb80 scanning the set / 0x15fb94 scanning s for c[0] when the set has 1 char), wcslen entry/loop carrying "memory is mem or the frame" (empty set tail-branches to wcslen with no frame). Branch hypotheses are picked by type pattern (`match goal with H: (_ Ⓓ[_] =? 0) = true`), not by BC names, because arm8_step's BC numbering differs per path. Pitfall: inside `all: first [...]`, `match goal` patterns may not mention section variables like `mem` (reference not found); use `_`.
- done 15:10 CST Nov 16 wcspbrk: proofs/wcspbrk_proof.v, Qed, no admits (~7.6 min coqc), 80 functions. wcspbrk_prog = wcspbrk + wcscspn_prog; binvs = wcspbrk points (id 1) + a copy of wcscspn's invariants (id 0), so the same family serves caller and callee for perform_call; wcscspn_in_wcspbrk is the wcscspn proof script re-run over wcspbrk_prog. Strings below sp-80 (both frames); transfer lemmas cspn_ext / winset_ext / nilfree_ext move facts between mem and the frame memories. _CoqProject now also lists lifted/wcsspn_armv8.v, lifted/wcscspn_armv8.v, lifted/wcspbrk_armv8.v (wcsspn's lift was missing from it).
- NEXT (15:14): no quick already-lifted target left in this family; Ghidra project aarch64/ghidra still untouched, awaiting Garry before re-importing. Not yet confirmed by a full `make` (only targeted chk.sh builds since 13:13).
- (16:18 CST Nov 16) Full clean make started 15:16 was stopped for a system shutdown at Garry's request near the end (0 errors in build_logs/make_full_1516.log up to that point). Re-run `make` to finish the confirmation. Ghidra "Corrupt file" diagnosis (did our own 12:19-12:25 lift.sh run cause it?) not finished; aarch64/ghidra still untouched.
- (18:42 CST Nov 16) Resumed after restart. Full clean `make clean; make -j4` started 18:18 (wrapper PID 5368, log aarch64/build_logs/make_full_1818.log); 159 compiles done, 0 errors so far at 18:40; wcscspn/wcspbrk/Assumptions still to finish.
- GHIDRA "Corrupt file" ROOT CAUSE (read-only diagnosis, 18:20-18:40): NOT lift.sh. Garry's git commits of the picinae-llm worktree at 12:19:38 and 12:25:39 (commit 13990bf) ran the repo pre-commit hook (/home/ixb/research/picinae/.git/hooks/pre-commit), which runs `stripwhite` = `sed -i "s/[ ]*$//"` on every staged file, including the binary ghidra/musl_aarch64.rep/idata/00/~00000000.db/db.1.gbf. Removing 0x20 bytes before 0x0a bytes corrupts the Ghidra DB; sed -i also recreated every staged file (birth times 12:25:41-12:25:46 for all of grok-bot, 12:19:40 for the logs). Our headless lift at 12:27:49 (build_logs/lift2.log) was the first to hit "java.io.IOException: Corrupt file". The working-tree gbf equals the committed blob fcc921c (already stripped). Proposed fix (needs Garry's OK): re-import the binary into a fresh project dir (e.g. aarch64/ghidra2, headless analyzeHeadless -import) and keep Ghidra projects out of git commits (gitignore aarch64/ghidra*/ or exclude binaries from the hook). Whitespace-only changes to .v files are harmless (full make confirms).
- GHIDRA GUI INCIDENT: Garry's zsh has `alias find="find 2>/dev/null "` (trailing space => next word is alias-expanded) and `alias ghidra="cd ~/research; ...; pyghidraRun; p2c"`. Our command `find ghidra -maxdepth 3 ...` at ~18:19 therefore launched the Ghidra GUI (application.log: GhidraRun started 18:19:28, opened ~/research/ghidra_projects/mass_lifting). The four GhidraRun starts 15:15:47-15:16:18 most likely had the same cause. RULE: Ghidra headless only (lift.sh uses pyghidraRun --headless; fine). Never type a bare `ghidra` word in the user's zsh; run diagnostics via `bash --norc --noprofile -c` or `command find`. No Ghidra/java process was running at 18:20.
- (19:16 CST Nov 16) FULL CLEAN BUILD CONFIRMED: `make clean; make -j4` 18:18:55-19:14:26 CST, BUILD_EXIT=0, all 171 _CoqProject files compiled, 0 errors (aarch64/build_logs/make_full_1818.log). Audit (aarch64/build_logs/assumptions.log, extracted from that log): 100 Print Assumptions covering all 80 functions plus the GrokTail lemma; 92 report exactly one axiom, FunctionalExtensionality.functional_extensionality_dep (Picinae's), 8 are closed under the global context; no other axioms; no admit/Admitted/Axiom/Parameter in proofs/ or lib/.
- (19:00 CST Nov 16) GHIDRA FIXED (Garry approved): grok-bot/.gitignore created with `aarch64/ghidra*/` (git check-ignore matches aarch64/ghidra/ and aarch64/ghidra2/; NOTE the 9 files of aarch64/ghidra/ are already tracked by commit 13990bf, so .gitignore does not untrack them; nothing was git rm-ed or committed). Fresh headless import (pyghidraRun --headless ... -import ld-musl-aarch64.so.1, sha256 4723e4ca... = sha256sums) into aarch64/ghidra2 18:56:17-18:57:55, IMPORT_EXIT=0, log build_logs/ghidra2_import.log. lift.sh now uses "${GHIDRA_PROJ:-$here/ghidra2}" (backup scratch/lift.sh.bak_1856). Test re-lift of wcslen into scratch/relift_1858/ is byte-identical to lifted_raw/wcslen_armv8.v and lifted/wcslen_armv8.v. aarch64/ghidra (corrupt) left untouched. Lifting is unblocked.
- done 19:37 CST Nov 16 atoi, atol, atoll: proofs/{atoi,atol,atoll}_proof.v, Qed, no admits (~95 s / ~4.5 min / ~4.5 min coqc), 83 functions. Re-lifted headless from aarch64/ghidra2: the symbols lift truncated (2 instructions) because Ghidra splits each function at the white-space loop head, so lifted/<fn>_armv8.v is the lift of FUN_0015cfb0 / FUN_0015d01c / FUN_0015d088 (raw copies in lifted_raw/FUN_*_armv8.v) with the definition renamed; each contains all instructions of the function. New library lib/GrokAtoi.v (is_ws/is_dig, ws_run/dig_run, acc = musl's negative accumulator n = 10n - d mod 2^w, sgn_len, atox_result, ccmp/ls branch lemmas ws_bc/dig_bc, acc_step32 and acc_step64sx for the SXTW form). Post: ∃ i n, s[0..i) white space, s[i] not; q = s+i+sgn_len(s[i]); q[0..n) digits, q[n] not; X0 = acc(n) if s[i]='-' else 0-acc(n) mod 2^w. One proof script serves all three (generated from scratch/atox_template.v). Registered in _CoqProject (lib, lifted, proofs) and proofs/Assumptions.v (partial_correctness + preserves_callee_saved each).
- PARKED 19:40 strcspn (timebox: not quick). Lift (lifted_raw/strcspn_armv8.v, ghidra2 re-lift identical) calls strchrnul (0x15ebf4, which itself calls strlen 0x15efa8 when c==0) for sets of length 0/1, and memset (0x118400, n=32, c=0) to clear a 32-byte bitset at sp+0x30 for longer sets; then two loops set/test bits (ubfx x2,x1,#6,#2; lsl; ldr/orr/str [x5,x2]). Needs: strcspn_prog = strcspn+strchrnul+strlen+memset; three-level call nesting; memset's n=32 path (q-register 128-bit stores of 0 at x0, x0+16, x4-16, x4-32) stepped concretely; a bitset invariant "bit b of the 4 words at sp+0x30 is set iff b ∈ c[0..j)" with 64-bit word read/OR/write lemmas; strings below the frame. Estimate 2-4 h. Option: first prove a restricted theorem (set length >= 2, False invariant at the strchrnul call) to avoid the nested callee. strpbrk/strsep are thin wrappers once a strcspn theorem with an X19/X29-carrying callee form exists.
- (19:47 CST Nov 16) Incremental `make -j4` 19:37:48-19:46:13 CST (PID 19715), BUILD_EXIT=0, log aarch64/build_logs/make_1938.log (atol/atoll/GrokAtoi .vo were already built by chk.sh with the final sources). Audit aarch64/build_logs/assumptions.log: 106 Print Assumptions covering 83 functions plus the GrokTail lemma; 95 report exactly one axiom, functional_extensionality_dep (Picinae's), 11 closed; no other axioms. New: atoi/atol/atoll_partial_correctness -> functional_extensionality_dep only; *_preserves_callee_saved -> closed. No admit/Admitted/Axiom/Parameter in the new files. NEXT: strcspn (parked note above), then strpbrk/strsep.

### 2026-11-16 20:18 CST — leaf batches 1 and 2 (Grok Bot)
- Generator: `tools/gen_leaf.py` + `tools/leaf_template.v` (spec table → lifted invariants + standard theorem set). Helpers in `lib/GrokLeaf.v` (lnot32_sign, bit_not, bit_eqb0, negb_eq, grok_leaf_close) and `lib/GrokLeaf2.v` (hi_flag for cmp+b.hi, grok_leaf_close2).
- Batch 1 (41, Qed): __fbufsize dirfd telldir aio_return sigisemptyset sigandset sigorset cfgetospeed cfgetispeed pthread_attr_get{detachstate,guardsize,inheritsched,schedparam,schedpolicy,stacksize,scope} pthread_rwlockattr_getpshared posix_spawnattr_get{pgroup,flags} pthread_attr_setschedpolicy posix_spawnattr_setpgroup pthread_attr_setschedparam posix_spawn_file_actions_init pthread_{barrierattr,condattr,mutexattr,rwlockattr}_init pthread_spin_init pthread_condattr_get{clock,pshared} pthread_mutexattr_get{protocol,pshared,robust,type} sem_getvalue pthread_barrierattr_getpshared __fseterr __freadptrinc __flbf __freadable __fwritable.
- Batch 2 (12, Qed): mbsinit __freadahead __fpending __freading __fwriting pthread_attr_setdetachstate pthread_attr_setinheritsched pthread_rwlockattr_setpshared pthread_attr_setguardsize cnd_init pthread_mutex_init pthread_attr_getstack.
- Audit (make_2017, all registered incl. batch 2): 159 Print Assumptions = 11 "Closed" + 148 functional_extensionality_dep only. Clean build 20:24 CST.
- Lesson: an early audit showed GrokLeaf lemmas as axioms because I recompiled lib/GrokLeaf.v while `make` was running; never rebuild a lib during a make. Also `rewrite ?(N.add_comm _ _) in *` loops forever — removed.
- Next-round candidates: pthread_mutexattr_settype/setpshared, pthread_condattr_setpshared/setclock, pthread_barrierattr_setpshared, pthread_attr_setscope/setstacksize/setstack, posix_spawnattr_setflags, pthread_setconcurrency, pthread_getcpuclockid, mtx_init, pthread_barrier_init, pthread_cond_init, __freadptr, cfmakeraw, srand, inet_netof/lnaof/makeaddr, constant stubs (__libc_current_sigrtmax/min etc.), l64a, __sched_cpucount (loop). Parked: strcspn, rand_r.

### 2026-11-16 20:45 CST — sanity check and leaf batch 3 (Grok Bot)
- Sanity check of batch 1/2 (sample: pthread_attr_getguardsize, pthread_attr_setguardsize, posix_spawn_file_actions_init, sigandset, __fwritable, pthread_attr_getstack, pthread_mutex_init): each post gives the exact X0 and the exact memory (only register-equality preconditions, so none vacuous); offsets/constants checked against musl source. Script /tmp/grok_retchk.py confirmed for all 53 generated proofs that the Post invariant sits on every `ret` of the lift and there are no other exits (indirect jumps or branches out). Fixed: generic C text "(... *a, int v)" in the headers of the 4 bounds-checked setters (comment-only; the specs were already right).
- GrokLeaf2.grok_leaf_close2 fix: it cleared the branch hypothesis after the first case split, so nested `if` conditions were lost; now only trivial `x = x` hypotheses are cleared.
- Batch 3 (12, Qed): pthread_mutexattr_settype pthread_mutexattr_setpshared pthread_condattr_setpshared pthread_barrierattr_setpshared pthread_getcpuclockid mtx_init __libc_current_sigrtmax __libc_current_sigrtmin pthread_attr_setstacksize pthread_attr_setstack pthread_attr_setscope __freadptr. New lifts from ghidra2 (headless) in scratch/lift_b3.
  - pthread_getcpuclockid's stored value is stated as the binary computes it (6 + (29-bit complement of tid) << 3, truncated by the 32-bit store); the stack setters state the bounds test as the binary does (size = 2048 + SIZE_MAX/4, or SIZE_MAX/4 not <= (size-2048) mod 2^64).
- Also Qed (20:46): inet_lnaof, inet_netof, with the class-A test stated as the binary does it (bit 31 of the address clear, equivalent to h>>24 < 128) and class B as top byte <= 191.
- PARKED (first spec attempt failed, needs bit lemmas): inet_makeaddr (needs `(b .| x) mod 2^32` distribution), pthread_cond_init (psimpl drops the overwritten `[Ⓠ a := 0]` and uses `>> 31 =? 0`), pthread_barrier_init (signed `slt 32` flag). Drafts in scratch/b3.
- Not attempted yet (lifted in scratch/lift_b3): posix_spawnattr_setflags (sxth), pthread_condattr_setclock (ccmp).
- Audit (make_2055, 21:01 CST, all registered incl. batch 3 + inet pair): 173 Print Assumptions = 11 "Closed" + 162 functional_extensionality_dep only; BUILD_EXIT=0. /tmp/grok_retchk.py: all 67 generated leaf proofs have Post on every ret and no other exits.

### 2026-11-16 21:22 CST — leaf batch 4 + parked trio (Grok Bot)
- Qed (29): stubs setutent setutxent endutent endutxent sethostent setnetent endhostent endnetent setservent endservent setspent endspent (ret-only: the Post invariant sits on the entry, which is the RET), gethostent getnetent getservent getspent getutent getutxent (return 0), ether_hostton ether_line (return -1 as W0), endprotoent setprotoent (clear static idx at Ghidra 0x1c2ed4), srand (seed at 0x1c2598 := msub 32 s 1), cfmakeraw, posix_spawnattr_setflags, pthread_condattr_setclock, and the previously parked inet_makeaddr, pthread_cond_init, pthread_barrier_init.
  - Alias pairs share one address (endhostent/endnetent etc.); the alias lift is the same Ghidra output with the definition renamed (lifted_raw keeps the original).
- GrokLeaf2 additions: msub_0_mod, mod_mod_pow2, scast_mod, le0_flag, grok_leaf_close3 (case-splits branch conditions in hypotheses; uses cbv on N.lor/negb/N.eqb only — an earlier vm_compute version ran a compile out of memory on posix_spawnattr_setflags; compiles now run under `ulimit -v 8000000`).
- Specs stated in the binary's own test form where noted in each header (pthread_condattr_setclock: clk-2 below 1 or clk = 3; inet_makeaddr branch shapes; pthread_cond_init writes -1 over the zeroed first word).
- /tmp/grok_retchk.py: 96 generated leaf proofs, Post on every ret, no other exits.
- Not done: l64a (loop writing a static buffer), __sched_cpucount (nested popcount loop) — both need loop invariants, lifted in scratch/lift_b4. Restricted strcspn not started.
- Audit (make_2121, 21:32 CST, BUILD_EXIT=0): 202 Print Assumptions = 11 Closed + 191 functional_extensionality_dep only.

### 2026-11-16 ~21:55 CST — rand, loops, missed stubs (Grok Bot)
- Qed: rand (seed at Ghidra 0x1c2598 := (1 + seed*6364136223846793005) mod 2^64, returns new seed >> 33).
- Qed: __sched_cpucount (nested loop; invariants at 0x150f04 outer / 0x150f14 inner; result = cpucnt mem set size mod 2^64, cpucnt = Fixpoint sum of per-byte bit counts) — about 5 min.
- Qed: l64a (loop at 0x13b170; memory = l64w mem x i, then s[i] := 0, with i the digit count; digit table read from memory; lemma l64w_digit shows the stores at 0x1c2348.. never touch the table at 0x19dab0..+63). First attempt OOM-killed under the 8 GB cap: `simpl l64w` unfolded getmem — use `cbn [l64w]`.
- Scan of exported functions <= 80 bytes with no calls/SIMD/FP not yet proved found 59; proved 46 of them (generator, Qed): no-op stubs __cxa_finalize _dl_debug_state cnd_destroy mtx_destroy updwtmp updwtmpx; constant returns __fsetlocking ether_ntohost gethostid getnetbyaddr getnetbyname getutid getutxid getutline getutxline pututline pututxline grantpt lckpwdf ulckpwdf res_init sem_destroy posix_spawnattr_destroy posix_spawnattr_{get,set}sched{param,policy} (ENOSYS) pthread_{attr,barrierattr,condattr,mutexattr,rwlockattr}_destroy pthread_rwlock_destroy pthread_spin_destroy pthread_getconcurrency pthread_mutex_{get,set}prioceiling pthread_mutexattr_setprioceiling (EINVAL); address returns __ctype_b_loc __ctype_tolower_loc __ctype_toupper_loc __res_state localeconv; globals getpagesize issetugid; pthread_setconcurrency.
- Left from the scan: _init _fini (ret-only ELF hooks, not C functions), creal crealf creall nanl __signbitl conjl (FP/SIMD registers), __stack_chk_fail (brk), iswcntrl iswpunct iswalpha (range checks / table lookups, small), rand_r (parked).
- strcspn (restricted, set length >= 2): not attempted. That path calls memset(byteset, 0, 32), and memset is the SIMD assembly version (dup v0 + q stores) parked at 10:30; it would need memset's n=32 path proved first.
- iswcntrl: lifted (aarch64/lifted_raw/iswcntrl_armv8.v; scratch/b7 has the debug proof), parked after one look: the ccmp chains leave flag terms like ((if 31 <=? x then 0 else 1) .| (if x =? 31 then 1 else 0)) and (if x =? 159 ... msub 32 a 127 ...) .^ 1; needs small lemmas relating them to the C range tests.
- 22:01 make_b6 BUILD_EXIT=0; audit: 251 Print Assumptions = 11 Closed + 240 with only FunctionalExtensionality.functional_extensionality_dep; no other axioms, no admits.
- ~22:38 isw*/memset round: iswcntrl PROVED (spec: 1 iff a mod 2^32 < 32 or msub 32 a 127 < 33 or msub 32 a 8232 < 2 or msub 32 a 65529 < 3, else 0). New lib/GrokRange.v: msub32_cases (msub 32 a k as a case on a mod 2^32) + grok_range_close (revert flag hyps, rewrite msubs, generalize x, case-split comparisons pruning each branch with lia). Unpruned case split took 190 s on one goal; with lia pruning the whole proof is ~3.5 min. iswpunct/iswalpha lifted to scratch/lift_b8 (bitmap table lookups, need a table spec), not proved. memset (restricted) and strcspn not attempted this round (out of time); note memset n <= 96 never reaches dczid_el0/dc zva (the cmp x2,#0x60 / b.hi at 0x18408 branches away first), so the old scratch/memset.v restriction n <= 96 is the right precondition.
- 22:39 make_b8 BUILD_EXIT=0; audit 252 Print Assumptions = 11 Closed + 241 functional_extensionality_dep only.
  Count: 227 distinct proved function symbols (227 partial-correctness theorems), at 218 distinct code addresses (9 symbols share code with another).
- ~23:12 table/memset round: iswpunct and iswalpha PROVED (spec reads both bitmap bytes from memory at the table, Ghidra 0x173140 / 0x1721b0, like l64a reads its digit table; new GrokRange lemmas tab_addr, byte_ashiftr and tactic grok_tab_close). make_b9 BUILD_EXIT=0 (END 22:59:57); audit 254 Print Assumptions = 11 Closed + 243 functional_extensionality_dep only. Count: 229 distinct proved function symbols, 220 distinct code addresses.
- memset n <= 96 (scratch/b10/memset_try.v, NOT registered, has Admitted): the dup/splat step is now solved (solve_splat c (s1 R_Z0) right after arm8_step at 0x118400; reify + vm_compute take < 0.1 s; old blocker (2) was just not passing z). Preconditions added: 4096 <= d (page 0 never mapped, so d - k never wraps) and d + n < 2^64. Remaining blocker: symbolic execution of the n <= 96 paths after the 0x118404 invariant grows ~2x per step (8 steps = 4 s; full run plus rd1 byte reads did not finish in 9 min). Next: add invariants at the branch targets 0x118418, 0x118430, 0x118440, 0x118454, 0x118470 (each carrying ZS and the n range) so each path is a few steps, then close posts with memset_addr/rd1/memset_byte. Note: coqc output to a file is buffered, so idtac markers are lost on timeout; use Timeout per tactic instead.
- strcspn: not attempted (waits on memset).
- ~23:37 memset n <= 96 PROVED (proofs/memset_proof.v; preconditions n <= 96, 4096 <= d, d + n < 2^64, soundness argument in the header). Fix that worked: invariants at every branch target (0x118418, 0x118430, 0x118440, 0x118454, 0x118470) plus `Inv 0 False` at 0x118480 to cut the n > 96 path (the dczid/dc zva Nop region is never entered); splat via solve_splat right after the dup; posts closed by memset_prep/memset_addr/rd1/memset_byte. Partial correctness ~3 min; the frame theorems over the whole program ~4.5 min. make_b10 BUILD_EXIT=0 (END 23:36:30); audit 255 Print Assumptions = 11 Closed + 244 functional_extensionality_dep only. Count: 230 distinct proved function symbols, 221 distinct code addresses.
- Not done after memset: strcspn (strchrnul + memset callees, bitset loops), strlcpy (strlen + loops), stpncpy (loops + memset tail), strncpy (calls stpncpy), mempcpy (calls memcpy, SIMD), bzero (mov, mov, b memset: needs a small "prefix then tail call" variant of tailcall_satisfies_all; GrokTail only handles a lone b).
- ~23:49 bzero + FP round: lib/GrokTail.v gains step_satisfies_all (one instruction at a0 that always continues to a1, then anything proved from a1; same trace surgery as tailcall_satisfies_all with STMT/STEP hypotheses) and reset_move. bzero PROVED by chaining step (mov x2,x1) + step (mov w1,#0) + tailcall (b memset) onto memset_partial_correctness (same n <= 96 / 4096 <= d / d+n < 2^64 preconditions); compiles in ~1 s.
  FP/SIMD: Picinae models v-registers as 256-bit R_Z0..R_Z31, so all six were stateable. PROVED: creal, crealf, creall (lone RET: R_Z0 unchanged = real part returned), nanl (X0 = 0x16e320, R_Z0 = mem Ⓧ[0x16e320]), __signbitl (X0 = bit 127 of Z0 as ((Z0>>64) mod 2^64) >> 63; memory gets q0 at sp-16), conjl (R_Z1 = (b mod 2^64 .| ((b>>64) .^ 2^63) << 64) mod 2^128, R_Z0 unchanged; stack writes stated). __signbitl/conjl use preserves_other_callee_saved (SP is moved and restored; restoration is in the post).
  make_b11 BUILD_EXIT=0 (END 23:49:08); audit 263 Print Assumptions = 11 Closed + 252 functional_extensionality_dep only. Count: 237 distinct proved function symbols, 228 distinct code addresses.
- stpncpy: assessed, not attempted: three loops including a word-at-a-time copy with the (x - 0x0101..) & ~x & 0x8080.. zero-byte test, its own frame (x19, x29, x30) and a bl memset; needs a has-zero-byte lemma and caller+callee invariants; estimate 2+ hours. strncpy waits on it.
- (00:15 CST Nov 17) WIDENED SCAN round (instruction 23:49). Scan of all exported symbols (/tmp/grok_scan2.py) for (a) wrappers/tail-callers onto proved callees and (b) short single-loop leaf functions. Candidates and effort estimates:
  - DONE: 45 single-`b` tail wrappers (all *_l / __*_l ctype + strcasecmp/strncasecmp/tolower/toupper locale variants, strcoll_l/__strcoll_l -> strcmp, wcscoll_l/__wcscoll_l -> wcscmp, iswblank -> isblank). Generated by new tools/gen_tail.py <outdir> <list> (list format `name 0xaddr callee`), proofs reuse the callee partial_correctness via GrokTail.tailcall_satisfies_all. make_b12 BUILD_EXIT=0.
  - DONE: ispunct (bl isalnum; caller+callee pattern like strnlen, program updateall2, callee id 0, perform_call; ~10 min). make_b13 BUILD_EXIT=0.
  - DONE: iswalnum (bl iswalpha; same pattern; table bytes read from frame_mem, spec states it via iswalpha_val frame_mem; ~15 min). Registered, make_b14 BUILD_EXIT=0 (00:21:56).
  - OPEN: ctermid (cbz, else tail `b strcpy` with buffer 0x19f980; ~30-45 min, needs strcpy re-verified inside composed prog + branch), explicit_bzero (bl memset with frame; ~40 min, needs n<=96/4096<=d preconditions + no overlap of d..d+n with sp-16..sp-1; memset composition compiles ~8 min), iswspace (bl wcschr, ~45 min), wcpncpy (wcsncpy+wcsnlen, 1h+), dn_skipname (104 B one loop, ~45 min), setvbuf/memccpy (1h+), strlcpy (loop + strlen, 45 min fallback).
  - BLOCKED: posix_spawnattr_init (memset n=336 > 96 -> dc zva path not covered by memset proof).
  - Audit after make_b14: 312 Print Assumptions = 11 "Closed under the global context" + 301 functional_extensionality_dep only (build_logs/assumptions.log).
  - Count (registered proofs/*_proof.v): 284 distinct symbols / 253 distinct addresses.
  - Lifts this round (headless lift.sh, ghidra2): ispunct, iswalnum, ctermid, explicit_bzero in lifted/ and lifted_raw/ (ctermid/explicit_bzero lifted but not yet registered/proved).
- (00:55 CST Nov 17) Round "ctermid, explicit_bzero, iswspace, dn_skipname, strlcpy" (timeboxes = estimates + 25%).
  - DONE ctermid (~30 min): two theorems. ctermid_null_partial_correctness (s = NULL: X0 = 0x19f980 = "/dev/tty" literal in .rodata, memory unchanged) and ctermid_partial_correctness (s <> NULL: satisfies exactly strcpy_proof invs1/exits1 for strcpy(s, 0x19f980)). The cbz/adrp/add prefix is peeled with GrokTail.step_satisfies_all (statement-level inversion lemmas cbz_nz, add_x1, step_models in the proof file), the branch with tailcall_satisfies_all. NOTE: add_x1 takes ~4 min (cbn over the flag updates). make_b15 BUILD_EXIT=0 (00:51). Header lesson again: never write "(name_*)" in a header, the "*)" closes the comment.
  - Audit after make_b15: 314 Print Assumptions = 11 Closed + 303 functional_extensionality_dep only. Count: 285 symbols / 254 addresses.
  - DONE (standalone check 00:59, registered, make_b16 running) explicit_bzero: composed program eb_prog = explicit_bzero + memset, family invs = caller (id 1) + memset_proof.invs frame_mem d c n (sp-16) 0x15e11c (id 0) with c a family parameter (solve_splat cannot reify the literal 0); callee part re-runs the memset proof script verbatim (checks, ~8 min); caller part needs S2X2/S2X1 rewrites after perform_call. Full file scratch/b16/eb_full.v, header scratch/b16/eb_hdr.txt.
  - Next: iswspace (bl wcschr with table at 0x1740e0, needs wcschr re-verified in composed prog), dn_skipname (0x3ff00-0x3ff64, one loop, leaf), strlcpy.
- (01:30 CST Nov 17) Round "iswspace, dn_skipname, strlcpy" (55 min each).
  - make_b16 BUILD_EXIT=0 (END 01:15:43): explicit_bzero DONE. Audit 316 Print Assumptions = 11 Closed + 305 functional_extensionality_dep only. Count 286 symbols / 255 addresses.
  - DONE iswspace: composed program updateall2 iswspace wcschr (wcslen not needed: the c = 0 path returns before it). Post: c mod 2^32 = 0 -> X0 = c (0); else exists r, wcschr_spec frame_mem 0x1740e0 (c mod 2^32) r and X0 = (r =? 0 ? 0 : 1). spaces[] table at ELF 0x740e0. wcschr re-verified in the family (wcschr_correct_in_iswspace).
  - DONE dn_skipname: leaf loop; inductive dn_walk (label-length walk) + dn_res (end, zero byte, compression pointer >= 192, overrun); preconditions s <= e and e - s < 2^63.
  - make_b17 FAILED only on a header lexer error: "(*p>=192)" in the C sketch opens a nested comment. Fixed to "( *p>=192)". Lesson: grep headers for "(\*" as well as "\*)".
  - make_b18 BUILD_EXIT=0 (END 01:25:40). Audit 319 Print Assumptions = 11 Closed + 308 functional_extensionality_dep only (build_logs/assumptions.log). Count: 288 distinct proved symbols / 257 distinct code addresses.
  - IN PROGRESS strlcpy (box until ~02:11): plan in aarch64/scratch/b19/strlcpy_plan.txt. Three loops (aligned byte loop, K8 word loop, bounded byte loop) + bl strlen; reuse GrokStr bcp/bnz/bnz_word/bcp_word8. Snag: after a zero byte is copied at 0x5ef30 the code re-reads src[k] from the updated memory (0x5ef34), so invariants must carry "mem = bcp k or (mem = bcp (k+1) and src byte k = 0)". Estimate 1.5-2 h, likely to be parked.
- (02:04 CST Nov 17) strlcpy checkpoint (2 h box until ~03:30). Spec uses a no-overlap precondition (src [q, q+L] vs dst [d, d+n), C UB) plus: src string of length L and frame below sp-32, d+n+32 <= sp, q+n < 2^64; ghost K = min(L, n-1). Post: X0 = L, memory = (n = 0 ? frame : bcp frame d q K with byte d+K := 0), callee-saved restored. Composed program strlcpy + strlen; strlen_correct_in_strlcpy CHECKS. Main theorem (scratch/b19/slc_p2.v, Admitted pieces only in scratch): entry, bounded byte loop 0x15eef0, alignment loop 0x15ef1c, junction 0x15ef34 PROVED; 0x15ef88 nearly; remaining: word loop 0x15ef64 and the strlen call/return at 0x15ef90 (drafted). Compile of the main file ~5 min.

### 2026-11-17 09:40 CST — session: finish strlcpy, then stpncpy/memccpy (Grok Bot)
- (10:16) strlcpy: the 02:54 run of scratch/b19/slc_p2.v had only the post-call goal left (GOAL7: X0 = (L-k)+k mod 2^64, X19/X29/X30 reloaded from the frame via FQ/Q16/Q32/Q24); closed in focused file slc_p3.v (other cases admitted, 40 s). Full file slc_p4.v then ran OUT OF MEMORY (8 GB cap) in the word-loop case at `splits; clo` (and earlier at a bare `lia`). Cause: clo tried `reflexivity` before `assumption` (unifying `s1 R_X29` with `sp ⊖ 32` unfolds the whole store chain: 10-25 s per goal) and `lia` over the full context (bcp/getmem atoms, ∀-hyps). Fix: new `clean` (clears getmem/bcp/setmem/∀/nilfree/models/exec_prog/store-equation hyps) + `llia := clean; lia`, closer `clo2`, and `assumption` before `reflexivity`. Tools: scratch/b19/focus.py (keep one destruct_inv case, admit the rest) and mchk.py (compile + max RSS + seconds).
- (11:21) strlcpy PROVED (scratch): the one-theorem script OOMs at the 8 GB cap even with clo2 (peak 7.45 GB); a second culprit was `assumption`/`reflexivity` in clo2 unifying store terms (now `sassumption | sreflexivity`, GrokCommon). Each destruct_inv case became its own lemma `slc_case_<addr>` stated over the post-step goal (`invs ... s1 <addr>` -> `nextinv strlcpy_prog (invs1 ...) (exits1 ...) false ((Addr <addr>, s1) :: t)`, hnf in PRE); the main theorem dispatches with `eapply slc_case_<addr>; eassumption`. All 7 case lemmas compile in separate coqc runs (max 4.56 GB, the word loop 0x15ef64); dispatcher 0.6 GB / 15 s; Print Assumptions = functional_extensionality_dep only. Ilan asked (t2u) for a measured write-up: grok-bot/VCEffectsOnMemOverhead.md (experiment files in aarch64/scratch/vcmem/, driver run_all.sh + sequential replicate run_rep2.sh, sampler mchk2.py).
  - Final layout drafted (not yet compiled/registered): proofs/strlcpy_callees.v (prog, slc_pre/slc_frame/slc_mem, invariant family, strlen_correct_in_strlcpy, shared tactics), proofs/strlcpy_vcs_small.v (0x15eec4, 0x15eef0, 0x15ef88, 0x15ef90), proofs/strlcpy_vcs_loops.v (0x15ef1c, 0x15ef34), proofs/strlcpy_vcs_word.v (0x15ef64), proofs/strlcpy_proof.v (full header, strlcpy_partial_correctness, strlcpy_preserves_other_callee_saved). Generated by scratch/b19/assemble2.py.
  - memccpy: the 10:30-Nov-16 "variable k not found" blocker was an artifact: GrokCommon.dump_ctx REVERTS the context, and it was called before the tactics that then failed. Removed; split into case lemmas (scratch/b20/mcc.v). The word-loop lemma alone ran 44 min without finishing under the old closers (assumption/reflexivity/lia on full context) and was stopped; next: apply sassumption/sreflexivity/llia there.
- (11:32) WROTE grok-bot/VCEffectsOnMemOverhead.md (Ilan's t2u). Headline: per-VC lemmas in ONE file do not lower peak RSS (mono 7453 MB OOM vs deco 7366 MB OOM, the OCaml heap is not returned after Qed); `Optimize Heap.` after each lemma -> 6235 MB, Qed; one file per lemma -> max 4564 MB (0x15ef64), dispatcher 598 MB; summed per-process peaks 11.5 GB (each process reloads ~444 MB). Lesson: for heavy Picinae proofs, put VC lemmas in separate files (or at least `Optimize Heap.` between them); the floor is the largest single case, so tactic cost still matters.
  - Replicate 2 (sequential, scratch/vcmem/run_rep2.sh -> rep2.out) still running at 11:32; append its numbers to the write-up when done (mono rep2 already: OOM 7457 MB, 333.6 s).
  - NEXT: compile + register the strlcpy final layout (proofs/strlcpy_callees.v, strlcpy_vcs_{small,loops,word}.v, strlcpy_proof.v; _CoqProject also needs lifted/strlcpy_armv8.v; Assumptions.v), `make` + `make assumptions`; then memccpy with the new closers (scratch/b20/mcc.v), then stpncpy (same shape as strlcpy, memset tail needs X19 carried in memset's invariants), strncpy, strcspn.
- (11:35 CST Nov 17) CHECKPOINT — stopped for system shutdown (Ilan, t3u). Killed only my own processes: run_rep2.sh driver, mchk2 runs of rep2/deco_opt.v, proofs/strlcpy_vcs_loops.v, proofs/strlcpy_vcs_word.v, scratch/b20/mcc2_w.v (+ their rocqworkers). No coqc/make of ours left running. Nothing committed.
  - strlcpy final files (generated by scratch/b19/assemble2.py from scratch/vcmem/deco.v): proofs/strlcpy_callees.v COMPILED (Qed, 921 MB, 80 s); proofs/strlcpy_vcs_small.v COMPILED (1206 MB, 233 s, with Optimize Heap between lemmas); proofs/strlcpy_vcs_loops.v and proofs/strlcpy_vcs_word.v were KILLED mid-compile (no .vo); proofs/strlcpy_proof.v not compiled (needs the two). The same lemma bodies already Qed in scratch (vcmem/deco_L_*.v), and the dispatcher + Print Assumptions (functional_extensionality_dep only) checked in scratch/vcmem/deco_main.v. NOT yet registered: add to _CoqProject `lifted/strlcpy_armv8.v proofs/strlcpy_callees.v proofs/strlcpy_vcs_small.v proofs/strlcpy_vcs_loops.v proofs/strlcpy_vcs_word.v proofs/strlcpy_proof.v`, and to proofs/Assumptions.v (`From Grok.proofs Require strlcpy_proof.` + Print Assumptions for strlcpy_partial_correctness, strlen_correct_in_strlcpy, strlcpy_preserves_other_callee_saved); then make + make assumptions. Compile logs: build_logs/strlcpy_final/.
  - VCEffectsOnMemOverhead.md: written; replicate-2 partial results added (mono OOM 7457 MB / 333.6 s, deco OOM 6803 MB / 398.2 s); rep2 remainder not run (can be re-run with scratch/vcmem/run_rep2.sh, ~1 h, ideally on an idle machine).
  - memccpy: scratch/b20/mcc2.v = case lemmas + cheap closers (clean/llia, sassumption/sreflexivity, modeq via llia). Word-loop lemma (mcc2_w.v) got past all closers except one: `rewrite msub_small by llia. reflexivity.` after `splits` hit "No such goal" (llia already closed it) — now wrapped as `all: try (...)` in mcc2.v/mcc2_w.v; that retry was killed before finishing. Branch goals/BC forms printed in scratch/b20/mcc_d.v (BC: `k ⊖ k0 ≠ n - k0 .& 18446744073709551608`). NEXT: compile mcc2_w.v, then the other 3 lemmas + dispatcher (split into files if memory is high), header headers/memccpy.txt, register.
  - Then: stpncpy (same shape as strlcpy; memset tail call needs X19 added to a copy of memset's invariants, n-K <= 96, 4096 <= d+K), strncpy (wraps stpncpy), strcspn (memset n=32 + strchrnul).

### 2026-11-17 13:12 CST — afternoon: strlcpy registered, memccpy proved (Grok Bot)
- System came back clean after the shutdown (12:14 boot; no stale coqc/make of ours).
- DONE strlcpy (0x15eec4): proofs/strlcpy_callees.v (921 MB/80 s), strlcpy_vcs_small.v (1206 MB/233 s), strlcpy_vcs_loops.v (4201 MB/345 s), strlcpy_vcs_word.v (3378 MB/730 s), strlcpy_proof.v (1120 MB/122 s) all Qed. Theorems: strlcpy_partial_correctness, strlen_correct_in_strlcpy, slc_case_<addr> (7 VC lemmas), strlcpy_preserves_other_callee_saved. Registered in _CoqProject (lifted/strlcpy_armv8.v + 5 proof files) and proofs/Assumptions.v (3 Print Assumptions).
- make_b20 (13:00:54-13:07:54) BUILD_EXIT=0, log build_logs/make_b20.log (copied to build_logs/assumptions.log): 322 Print Assumptions = 12 Closed + 310 functional_extensionality_dep only; no other axiom names.
- memccpy (0x15e128) PROVED in scratch/b20/mcc2.v (2417 MB, 530 s, Qed): case lemmas mcc_case_<addr>; word-loop step fixed by (1) removing dump_ctx (it reverts the context), (2) targeted closers instead of a generic `first [...]` (the old `lia`/`replace ... by lia` alternatives on the full context ran >120 s per goal), (3) new lemma hasbyte_none2: psimpl drops the `mod 2^64` on (w^k)+K8 inside the land with H8, so hasbyte_none's hypothesis did not match. Small cases kept their original (assumption/reflexivity) closers. Final file proofs/memccpy_proof.v (header headers/memccpy.txt; spec over bcp/bnc, no precondition; frames nwc/preserves_callee_saved/preserves_x30) compiling at 13:12; then register + make.
- NEXT: register memccpy; stpncpy (0x15e9c0, strlcpy-shape + bl memset tail; memset invariants need X19), strncpy, strcspn.

### 2026-11-17 13:48 CST — memccpy registered; stpncpy VCs mostly proved (Grok Bot)
- memccpy_proof.v compiled (530.6 s, peak RSS 2608 MB; logs in aarch64/build_logs/memccpy/).
  Registered: _CoqProject += lifted/memccpy_armv8.v, proofs/memccpy_proof.v; Assumptions.v
  prints memccpy_partial_correctness / memccpy_preserves_callee_saved / memccpy_preserves_x30.
- _CoqProject was missing lib/GrokFill.v (used by memset/explicit_bzero); added, plus new
  lib/GrokMem.v (getmem_ext: multi-byte read depends only on its bytes; bcp_read_in).
  make_b21 (make + make assumptions) running in background -> build_logs/make_b21.log.
- stpncpy (0x15e9c0): lifted/stpncpy_armv8.v; proofs/stpncpy_callees.v (stp_prog, stp_pre,
  stp_post, invariants, memset_correct_in_stpncpy — memset's invariant family wrapped so each
  memset invariant also carries X19 = md; memset params mm/md/cc/mn are ghost section vars
  instantiated from the call state). Case lemmas in scratch/b21/c_*.v: e9c0, e9ec, ea0c, ea64,
  ea78 (call + return via stp_mem_ok) all close; ea38 (word loop) in progress.
  Precondition includes n - K <= 96 (memset proof covers only the small path) and 4096 <= d.
- NEXT: finish ea38, assemble (scratch/b21/assemble.py) -> proofs/stpncpy_vcs.v +
  stpncpy_proof.v, register, make; then strncpy (wrapper), strcspn.

### 2026-11-17 14:17 CST — CHECKPOINT (shutdown requested; Grok Bot)
- make_b21: `make` finished BUILD_EXIT=0 (includes memccpy, GrokFill, GrokMem). Audit printed by
  that build (Assumptions.v rebuilt): 311 x functional_extensionality_dep + 14 "Closed under the
  global context", no other axioms. The follow-up `make assumptions` re-run was killed at
  shutdown (redundant). Log: aarch64/build_logs/make_b21.log.
- stpncpy: ALL six case lemmas now close (ea38 word loop finished: k≠m ⇒ k+8<=m via (m-k) mod 8,
  haszero_test_zero ⇒ k+8<=K, bcp_word8). scratch/b21/assemble.py generated
  proofs/stpncpy_callees.v (header added), proofs/stpncpy_vcs.v (tactics + stp_mem_ok + 6 cases,
  Optimize Heap between), proofs/stpncpy_proof.v (full header from headers/stpncpy.txt,
  stpncpy_partial_correctness, stpncpy_preserves_other_callee_saved). No admits.
  The final 3-file compile was killed at shutdown (callees in progress) — NOT yet compiled as
  final files and NOT yet registered.
- New lib/GrokCall.v (compiles): nextinv'_transfer / satisfies_all_transfer — reuse a callee's
  whole satisfies_all proof inside a larger program whose invariant set agrees on the callee's
  code (avoids re-proving stpncpy VCs for strncpy). Not yet in _CoqProject.
- strncpy (0x15f14c): lifted/strncpy_armv8.v copied + compiles. Draft proof scratch/b21/sn.v
  (sn_prog, sn_pre, sn_post, invs with `if a =? ...` so non-strncpy addrs fall through to the
  stpncpy family, stpncpy_correct_in_strncpy via satisfies_all_transfer + functional
  extensionality on exits, strncpy_partial_correctness, frame thm). NOT yet compiled.
- NEXT: (1) cd aarch64; ./chk.sh proofs/stpncpy_callees.v proofs/stpncpy_vcs.v proofs/stpncpy_proof.v
  (callees ~5-10 min); (2) register in _CoqProject: lib/GrokCall.v (after GrokMem),
  lifted/stpncpy_armv8.v, proofs/stpncpy_callees.v, proofs/stpncpy_vcs.v, proofs/stpncpy_proof.v;
  Assumptions.v += stpncpy_partial_correctness, memset_correct_in_stpncpy,
  stpncpy_preserves_other_callee_saved; (3) compile/debug scratch/b21/sn.v, then make it
  proofs/strncpy_proof.v with a header; (4) make + make assumptions; (5) strcspn.

### 2026-11-17 18:36 CST — stpncpy compiled + registered; strncpy proved (Grok Bot)
- Resumed after shutdown; no stale processes of ours on debixb.
- stpncpy (0x15e9c0 / ELF 0x5e9c0) final files compiled: stpncpy_callees.v (18:06, 407 s),
  stpncpy_vcs.v (18:12, 341 s), stpncpy_proof.v (18:17, 292 s). Theorems:
  stpncpy_partial_correctness, stpncpy_preserves_other_callee_saved, memset_correct_in_stpncpy.
- strncpy (0x15f14c / ELF 0x5f14c): proofs/strncpy_proof.v (header from headers/strncpy.txt +
  scratch/b21/sn.v). Reuses the whole stpncpy proof via lib/GrokCall.v
  (satisfies_all_transfer). Theorems: strncpy_partial_correctness, stpncpy_correct_in_strncpy,
  strncpy_preserves_other_callee_saved. sn.v compiled standalone (18:31).
- Registered: _CoqProject += lib/GrokCall.v, lifted/stpncpy_armv8.v, proofs/stpncpy_{callees,vcs,proof}.v,
  lifted/strncpy_armv8.v, proofs/strncpy_proof.v; Assumptions.v prints the six theorems above.
- make_b22 (make + make assumptions) running -> aarch64/build_logs/make_b22.log, assumptions_b22.log.
- NEXT: strcspn (restricted: c[0]≠0 ∧ c[1]≠0, so the strchrnul branch is excluded).

### 2026-11-17 19:06 CST — make_b22 green; audit clean (Grok Bot)
- make_b22: `make` BUILD_EXIT=0 (rebuilt strncpy_proof.v + Assumptions.v); `make assumptions`
  ASSUM_EXIT=0. Audit (assumptions_b22.log): 331 Print Assumptions = 315 x
  functional_extensionality_dep only + 16 "Closed under the global context"; no other axioms.
  stpncpy, memset_correct_in_stpncpy, strncpy, stpncpy_correct_in_strncpy now in the build.
- strcspn (0x15ecf0) started in scratch/b23: cs_defs.v (cs_prog, cs_pre restricted to c[0],c[1]≠0,
  bset bitset model, cs_mem, cs_post, invariants at ecf0/ed4c/ed78, Post ed28) compiles; entry
  case (steps straight through memset with n=32 concretely — no call composition needed) compiles.

### 2026-11-17 19:13 CST — strcspn proved (restricted) and registered (Grok Bot)
- strcspn (0x15ecf0 / ELF 0x5ecf0): proofs/strcspn_defs.v (cs_prog = strcspn + memset lifts,
  bset bitset model, cs_mem, cs_pre, cs_post, invariants ecf0/ed4c/ed78, Post ed28) and
  proofs/strcspn_proof.v (full header from headers/strcspn.txt; lemmas bset_bit, cm_out, cm_q,
  cm_test, cm_step; VC lemmas cs_case_15ecf0/15ed4c/15ed78; strcspn_partial_correctness,
  strcspn_preserves_other_callee_saved). Both compile standalone (defs + proof ~9 min total).
  memset (n = 32) is stepped through symbolically, so no callee lemma is needed.
- RESTRICTION: cs_pre requires strlen(c) >= 2; the c[0]=0 / c[1]=0 path (bl __strchrnul)
  is not covered. Postcondition: X0 = K with K = strcspn(p,c) characterised via cs_in;
  callee-saved regs/SP restored; memory outside sp-80..sp-1 unchanged.
- Registered in _CoqProject (lifted/strcspn_armv8.v, proofs/strcspn_defs.v, proofs/strcspn_proof.v)
  and Assumptions.v. make_b23 (make + make assumptions) running -> aarch64/build_logs/make_b23.log,
  assumptions_b23.log. Scratch sources: aarch64/scratch/b23/.

### 2026-11-17 19:37 CST — make_b23 green; audit clean (Grok Bot)
- make_b23: BUILD_EXIT=0, ASSUM_EXIT=0. Audit: 333 Print Assumptions = 316 x
  functional_extensionality_dep only + 17 closed; no other axioms (strcspn included).
- Parked / next: strcspn short-set path (strlen(c) < 2 → __strchrnul) not covered;
  stpncpy/strncpy limited to n - K <= 96 (memset small path only). Candidates next: strspn
  (same bitset pattern; reuse cs lemmas), full memset (large path) to lift the 96-byte limit.
- Nothing committed. VCEffectsOnMemOverhead.md unchanged.

### 2026-11-17 20:23 CST — strspn proved (all paths) (Grok Bot)
- strspn (0x15f2e8 / ELF 0x5f2e8): proofs/strspn_defs.v + proofs/strspn_proof.v (header
  headers/strspn.txt). Leaf; table zeroed from the 32-byte all-zero .rodata constant at 0x19e6b0
  (checked with objdump; stated in ss_pre as mem Ⓧ[0x19e6b0] = mem Ⓧ[0x19e6c0] = 0). All paths
  covered: c[0]=0, single-byte set (cmp loop 0x15f340), table build 0x15f314, scan 0x15f360.
  Reuses bset/cs_in/bset_bit/zero_q from strcspn. Theorems: strspn_partial_correctness,
  strspn_preserves_other_callee_saved (X19..X29, Z8..Z15; SP is restored per ss_post but is
  assigned, so excluded from the noassign list). Registered in _CoqProject + Assumptions.v.
- Lessons: lia on failing goals with big contexts and `rewrite ... in *` near hypotheses such as
  `mem Ⓧ[0x19e6b0] = 0` can exhaust the 8 GB cap (conversion unfolds getmem); clear such hyps
  and use a cleaning lia (llia) / syntactic closers (sassumption) instead of assumption.

### 2026-11-17 21:20 CST — make_b24 green; strpbrk proved + registered; strsep in progress (Grok Bot)
- make_b24 (strspn in the full build): BUILD_EXIT=0, ASSUM_EXIT=0; audit 335 = 317
  functional_extensionality_dep-only + 18 closed. Logs build_logs/make_b24.log, assumptions_b24.log.
- strpbrk (0x15f1f8 / ELF 0x5f1f8; bl strcspn): proofs/strpbrk_defs.v + proofs/strpbrk_proof.v
  (header headers/strpbrk.txt). Reuses the whole strcspn proof via GrokCall transfer
  (strcspn_correct_in_strpbrk). Theorems: strpbrk_partial_correctness,
  strpbrk_preserves_other_callee_saved (X20..X28, Z8..Z15). Inherits strcspn's strlen(accept) >= 2
  restriction. Both files compile (proof ~10 min). Registered in _CoqProject + Assumptions.v;
  not yet in a full make run.
- strsep (0x15f258): scratch/b26/se.v — defs (se_frame/se_pre/se_post/se_invs), set_pt lemma and
  strcspn_correct_in_strsep written; main theorem: NULL path done, call set up, post-call
  (strb wzr / str x1,[x3]) still being written.
- Note: `(char *)s` inside a header comment closes the Coq comment; write `(char * )s`.

### 2026-11-17 21:58 CST — strsep proved in scratch (Grok Bot)
- scratch/b26/se.v: strsep_partial_correctness proved (NULL *str path, strcspn call via transfer
  strcspn_correct_in_strsep, both post-call paths incl. strb wzr and str x1,[x3]); memory post
  stated pointwise outside [sp-112,sp) against mem[Ⓠ q:=0] or mem[Ⓑ p+K:=0][Ⓠ q:=p+K+1]
  (lemma set_pt). Compile ~4 min. Next: split into proofs/strsep_defs.v + strsep_proof.v, header,
  frame theorem, register, make.
- Lesson: the catch-all `first [eassumption | reflexivity | unfold s2; simpl_stores; ...]` on the
  call's side goals hung >20 min here (evar store ?s); solving side goals one by one with exact
  took <1 s.

### 2026-11-17 22:15 CST — strsep final + registered; make_b25 started; memset full path started (Grok Bot)
- strsep (0x15f258 / ELF 0x5f258): proofs/strsep_defs.v + proofs/strsep_proof.v (header
  headers/strsep.txt) compiled (proof ~12 min incl. frame theorem). Theorems:
  strsep_partial_correctness, strcspn_correct_in_strsep, strsep_preserves_other_callee_saved
  (X20..X28, Z8..Z15). Inherits strcspn's strlen(delim) >= 2 restriction (when *stringp != NULL).
  Registered in _CoqProject + Assumptions.v (strpbrk too).
- make_b25 (make + make assumptions; strpbrk + strsep) running -> build_logs/make_b25.log,
  assumptions_b25.log.
- memset large path: scratch/b27/mf.v, new invariant set mf_invs (separate theorem
  memset_full_partial_correctness, precondition mf_side c n := n <= 96 \/ c mod 256 <> 0 \/ n < 160
  so the Nop-lifted dczid_el0/dc zva region 0x118498.. is cut by Inv False). Loop invariant at
  0x1184e8 over X3 (bytes [d, X3+32) = c, outside [d,d+n) unchanged). Symbolic stepping of all
  paths done; closing goals in progress.

### 2026-11-17 22:36 CST — make_b25 build green; memset full path progress (Grok Bot)
- make_b25: BUILD_EXIT=0 (strpbrk + strsep in the full build); make assumptions still running.
- memset full (scratch/b27/mf.v): entry/small paths (reused tactics), 0x118404, and 0x118480
  (incl. Inv False at the dczid region, contradicted by mf_side; new lemma land_m16:
  d .& 0xfff..f0 = d - d mod 16) close. Loop 0x1184e8 (loop-back + exit to RET 0x118500) closing
  tactics compiling (rd1 chains through four 16-byte q stores per iteration).

### 2026-11-17 22:40 CST — make_b25 green (strpbrk + strsep) (Grok Bot)
- make_b25: BUILD_EXIT=0, ASSUM_EXIT=0; audit 341 Print Assumptions = 321
  functional_extensionality_dep-only + 20 closed; no other axioms. Logs build_logs/make_b25.log,
  assumptions_b25.log. strpbrk and strsep are now in the full build.

### 2026-11-17 22:51 CST — memset large path proved in scratch (Grok Bot)
- scratch/b27/mf.v: memset_full_partial_correctness (Qed, ~5 min) for any n with
  mf_side c n := n <= 96 \/ c mod 256 <> 0 \/ n < 160 (excludes only c=0 /\ n>=160, the
  dczid_el0 / dc zva path that the lifter turns into Nops, so it cannot be soundly verified),
  4096 <= d, d+n < 2^64. Same memset_post as the small theorem. Fix for the slow loop goals: rd2
  (one in-branch, one out-branch per store via rng_dec) instead of rd1 (two out-branches, 2^8 leaves
  over the 8 q-stores). Next: final files, register, make.

### 2026-11-17 22:59 CST — memset full path final + registered; make_b26 started (Grok Bot)
- memset full (0x118400 / ELF 0x18400): proofs/memset_full_defs.v (mf_side, mf_invs) +
  proofs/memset_full_proof.v (header headers/memset_full.txt; lemmas land_m16, rng_dec, tactic
  rd2) compiled (~5 min). Theorem memset_full_partial_correctness: precondition
  mf_side c n := n <= 96 \/ c mod 256 <> 0 \/ n < 160 (excludes only the Nop-lifted
  dczid_el0/dc zva path, c = 0 /\ n >= 160), 4096 <= d, d + n < 2^64; postcondition memset_post
  (same as the small theorem). Callee-saved frame: memset_proof.memset_preserves_callee_saved
  (same program). Registered in _CoqProject + Assumptions.v.
- make_b26 (make + make assumptions) running -> build_logs/make_b26.log, assumptions_b26.log.
- Note: rd2/rng_dec live in memset_full_proof.v for now (moving them to lib/GrokFill.v would
  force a rebuild of every GrokFill dependent; do it at a quiet moment).

### 2026-11-17 23:16 CST — make_b26 green (memset full) ; stpncpy relaxation started (Grok Bot)
- make_b26: BUILD_EXIT=0, ASSUM_EXIT=0; audit 342 = 322 functional_extensionality_dep-only + 20
  closed. memset_full_partial_correctness is in the full build.
- Relaxing stpncpy/strncpy: padding memset is called with c = 0, so mf_side reduces to
  n - K < 160 (the c=0, n>=160 DC ZVA path stays out of reach of the lift). Editing
  stpncpy_callees (stp_pre n-K < 160, family-0 invariants = memset_full_defs.mf_invs,
  memset_correct_in_stpncpy re-proved with the full script), stpncpy_vcs call site, strncpy
  (sn_pre, stp_post_addr). Originals backed up in scratch/b28/orig/.
- 23:23 stpncpy_callees: memset_correct_in_stpncpy now uses SIDE: mf_side; fixing the
  full-script port (wrapped invariants need unfold mf_loop / memset_post). Recompiling.
- 23:32 stpncpy_callees port: 0x118480 case closes; 0x1184e8 failed only because
  `unfold mfb, fbase, mf_loop in *` left fbase folded (mf_loop unfolds into fbase) -> reordered
  to `unfold mf_loop, mfb, fbase in *`. Recompiling (~6 min per try).
- 23:44 proofs/stpncpy_callees.v compiles with the full memset script (~12 min).
  Compiling stpncpy_vcs -> stpncpy_proof -> strncpy_proof.
- 23:49 Restarted the stpncpy_vcs -> stpncpy_proof -> strncpy_proof chain detached
  (setsid nohup aarch64/build_logs/run_b27.sh; logs chain_b27.log, then make_b27 /
  assumptions_b27). If it fails: restore proofs/stpncpy_{callees,vcs,proof}.v, strncpy_proof.v and
  headers from scratch/b28/orig/.
- 23:50 bzero_full (0x15e0fc): proofs/bzero_full_proof.v, theorem
  bzero_full_partial_correctness (n < 160 instead of n <= 96; mov/mov/b memset chained onto
  memset_full_partial_correctness, ~1 s). bzero_proof.v kept unchanged. Registered in _CoqProject +
  Assumptions.v (picked up by make_b27).
- 23:58 chain_b27 still compiling stpncpy_vcs (detached). In parallel:
  scratch/b29/ebf.v = explicit_bzero_full (memset_full script re-run inside eb_prog with the
  frame_mem remember trick; n < 160), compiling.
- 00:06 chain_b27 try 1 failed (log chain_b27_fail1.log): call-site side goal
  memset_full_defs.mf_side 0 (s1 R_X2) not solved because stpncpy_vcs does not Import
  memset_full_defs (unqualified `unfold mf_side` failed). Fixed (qualified name), relaunched
  detached run_b27.sh.
- 00:06 explicit_bzero_full (0x15e108): scratch proof compiled; final
  proofs/explicit_bzero_full_defs.v (ebf_invs) + explicit_bzero_full_proof.v (header; theorems
  memset_full_correct_in_explicit_bzero, explicit_bzero_full_partial_correctness, n < 160)
  compiling; registered in _CoqProject + Assumptions.v ahead of make_b27.
- 00:13 stpncpy_vcs.v compiled with the relaxed precondition (00:13); stpncpy_proof / strncpy_proof next in the detached chain.
- 00:20 explicit_bzero_full final files compiled (00:17); stpncpy_proof compiled (00:20); strncpy_proof compiling, then make_b27.

### 2026-11-18 00:28 CST — stpncpy/strncpy relaxed to n - K < 160 (chain green); make_b27 running (Grok Bot)
- chain_b27: stpncpy_vcs, stpncpy_proof, strncpy_proof all compile (CHAIN_EXIT=0). stp_pre /
  sn_pre now require n - K < 160 instead of <= 96 (zero padding; only the Nop-lifted DC ZVA path,
  c = 0 /\ n >= 160, stays excluded). memset_correct_in_stpncpy re-proved with the full memset
  script. Headers (proof files + headers/stpncpy.txt, strncpy.txt) updated. Originals in
  scratch/b28/orig/.
- make_b27 + make assumptions now running detached (same run_b27.sh).

### 2026-11-18 00:42 CST — make_b27 green
- make_b27: BUILD_EXIT=0; assumptions_b27: ASSUM_EXIT=0, 345 Print Assumptions = 325 fext-only + 20 closed, no other axioms.
- Covers stpncpy/strncpy relaxed to n-K<160 (via memset_full), bzero_full, explicit_bzero_full.
- Next: strcspn short-set path (strlen(c)<2 → __strchrnul) needs X19 preserved across transferred callee proof.

### 2026-11-18 00:48 CST — strcspn short path: lib/GrokKeep.v + strchrnul transfer
- New lib/GrokKeep.v (compiled, not yet in _CoqProject): keep_invs / satisfies_all_keep — strengthen a proved
  invariant family with "s v = val" when the program never assigns v (prog_noassign). Carries X19 through __strchrnul.
- scratch/b30/css_defs.v (css_prog = strcspn + strchrnul_prog, css_frame, css_pre with Lc < 2, css_post (mem outside
  [sp-112,sp)), css_F = strchrnul invs wrapped with X19 = p) and scratch/b30/css.v: strchrnul_correct_in_strcspn
  (GrokCall transfer + GrokKeep) compiled. Next: main css theorem (entry -> bl -> sub -> ret).

### 2026-11-18 01:07 CST — strcspn short path proved (scratch)
- scratch/b30/css.v compiled (~4.5 min): strcspn_short_partial_correctness (Lc = strlen(c) < 2: __strchrnul(s,c[0]) - s,
  post = cs_post shape with memory unchanged outside [sp-112,sp)), via strchrnul_correct_in_strcspn (GrokCall + GrokKeep),
  helper lemmas css_K, css_cs_in, msub_addK. Next: final files proofs/strcspn_short_{defs,proof}.v, header, register, make.

### 2026-11-18 01:08 CST — strcspn short path: final files registered; make_b28 running
- headers/strcspn_short.txt; proofs/strcspn_short_defs.v, proofs/strcspn_short_proof.v (from scratch/b30): theorems
  strchrnul_correct_in_strcspn, strcspn_short_partial_correctness (strlen(c) < 2),
  strcspn_short_preserves_other_callee_saved. lib/GrokKeep.v added to _CoqProject (after GrokCall); 3 Prints added to
  Assumptions.v (expected 348 total).
- Detached build_logs/run_b28.sh (PID 72702): chain_b28 -> make_b28 (BUILD_EXIT) -> assumptions_b28 (ASSUM_EXIT).
- Together with strcspn_proof (Lc >= 2) this covers strcspn for every reject set (two theorems, complementary pre).
  Next candidate: lift strpbrk/strsep to the short path the same way (transfer css into pb/se programs).

### 2026-11-18 01:14 CST — chain_b28 green; strpbrk short path drafted
- chain_b28: GrokKeep + strcspn_short_{defs,proof} CHAIN_EXIT=0; make_b28 + assumptions_b28 now running (run_b28.sh).
- scratch/b31/pbs_defs.v + pbs.v (strpbrk for strlen(c) < 2, transfer of strcspn_short into pbs_prog, ids 3/2/1/0,
  memory outside [sp-144,sp)) compiling detached (scratch/b31/run.sh -> pbs.log PBS_EXIT).

### 2026-11-18 01:21 CST — strpbrk short path proved; make_b29 queued
- scratch/b31 pbs compiled (PBS_EXIT=0). Final: headers/strpbrk_short.txt, proofs/strpbrk_short_defs.v,
  proofs/strpbrk_short_proof.v (strcspn_short_correct_in_strpbrk, strpbrk_short_partial_correctness (strlen(c) < 2,
  mem outside [sp-144,sp)), strpbrk_short_preserves_other_callee_saved).
- build_logs/run_b29.sh (detached) waits for run_b28, then registers strpbrk_short (_CoqProject + 3 Prints, expected 351),
  chain_b29 -> make_b29 -> assumptions_b29. If a session cut happens: just check those logs.

### 2026-11-18 01:28 CST — make_b28 green (strcspn short); strsep short compiling
- make_b28 BUILD_EXIT=0; assumptions_b28 ASSUM_EXIT=0: 348 Prints = 327 fext-only + 21 closed, no other axioms.
- run_b29 (strpbrk_short register + make) now proceeding automatically.
- scratch/b32/ses_defs.v + ses.v (strsep for *str = 0 or strlen(sep) < 2, ids 3/2/1/0, mem outside [sp-144,sp))
  compiling detached (scratch/b32/run.sh -> ses.log SES_EXIT).

### 2026-11-18 01:30 CST — resume after ~01:28 cut: detached jobs survived
- setsid nohup jobs are alive: run_b29 (PID 73789, compiling strpbrk_short_proof) and scratch/b32/run.sh (PID 74369,
  compiling ses.v). Compiles show up as "rocqworker", not "coqc" (Rocq 9.1), hence not visible to a coqc grep.
- headers/strsep_short.txt written.

### 2026-11-18 01:34 CST — strsep short path proved; make_b30 queued
- scratch/b32 ses compiled (SES_EXIT=0); chain_b29 (strpbrk_short) CHAIN_EXIT=0, make_b29 running.
- Final: proofs/strsep_short_defs.v, proofs/strsep_short_proof.v (strcspn_short_correct_in_strsep,
  strsep_short_partial_correctness (*str = 0 or strlen(sep) < 2, mem outside [sp-144,sp)),
  strsep_short_preserves_other_callee_saved).
- build_logs/run_b30.sh (detached) waits for run_b29, registers strsep_short (+3 Prints, expected 354), chain_b30 ->
  make_b30 -> assumptions_b30.

### 2026-11-18 01:37 CST — next: strtok (strspn + strcspn composition), plan
- strtok (0x15f7c4, lifted_raw/strtok_armv8.v): static G = 0x1c25e0 (adrp x21 + 0x5e0); bl strspn 0x15f2e8, bl strcspn
  0x15ecf0. Plan (scratch/b33): tk_prog = strtok + strspn + cs_prog (Lc >= 2 first; short sets via css later).
  strspn's post lacks X19/X20/X21/X29 -> new multi-register keep (scratch/b33/keepl.v: keepl_invs / satisfies_all_keepl,
  compiled; goes into lib/GrokKeep.v after make_b30). strcspn's memory param = memory after strspn (only known at the
  call) -> family parametrised by (M1, K1), perform_call with g ≠ f (same_invset_family by conversion).
- Waiting: run_b29 (make_b29) then run_b30 (strsep_short register + make_b30).

### 2026-11-18 01:40 CST — strtok progress
- lifted/strtok_armv8.v (copy of lifted_raw, compiles). scratch/b33/tk_defs.v (tk_prog, tk_frame, tk_pre, tk_post,
  family with ids 2 strtok / 1 strcspn (params M1 K1, X21 kept) / 0 strspn (X19,X20,X21,X29 kept)) compiles.
  scratch/b33/tk.v: prog lemmas, tk_at_ss/tk_at_cs dispatch, ss_shape/cs_shape, tk_post_addr compile.
  Next: strspn_correct_in_strtok, strcspn_correct_in_strtok (transfer + keepl), then main theorem.

### 2026-11-18 01:44 CST — strtok: both callee transfers proved
- scratch/b33/tk.v: strspn_correct_in_strtok (GrokCall transfer + keepl of X19/X20/X21/X29) and
  strcspn_correct_in_strtok (transfer + keepl X21, memory param M1 = memory at the strcspn call) compile (~45 s).
  Next: main theorem strtok_partial_correctness (entry, join 0x15f7e0, two perform_calls with g = family at (M1,K1)).

### 2026-11-18 01:50 CST — make_b29 green (strpbrk short)
- make_b29 BUILD_EXIT=0, assumptions_b29 ASSUM_EXIT=0: 351 Prints = 329 fext-only + 22 closed (Axioms blocks: 329, all fext).
- run_b30 (strsep_short) now running. strtok: entry-case lemma hits the 8 GB cap when a memory lemma (FG) is in the
  context during repeat arm8_step; restructuring (do the read-through after stepping).

### 2026-11-18 02:12 CST — make_b30 green (strsep short) — short-set coverage done
- run_b30: CHAIN_EXIT=0, make_b30 BUILD_EXIT=0, assumptions_b30 ASSUM_EXIT=0: 354 Prints = 331 fext-only + 23 closed.
  strcspn / strpbrk / strsep now proved for both Lc >= 2 (bitmap) and Lc < 2 (strchrnul) paths.
- strtok (scratch/b33/tk.v): tk_case_entry (entry block, static/null/direct paths) now Qed (~100 s, under 8 GB).
  OOM cause was `contradiction` / first[reflexivity|..] closers over large frame-memory goals; replaced with explicit
  terms (exfalso; exact (NZ BC), refine (conj ... eq_refl ...)). Next: join case with the two perform_calls.

### 2026-11-18 02:33 CST — strtok join case in progress
- keepl (multi-register keep) moved from scratch into lib/GrokKeep.v (keepl_st/keepl_head/keepl_invs/satisfies_all_keepl);
  tk_defs/tk import it; both recompile.
- scratch/b33/tkj.v: helper lemmas setmem_agree_B, agree_cs_in, agree_nilfree, agree_X (memory agreement below a bound).
  tk_case_join: strspn perform_call (CALLEE obligations incl. ss_pre on the frame, SF) done; working on the post-strspn steps.
- OOM lessons: never run L64/lia with the full post-step context (use `clear - H..; L64`); avoid big nested
  `refine (conj ... ltac:(..))` — use split + small bullets. Both blew the 8 GB cap in seconds.

### 2026-11-18 02:47 CST — strtok join: both calls discharged
- tkj.v tk_case_join: strspn call + post, "*s == 0" path to Post (static := 0, X0 = 0) closed; strcspn call
  (perform_call 1 2 with g = tk_invs at M1 = memory after "str x2,[sp,#0x38]", K1 = strspn result) CALLEE/SF closed.
  New lemmas: tk_FR_Q (frame qword reads), tk_post_A. Remaining: post-strcspn two exits (token end / string end).
- Note: level-1 invariants are not stop points for the level-2 family, so use `do N arm8_step` before a bl (repeat hangs).

### 2026-11-18 02:59 CST — strtok tk_case_join Qed
- scratch/b33/tkj.v compiles (~125 s, < 8 GB): tk_case_join covers strspn call, empty-token path, strcspn call,
  token-to-end path (static := 0) and separator path (static := end+1, NUL written). Lemmas tk_post_A/B1/B2, tk_FR_Q.
- Next: strtok_partial_correctness (prove_invs; dispatch entry/join to the two case lemmas), frame theorem, final files.

### 2026-11-18 03:08 CST — strtok proved (Lc >= 2); run_b31 launched
- strtok_partial_correctness (main, ~10 s) + strtok_preserves_other_callee_saved (X22..X28, Z8..Z15) compile in scratch;
  Print Assumptions: fext only / closed.
- Final files: headers/strtok.txt, proofs/strtok_defs.v, strtok_callees.v (transfer theorems + entry case),
  strtok_join.v (join case), strtok_proof.v (header + main + frame). lifted/strtok_armv8.v registered.
- build_logs/run_b31.sh (setsid nohup, PID 83279): chain_b31 -> make_b31 -> assumptions_b31 (expect 358 Prints).
- Restriction: strlen(sep) >= 2 (strcspn bitmap path). Short-set strtok needs a strspn short path too — later.

### 2026-11-18 03:11 CST — run_b31 first attempt failed (my error), relaunched
- chain_b31 (saved as chain_b31_fail1.log) failed in 1 min: the debug-idtac stripping left bare "all:" lines in
  proofs/strtok_join.v ("Brackets do not support multi-goal selectors"); strtok_proof then had no strtok_join.vo.
  Not a session-kill. Fixed (bare lines removed), run_b31.sh relaunched (setsid nohup).

### 2026-11-18 03:14 CST — strtok short-set path started (scratch/b34)
- tks_defs.v compiles: tks_prog = strtok + strspn + css_prog; strspn's family renumbered 0 -> 3 inside the strtok family
  (ids: strtok 4, strspn 3, strcspn 2, strchrnul 1, strlen 0); window sp-176 (strcspn's 112-byte short frame below sp-64).
- tks.v (program lemmas, shape lemmas, both transfer theorems) written; waiting on make_b31 to rebuild strcspn_short_proof.vo
  (stale vs the extended lib/GrokKeep.v) before it can be checked.

### 2026-11-18 03:24 CST — chain_b31 green, make_b31 running
- chain_b31 CHAIN_EXIT=0: lifted/strtok_armv8, GrokKeep, strtok_defs/callees/join/proof all compile standalone.
- strtok short path (scratch/b34): tks.v now also holds tks_case_entry; tksj.v (join, retargeted to the short strcspn
  with perform_call 3 4 / 2 4) and tksm.v (main + frame) generated from the strtok sources; all pending
  strcspn_short_proof.vo rebuild by make_b31.

### 2026-11-18 03:34 CST — strtok short path: transfer, entry and join cases Qed
- scratch/b34/tks.v (program/shape lemmas, strspn_correct_in_strtok_short, strcspn_short_correct_in_strtok,
  tks_case_entry; ~127 s) and tksj.v (tks_case_join; ~162 s) compile. Main/frame (tksm.v) compiling.

### 2026-11-18 03:42 CST — strtok short path proved; run_b32 queued
- tksm.v: strtok_short_partial_correctness + strtok_short_preserves_other_callee_saved compile (~7 min, frame thm
  dominates); Print Assumptions: fext only / closed. strtok now covered for every separator set.
- Final files: headers/strtok_short.txt, proofs/strtok_short_{defs,callees,join,proof}.v.
- build_logs/run_b32.sh (setsid nohup) waits for run_b31, registers them + 4 Prints (expect 362), chain_b32 -> make_b32
  -> assumptions_b32.

### 2026-11-18 03:51 CST — make_b31 green (strtok, strlen(sep) >= 2)
- run_b31: CHAIN_EXIT=0, make_b31 BUILD_EXIT=0, assumptions_b31 ASSUM_EXIT=0: 358 Prints = 334 fext-only + 24 closed
  (every Axioms block is functional_extensionality_dep only). New: strspn/strcspn_correct_in_strtok,
  strtok_partial_correctness, strtok_preserves_other_callee_saved.
- run_b32 (strtok short path) now running its chain; expect 362 Prints.

### 2026-11-18 03:53 CST — next target: memcpy (hand-written asm, 0x118270)
- Target scan (skills/verification-target-finding): unproved lifted functions are memcpy, memmove, mempcpy, memrchr,
  strrchr/rindex, strstr/wcsstr/wcswcs, wcstok, rand_r, getenv, strerror_r, bsearch/lfind/lsearch, strdup/wcsdup.
  memcpy ranks highest: hand-written asm (Linaro-style src/string/aarch64/memcpy.S), leaf, clear spec, 95 insns,
  security-critical. Scalar x-register code only (no SIMD).
- Plan: (1) n <= 128 path: straight-line, every load precedes every store in each branch (so the result is
  correct even for overlapping buffers); spec: M[a] = mem[s + (a-d)] for d <= a < d+n, else mem[a].
  (2) n > 128: aligned 64-byte loop with interleaved ldp/stp, needs disjointness + loop invariant.
  Then mempcpy (memcpy + add), memmove (calls memcpy for small/forward cases?) — to check.

### 2026-11-18 04:02 CST — memcpy n <= 128 in progress (scratch/b35)
- run_b32 still in its chain (strtok_short_proof.v compiling).
- lifted/memcpy_armv8.v copied from lifted_raw (not yet registered). scratch/b35/mcp_lib.v: byte_getmem,
  msub_add_mod, addr_norm (normalizes (x ⊖ k) + y addresses via get/setmem_mod_l), copy_byte. No 4096 <= d/src
  precondition needed. mcp_defs.v: pre (n <= 128, d+n < 2^64, src+n < 2^64), post (copied bytes + outside
  unchanged, X0 = d). Symbolic stepping gives 9 goals (8 RET paths + the 0x118370 False case); closing now.

### 2026-11-18 04:34 CST — memcpy memory lemmas green
- chain_b32 CHAIN_EXIT=0 (strtok short); make_b32 running.
- scratch/b35/mcp_mem.v: cp_16_32, cp_8_15, cp_4_7, cp_1_3, cp_33_64, cp_65_96, cp_97_128 (copied mem M src d n for
  each size class's exact store chain) all check. Lessons: rd1 is exponential on long chains (two "outside"
  branches); new rdc in mcp_lib uses one disjunctive outside branch -> linear. Again: no reflexivity on big mem goals.
- Next: main theorem = stepping + apply cp_* per leaf.

### 2026-11-18 04:43 CST — run_b32 GREEN (strtok short registered)
- chain_b32 CHAIN_EXIT=0, make_b32 BUILD_EXIT=0, assumptions_b32 ASSUM_EXIT=0: 362 = 337 fext-only + 25 closed.
  strtok now proved for all separator sets (strtok_partial_correctness Lc>=2, strtok_short_partial_correctness Lc<2).
- memcpy: added cp_0 + apply_cp (picks size-class lemma by store-chain shape) + pow_lits; main-theorem probe
  compiling (scratch/b35/mcp_probe.v). Earlier attempt left only n=0 and n in {96,128}-boundary goals (2^k literals).

### 2026-11-18 04:50 CST — memcpy n <= 128 PROVED (scratch), run_b33 launched
- Main theorem closes: residual infeasible leaves had `0 .| 1 = 0` branch hyps (vm_compute; discriminate).
- Final files: lib/GrokCopy.v, proofs/memcpy_defs.v, proofs/memcpy_mem.v, proofs/memcpy_proof.v (header,
  welltyped, nwc, preserves_callee_saved, preserves_x30, memcpy_partial_correctness), headers/memcpy.txt,
  lifted/memcpy_armv8.v. No disjointness needed (loads precede stores on all n <= 128 paths).
- build_logs/run_b33.sh (detached): chain_b33 -> registers in _CoqProject + 2 Prints -> make_b33 -> assumptions_b33.
  Expect 364. Next: n > 128 loop (needs disjointness), then mempcpy / memmove.

### 2026-11-18 04:59 CST — memcpy n > 128 in progress (scratch/b36)
- run_b33 (memcpy n<=128 registration + make) running.
- mcl_lib.v: cov predicate (copy-coverage set C + outside unchanged), cov_init/mono/store8(')/copied, cov_src(')
  (source reads unaffected under disjointness), land15, land_m16', msub64_small', upd_simpl/num_norm/src_read/cov_peel.
- mcl_defs.v: pre adds 128 < n and src+n <= d \/ d+n <= src; invariants at 0x1183a0 (loop head: ∃L, L done,
  x6..x13 = next 64 src bytes, x1 = src+L+48, x2 = n-L-128) and 0x1183c8 (tail: 64 < n-L <= 128); post at 0x1183f8.
  Stepping probe OK (10 VCs). Closing tactics next.

### 2026-11-18 05:25 CST — memcpy n>128: entry VC closes
- Entry -> loop/tail VCs all close (scratch/b36/mcl_probe.v; stepping 150 s, rest ~3 min). Fixes: eapply in
  cov_peel, lor_absurd for infeasible `0 .| 1 = 0` leaves, pow_lits_g for 2^k in goals. Now testing loop + tail VCs.

### 2026-11-18 05:31 CST — run_b33 GREEN: memcpy n <= 128 in the build
- chain_b33 CHAIN_EXIT=0, make_b33 BUILD_EXIT=0, assumptions_b33 ASSUM_EXIT=0: 364 = 338 fext-only + 26 closed.
- LESSON (process, from Ilan via Meta): runs get cut ~every 50 min and setsid/nohup children die with the app cgroup
  (app-grok-bot-*.scope). Launch every long compile/build in its own systemd user unit:
    systemd-run --user --unit=coq-bNN --same-dir --collect bash -lc 'make > build_logs/make_bNN.log 2>&1; echo BUILD_EXIT=$? >> build_logs/make_bNN.log'
  Check with `systemctl --user status coq-bNN` or the log; after a cutoff read logs/unit status, don't relaunch.
  (Linger off: survives cutoffs, not logout.)

### 2026-11-18 05:39 CST — memcpy n>128 loop/tail VC probes as systemd units
- Full probe (entry+loop+tail) exceeded 770 s; split into scratch/b36/mcl_ploop.v and mcl_ptail.v, running as
  units coq-mcl-loop / coq-mcl-tail via scratch/b36/run1.sh (logs scratch/b36/*.log, unbuffered).
- Note: systemd user units don't get the opam PATH; scripts must export PATH=/home/ixb/.opam/Rocq9.1/bin:$PATH.

### 2026-11-18 05:47 CST — mempcpy started (scratch/b37), memcpy n>128 probes still running
- mempcpy (0x15e81c): stp x29,x30,[sp,-32]!; mov; str x2,[sp,24]; bl memcpy; ldr x2; ldp; add x0,x0,x2; ret.
  lifted/mempcpy_armv8.v copied (unregistered). mpc_defs.v: mp_prog = updateall2 mempcpy memcpy, mp_fm (frame
  memory at the call), mp_pre (n <= 128, [d,d+n) disjoint from frame [sp-32,sp)), mp_post (X0 = d+n, X29/X30/SP
  restored, copied mp_fm src->d), mp_inv_fn = memcpy_inv_fn over mp_fm for ids 0. mpc.v: memcpy_correct_in_mempcpy
  (re-run of the memcpy script) + mempcpy theorem draft via perform_call 0 (unit coq-mpc).
- memcpy n>128: tail VC needed addr_norm before num_norm (src ⊖ k + n addresses); loop VC src_read step slow (~200 s).

### 2026-11-18 05:55 CST — memcpy n>128: lia blow-up fixed with chain lemmas
- Cause of the hang: coverage sets built by nested disjunctions (8/16 levels) -> lia case-splits 2^k. Fix:
  scratch/b36/mcl_chain.v: cov_step + cov_entry2 / cov_loop8 / cov_tail16, each quantified over the store
  addresses/values with equations as premises (eapply unifies the chain shape; side goals lia/f_equal), proved once
  with explicit prefix/block sets (8 s total). cov_close tactic. Loop + tail probes relaunched (units).

### 2026-11-18 06:04 CST — memcpy n>128 PROVED (all VCs close); run_b34 launched (unit coq-b34)
- Entry, loop and tail VCs each close in the probes. Final files: lib/GrokCov.v, proofs/memcpy_large_defs.v,
  proofs/memcpy_large_chain.v, proofs/memcpy_large_proof.v (memcpy_large_partial_correctness: n > 128, buffers
  disjoint), headers/memcpy_large.txt. build_logs/run_b34.sh: chain_b34 -> register + 1 Print -> make_b34 ->
  assumptions_b34 (expect 365). Together with memcpy_proof (n <= 128, overlap allowed) memcpy is fully covered.
- mempcpy: callee theorem compiles; perform_call wiring being debugged (scratch/b37/mpc_main.v, unit coq-mpc).

### 2026-11-18 06:15 CST — mempcpy: perform_call wired, post goals being closed
- scratch/b37/mpc_callee.v (memcpy_correct_in_mempcpy) compiles. mpc_main.v: perform_call 0 needs goal order
  contains/subset/ENTRY/MDL2, then same_invset_family by reflexivity BEFORE the memcpy_pre goal (evars).
  Post: 6 identical goals (one per memcpy RET); frame reads via copied_out_read + getmem_setmem(_above).

### 2026-11-18 06:18 CST — mempcpy (n <= 128) PROVED; run_b35 queued (unit coq-b35, waits for coq-b34)
- Final files: proofs/mempcpy_defs.v, proofs/mempcpy_callee.v (memcpy_correct_in_mempcpy), proofs/mempcpy_proof.v
  (header, mempcpy_partial_correctness, mempcpy_preserves_other_callee_saved), headers/mempcpy.txt,
  lifted/mempcpy_armv8.v. Spec relative to mp_fm (entry memory + frame slots), like explicit_bzero.
- Expect assumptions 365 (b34) then 368 (b35).
- memmove plan (C, 0x15e708): d==s -> return; if (s-d-n) <= -2n (unsigned; i.e. disjoint) -> tail-call memcpy
  (b 0x118270, any n: needs both memcpy theorems re-checked in a combined program, or a transfer lemma);
  else forward (d<s) / backward byte+word loops, needing an overlap-aware invariant (dest prefix = original src
  prefix, source suffix still original). wmemmove's proof uses an operational spec (wcpy/bcpy); for memmove use
  byte-level copied spec instead.

### 2026-11-18 06:20 CST — memmove started (scratch/b38)
- mmv_lib.v (checks): fwd/bwd overlap-aware predicates (dest prefix/suffix done, source suffix/prefix still
  original), fwd/bwd_init, fwd/bwd_step (len <= 8 store of bytes = original source), fwd/bwd_read, fwd/bwd_done ->
  copied, copied_same, byte_load.
- mmv_defs.v (checks): mv_prog = updateall2 memmove memcpy; pre: bounds, n < 2^62, (n <= 128 \/ overlap) so the
  tail call b memcpy is covered by memcpy_inv_fn (n <= 128) — large disjoint memmove needs the large memcpy
  invariants merged later. Invariants at 0x15e7ac/758/788 (forward), 7c0/7f8/814 (backward), 7b4 join, 7b8 post.
- Stepping probe running (unit coq-mmv). run_b34 (memcpy large) still in progress; run_b35 queued.

### 2026-11-18 06:30 CST — resume after cutoff; b34 done (chain ok), memmove restructured
- coq-b34: chain_b34 CHAIN_EXIT=0 (memcpy n>128 files compile); full make + assumptions running inside the unit.
  coq-b35 (mempcpy) waiting on it. Units survived the 06:20 cutoff (systemd-run works).
- memmove: b38 probe (memcpy invariants merged in) showed the memcpy VCs re-appear inside memmove -> too costly.
  New split: (A) scratch/b39 mva_*: program = memmove_armv8 only, pre: n = 0 \/ overlap (d < s+n /\ s < d+n);
  the disjoint branch (0x15e750) gets invariant False (unreachable). (B) disjoint n > 0: straight-line prefix
  then `b memcpy` -> chain step_satisfies_all / tailcall_satisfies_all (as bzero) into memcpy_invs, reusing
  memcpy_partial_correctness (n <= 128) and memcpy_large_partial_correctness (n > 128). Probe A running (coq-mva).

### 2026-11-18 06:44 CST — memcpy n>128 IN BUILD (b34 green); memmove A/B drafted
- coq-b34: make_b34 BUILD_EXIT=0, assumptions_b34 ASSUM_EXIT=0: 365 results = 26 closed + 339 with only
  functional_extensionality_dep (no other axioms). memcpy is now fully covered (n <= 128 any overlap; n > 128 disjoint).
- coq-b35 (mempcpy) running its chain (mempcpy_callee.v).
- memmove (A) scratch/b39/mva_probe.v: 22 VCs, per-VC scripts written (fwd/bwd step/read lemmas, mod8 helpers,
  mva_branch = disjoint test fails on overlap / n=0). mva_branch first proof (lia over div_mod atoms with 2^64
  constants) ran >6 min -> rewritten with explicit mod_q1/mod_q2 case analysis.
- memmove (B) scratch/b39/mvb.v: Section Prefix (generic Invs/xp), r708 -> r70c -> ... -> r72c via
  step_satisfies_all + step_stmt per instruction (Pb carries models via step_models), r750 tailcall_satisfies_all.
  Instances: memmove_disjoint_small_partial_correctness (memcpy_invs) and ..._large_... (mcl_invs).

### 2026-11-18 06:57 CST — memmove PROVED (all VCs close); run_b36 launched; b35 relaunched
- coq-b35 had failed: chain_b35 CHAIN_EXIT=1 — the mempcpy header text "(char *)memcpy" closed the Coq comment
  ("*)").  Fixed wording in proofs/mempcpy_proof.v + headers/mempcpy.txt; relaunched as unit coq-b35b (same
  build_logs/run_b35.sh: chain -> register -> make_b35 -> assumptions_b35, expect 368).
- memmove (A) overlap/n=0: all 22 VCs close (scratch/b39/mva_try.v, error-tolerant run: no FAIL); (B) disjoint
  small/large: scratch/b39/mvb.v compiles (Qed).
- Final files: lib/GrokPrefix.v (step_models, reset_reg, lor_odd, msub_self, mod_q1/2), proofs/memmove_lib.v
  (fwd/bwd, mva_branch, mvb_disj, mod8 lemmas), proofs/memmove_defs.v, proofs/memmove_prefix.v (Section Prefix:
  r708..r750), proofs/memmove_proof.v (header; memmove_overlap_partial_correctness,
  memmove_disjoint_small_partial_correctness, memmove_disjoint_large_partial_correctness,
  memmove_preserves_callee_saved), headers/memmove.txt. Together: every n < 2^62 with d+n, s+n < 2^64.
- build_logs/run_b36.sh (unit coq-b36): chain_b36 -> waits for coq-b35b -> registers (+ lifted/memmove_armv8.v)
  -> make_b36 -> assumptions_b36 (expect 372).
- Next: memrchr. NEON-vectorised for n > 14 with 16-aligned end; plan: scalar-path theorem first
  (n <= 14 or (s+n-16) mod 16 <> 0), then look at the NEON block test.

### 2026-11-18 07:07 CST — memrchr scalar path in progress; b35b/b36 running
- b35b (mempcpy chain+build) and b36 (memmove final chain, waits on b35b) still running under systemd; no results yet.
- memrchr (scratch/b40/mrc.v): fixed Section-argument order in the probe goal (mrc_pre sp mem raddr p c n s). Six VCs after grok_step: NEON-path exclusion (n>14 ∧ 16-aligned end) closed by precondition; two entry→loop VCs and the loop exit/match/continue VCs being closed (msub1, c8_small). Scope: NEON path excluded by precondition `n <= 14 ∨ (p+n) mod 16 ≠ 0`.
- Next: strrchr = frame + bl strlen + tail call memrchr(s, c, len+1); template proofs/strchr_callees.v.

### 2026-11-18 07:18 CST — b35b chain OK, b36 chain OK; memrchr finalising; strrchr started (scratch/b41)
- After the ~07:10 interruption: units coq-b35b (mempcpy make running, chain_b35 CHAIN_EXIT=0) and coq-b36
  (memmove final files: chain_b36 CHAIN_EXIT=0, now waiting on b35b before register/make) still running; not relaunched.
- memrchr: scalar-path proof closed in scratch (scratch/b40/mrc.v, no FAIL). Final files: lifted/memrchr_armv8.v,
  proofs/memrchr_defs.v (mrc_pre/mrc_loop/mrc_post, invariant family with level parameter lv and X19/X29 carried
  so strrchr can reuse it at level 1), proofs/memrchr_lib.v (msub1, c8_small, nomatch_empty/step, VC closer
  Ltacs mrc_neon/enter/null/found/next), proofs/memrchr_proof.v (header, memrchr_partial_correctness,
  preserves_callee_saved/x30), headers/memrchr.txt.  Lesson: Ltac bodies may not mention hypothesis/variable
  names that only exist at use site (pass them as arguments or use lemmas).
- strrchr: rr_prog = strrchr+memrchr+strlen; family: strrchr entry + memrchr invs at level 1 (params sp,
  rr_frame, raddr, x19, x29, p, c mod 2^32, k+1), strlen invs at level 0 transferred (GrokCall) from
  strlen_partial_correctness.  Precondition carries k = strlen (nilfree + NUL in the frame memory).

### 2026-11-18 07:32 CST — b35b GREEN (mempcpy registered); b36 now building
- run_b35 (unit coq-b35b): chain_b35 CHAIN_EXIT=0, make_b35 BUILD_EXIT=0, assumptions_b35 ASSUM_EXIT=0:
  368 Print Assumptions = 27 "Closed under the global context" + 341 with only
  FunctionalExtensionality.functional_extensionality_dep.  mempcpy (n <= 128) is in the build.
- coq-b36 (memmove) chain passed; it has now proceeded to register + make_b36 + assumptions_b36 (expect 372).
- memrchr_proof.v: fixed stale VC-closer calls (Ltacs now take hypothesis names as arguments); recheck running
  (unit coq-mrc10).  Note memrchr_preserves_callee_saved (prove_regs_noassign) is slow here (NEON block, minutes).

### 2026-11-18 07:58 CST — b36 GREEN (memmove in the build); strrchr composition probing
- run_b36 (unit coq-b36): chain_b36 CHAIN_EXIT=0, make_b36 BUILD_EXIT=0, assumptions_b36 ASSUM_EXIT=0.
  372 Print Assumptions = 28 closed + 344 with only functional_extensionality_dep (as expected).
  memmove (overlap/n=0, disjoint small, disjoint large, callee-saved) is registered and builds.
- memrchr: tolerant re-run of the final script (scratch/b40/mrt.v) closes every VC; destruct_inv already
  discharges the `Inv False` NEON-block invariant (removed that bullet).  Strict file recheck running (coq-mrc11;
  ~10 min, dominated by prove_regs_noassign over the NEON code).
- strrchr (scratch/b41/rr.v, rr2.v): strlen transfer lemma proved (GrokCall); family re-parameterised by n
  (= strlen + 1) so memrchr's closers apply verbatim; X19 = s carried across strlen with GrokKeep
  (satisfies_all_keep).  Remaining: the post-call frame reads at the tail call into memrchr.

### 2026-11-18 08:03 CST — strrchr + rindex written; run_b37 queued (unit coq-b37)
- Interrupted ~08:00; only my unit coq-rr7 (strict chain of memrchr_defs/lib + strrchr_defs/callees/proof) was
  running; not relaunched.  b35b and b36 had already finished green (see 07:32 / 07:58).
- strrchr: scratch probe rr2.v closed every VC (memrchr VCs via memrchr_lib closers; post-call frame reads by
  psimpl after unfolding rr_frame).  Final: proofs/strrchr_defs.v, strrchr_callees.v (rr_prog, strlen transfer +
  GrokKeep X19), strrchr_proof.v (header, strrchr_partial_correctness, strrchr_preserves_other_callee_saved),
  headers/strrchr.txt.  memrchr_lib gained c8_32 (c mod 2^8 = c8 (c mod 2^32)).
- rindex = `b strrchr`: proofs/rindex_proof.v via GrokTail.tailcall_satisfies_all (pattern of index_proof.v);
  lifted/rindex_armv8.v copied from lifted_raw; headers/rindex.txt.
- build_logs/run_b37.sh (coq-b37): waits for coq-rr7 -> chain_b37a (copy) -> chain memrchr_proof + rindex ->
  register 10 files -> make_b37 -> assumptions_b37 (expect 378 = 372 + 6).

### 2026-11-18 08:14 CST — strrchr strict chain GREEN
- coq-rr7: memrchr_defs, memrchr_lib, strrchr_defs, strrchr_callees, strrchr_proof all compile (EXIT=0, no
  admits).  strrchr_proof ~10 min (prove_regs_noassign over rr_prog incl. memrchr's NEON block).
- coq-b37 now chaining memrchr_proof + rindex, then register/make/assumptions.
- Next targets after b37: strstr/wcsstr (two-way; big), wcstok, rand_r, getenv, bsearch/lfind/lsearch.

### 2026-11-18 08:51 CST — b37 GREEN: memrchr (scalar), strrchr, rindex in the build
- run_b37 (coq-b37): chain_b37a EXIT=0, chain_b37 CHAIN_EXIT=0, make_b37 BUILD_EXIT=0, assumptions_b37
  ASSUM_EXIT=0: 378 Print Assumptions = 30 closed + 348 with only functional_extensionality_dep (expected 378).
- SOLVED: memrchr (scalar path; NEON block path excluded by precondition n <= 14 \/ (s+n) mod 16 <> 0),
  strrchr (strlen transfer + GrokKeep X19 + memrchr at level 1; k = strlen in framed memory), rindex (tail call).
- OPEN: memrchr NEON block path (tbl/zip/cmeq/umaxp; needs vector semantics lemmas) — lifts strrchr's restriction too.
- Lessons: (1) destruct_inv drops `Inv False` cases itself; (2) parameterise a reusable invariant family by its
  level and by the values the caller needs preserved (X19/X29) so a caller can embed it verbatim; (3) instantiate
  callee families with an opaque n (not k+1) so psimpl's normal forms match the callee's closers;
  (4) prove_regs_noassign over NEON-heavy code costs ~8-10 min per file.
- Next: rand_r (parked: tempering spec vs psimpl form), wcstok, getenv, lfind/lsearch/bsearch (indirect calls).

## 2026-11-18 08:58 CST — getenv started (scratch/b42)
- gv.v (prog/frame/invs family, levels strlen0/strchrnul1/strncmp2/getenv3) and gvc.v (strchrnul/strncmp transfer lemmas into getenv) compile.
- Now probing main theorem (gv2.v): entry → strchrnul call, loop → strncmp call.

## 2026-11-18 09:17 CST — getenv probe (scratch/b42)
- Frame layout confirmed by stepping; strchrnul call (level 1) transfers cleanly, post-call 4 exits + loop entry reached.
- env_entry/gv_match restated with unwrapped `E + 8*j` / `e + l` (psimpl drops mod in getmem addresses).
- gvl.v (scan_unique, gv_rd frame reads, skip_succ, msub32 strncmp-result lemmas, gv_bools) green.
- Lesson: `try reflexivity` on unrewritten `gv_M Ⓠ[..] = x` goals → coqc OOM (conversion unfolds setmem); use syntactic `srefl`.

## 2026-11-18 09:52 CST — resumed after ~09:40 cutoff; getenv split into case files
- No coq-* units were running at resume; no b38 build yet (last green build: b37, 378 Prints).
- gv2 monolithic probe: entry case fully closes (post exits + loop entry j=0); whole-proof run OOMs (8 GB) in the loop/strncmp branch.
- Split per lesson from strlcpy: scratch/b42/gve.v (entry case lemma), gvp.v (loop case lemma), main theorem to dispatch.
- Lessons: set M := gv_M … and clearbody after stepping (keeps conversion cheap); closers via exact/refine conj chains, not try reflexivity/rewrite.

## 2026-11-18 10:30 CST — getenv proved in scratch; b38 (register + make + assumptions) launched
- getenv_partial_correctness (gv_post at RET: frame restored, X0 = 0 with reason, or first matching entry + L+1) green in scratch/b42 (all Qed).
- Final files: proofs/getenv_{defs,callees,lib,vc_ret1,vc_entry,vc_ret2,vc_post2pre,vc_post2,vc_loop,proof,frame}.v, headers/getenv.txt; unit coq-b38 (build_logs/run_b38.sh), expect 378 + 4 = 382 Prints.
- Lessons (kernel/elaboration memory):
  - eapply callee lemma with explicit params; `first [eassumption|reflexivity]` with evar params unified against getmem-heavy hyps → OOM.
  - Ltac non-linear `?a = ?a` match goes through conversion; use constr_eq-based sreflexivity/sassumption.
  - Qed OOM from destruct_inv on a family instantiated with getmem-valued params (q, k19): prove the postcondition shape once with generic params (getenv_vc_post2pre.gvq_pre) and `apply` it.
  - Same-family proof for differing callee params: lemma gv_sf (reflexivity with variables) instead of reflexivity on concrete terms.
  - Split stepping after each call return into its own lemma (vc_ret1/vc_ret2): entry case went from 9.5 GB peak to fitting in 8 GB.

## 2026-11-18 10:35 CST — resumed after ~10:30 cutoff; b38 chain green
- coq-b38b running (relaunched once at 10:29 after getenv_frame.v missed `From Grok.lib Require Import GrokCommon`); chain_b38: all 12 getenv files CHAIN_EXIT=0 under 8 GB. Full make + assumptions in progress.
- Next: wcstok (strtok analogue: calls wcsspn 0x15fe6c, wcscspn 0x15fb44, both proved; port strtok_{defs,callees,join,proof} structure).

## 2026-11-18 10:52 CST — b38 green: getenv landed (382 Prints)
- make BUILD_EXIT=0, make assumptions ASSUM_EXIT=0: 382 Print Assumptions = 31 closed + 351 functional_extensionality_dep only; no admits.
- New: getenv_partial_correctness, getenv_preserves_other_callee_saved, strchrnul_correct_in_getenv, strncmp_correct_in_getenv.
- Solved: getenv (full spec incl. first-match, NULL env, empty name, name containing '=').
- wcstok plan: wcsspn and wcscspn both call wcschr whose loop head 0x15fae0 has different invariants in the two proofs, so a single caller family cannot equal both (GrokCall needs I2 = I1 on callee code).
  New lib/GrokWeaken.v (satisfies_all_weaken: same invariant points, each I1 invariant implies the I2 one) lets the caller use the disjunction at 0x15fae0; transfer = weaken then GrokCall. Registered in _CoqProject, compiled.
- Next: wcstok defs (frame 48 bytes: x29/x30, x19/x20, x21/x22; static state is the caller's `wchar_t **p` in X2/X21, not a global), callee transfers at levels (wcschr 0 via wcsspn/wcscspn 1, wcslen 0), main proof split per call return as for getenv.

## 2026-11-18 11:06 CST — wcstok: callee transfers done (scratch-compiled)
- New lib/GrokExits.v (satisfies_all_xa: change the exit predicate when it agrees on the program's code heads) and lib/GrokCall2.v (satisfies_all_transfer2: GrokCall without XPIN, SUP' unconditional). Both registered in _CoqProject after GrokWeaken.
- Design: wcsspn and wcscspn both at level 1 (level-1 exits = feb8, fbcc, fc34); wcstok at level 2. Caller invs delegate to the callee invs (as in getenv), with Inv 1 (spn ∨ (cspn ∧ X22 kept)) at 0x15fae0.
  Chain per callee: original proof → xa (exits) → keepl X22 (wcscspn only) → weaken → transfer2.
- lifted/wcstok_armv8.v, proofs/wcstok_defs.v, proofs/wcstok_callees.v (wcsspn_correct_in_wcstok, wcscspn_correct_in_wcstok) compile under 8 GB (13 s).
- Next: VCs (entry incl. s=NULL → *p, after wcsspn, after wcscspn) and the main theorem with header.

## 2026-11-18 11:50 CST — resumed after ~11:40 cutoff; wcstok proved in scratch, b39 launched
- No units were running except my own coq-b44p3 (wcstok_proof/frame check; finished). Header fix: "(*" inside header text opens a nested Rocq comment — wrote "( *p" instead.
- All wcstok files compile individually under 8 GB (largest: vc_cspn 48 s, vc_entry 44 s, vc_spn 29 s):
  wcstok_defs, _callees, _lib (frame reads, memory agreement below sp-96, callee preconditions), _vc_cspn (after wcscspn), _vc_postq (post shapes; phase param ph rules out the other callee's RET), _vc_postc, _vc_spn (after wcsspn, calls wcscspn), _vc_posts (wcsspn call + post), _vc_entry (s==NULL → *p), _proof (header headers/wcstok.txt), _frame (X23–X28, Z8–Z15).
- Lesson: a shared helper (wcschr) at the same level forces both callees' exits into one level; GrokExits + a phase parameter make the transfer and the post case split work without re-proving callees.
- coq-b39 (build_logs/run_b39.sh): chain, register, make, make assumptions. Expect 386 Prints.

## 2026-11-18 12:08 CST — b39 green: wcstok landed (386 Prints)
- chain_b39 CHAIN_EXIT=0, make BUILD_EXIT=0, make assumptions ASSUM_EXIT=0: 386 Print Assumptions = 32 closed + 354 functional_extensionality_dep only; no admits.
- New: wcstok_partial_correctness (s / NULL→*p, NULL *p, empty remainder → *p=0, token with terminator or delimiter overwritten and *p advanced), wcstok_preserves_other_callee_saved, wcsspn_correct_in_wcstok, wcscspn_correct_in_wcstok. New lib: GrokExits, GrokCall2 (with GrokWeaken).
- Solved: wcstok.
- Next: bsearch/lfind/lsearch need a contract for the indirect comparator (blr): plan an abstract callee spec (assume comparator returns with callee-saved regs/frame intact) — open design question; otherwise strstr/wcsstr or strdup (malloc call).

### 12:21 CST — CHECKPOINT (stopping point requested): lfind comparator contract in progress
- Build state: last full build b39 (12:07 CST) green, make assumptions 386 Prints (32 closed + 354 fe_dep).
  Nothing registered since; _CoqProject and proofs/Assumptions.v reference no unfinished file. No coq-* units running.
- New, compiled, NOT registered: lib/GrokAbsProg.v (ptot, effinv_sub, getpre_tot, getpost_tot, Ltac sub_here/sub_step):
  stepping a caller's code inside an abstract `prog` (needed because the comparator lives in prog).
- lfind WIP moved to scratch/lfind_wip/{lifted,proofs}/ (all three compile when placed back in lifted/ and proofs/):
  - lfind_defs.v: lf_frame, lf_elt, lf_skip, cmp_ok, lf_cmp_invs, lf_cmp_contract (the comparator contract, a theorem
    HYPOTHESIS: entered at cmp with X30=0x151540 it reaches 0x151540 with cmp_ok = SP, memory, X19-X29 preserved and
    X0 mod 2^32 = C X0 X1; never passes lfind's cut points), lf_pre, invs (0x1514ec entry, 0x151528 loop, 0x151564 post,
    0x151540 Post 0 cmp_ok C s0).
  - lfind_lib.v: lf_invs0_eq / lf_exits0_eq, lf_callee (contract -> callee satisfies_all in lfind's family, via
    satisfies_all_xa + satisfies_all_weaken), lf_postq (comparator post shape via getpost_tot + destruct_inv). Proved.
  - lfind_vc.v: lf_rd, lf_elt_succ, lf_n_lt, lf_skip_succ, lf_after_call (0x151540 -> loop head with i+1 or found post). Proved.
- RESUME POINT: move scratch/lfind_wip files back to lifted/ and proofs/; then in lfind_vc.v add
  (1) lf_loop: at 0x151528, `do 12 try sub_step P`; b.eq branch -> post with X0=0 (derive i = n from the flag hyp and i<=n);
      call branch -> `apply (perform_call 0 1 eq_refl (invs .. s0) (invs .. s2))` with CALLEE = lf_callee (X30 by reflexivity),
      SF = reflexivity, POST = lf_postq then lf_after_call (rewrite cmp_ok equalities; reflexivity).
  (2) lf_entry: steps to 0x151528 with i=0 (base<2^64 from MDL; X22 via memsimp with nelp+8 <= sp-80; sp ⊖ 80 via msub_small).
  Then proofs/lfind_proof.v (header headers/lfind.txt, theorem with P: lfind_armv8 ⊆2 prog, CMP: lf_cmp_contract prog cmp C,
  prove_invs: base via sub_here P, INV via getpre_tot + destruct_inv). Register GrokAbsProg + lfind files, Assumptions Prints,
  run_b40 via systemd. Then bsearch / lsearch same pattern.
- Lessons: inside lazymatch patterns, local names (i, size, sp) were rejected ("reference not found"); use `_`/?x patterns.
  `80 ⊕ (sp-80) = sp` needs `rewrite N.mod_small by L64; L64`.
