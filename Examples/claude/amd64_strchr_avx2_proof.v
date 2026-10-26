(* strchr -- AVX2 implementation (__strchr_avx2)

   SEMANTICS
   ---------
   strchr(s, c) returns a pointer to the first byte of s equal to
   (unsigned char) c, or NULL if the terminating NUL comes first; for c = 0
   it returns a pointer to the terminator.  On AVX2 machines glibc's IFUNC
   resolver selects __strchr_avx2 (in our Firefox profile it is the most-used
   strchr variant).  It broadcasts c to all 32 bytes of YMM0 and looks for
   the first "hit", a byte that is either c or 0:
   * unless s is within 32 bytes of the end of a 4 KiB page, it checks the
     32 bytes at s: VPCMPEQB with the broadcast c and with zero, VPOR, then
     VPMOVMSKB and TZCNT; near a page end it checks the aligned block that
     contains s and shifts the mask right by s mod 32 (SARX);
   * then it checks the next four aligned 32-byte blocks one by one;
   * then it loops over aligned 128-byte blocks: for each vector x it computes
     VPMINUB(x, x XOR c), whose bytes are zero exactly at the hits, combines
     the four with VPMINUB, and compares with zero once;
   * at the first hit it compares the byte with c: equal gives its address,
     otherwise (it is the terminator) NULL.
   As for strlen, it reads past the end of the string within the page, and
   Picinae needs no page argument.

   SPECIFICATION (man 3 strchr, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strchr(const char *s, int c);

     DESCRIPTION
            The  strchr() function returns a pointer to the first occurrence of the
            character c in the string s.

            Here "character" means "byte"; these functions do not work with wide or
            multibyte characters.

     RETURN VALUE
            The strchr() and strrchr() functions return a pointer  to  the  matched
            character  or NULL if the character is not found.  The terminating null
            byte is considered part of the string, so that if  c  is  specified  as
            '\0', these functions return a pointer to the terminator.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            __strchr_avx2 at 0x29d200 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            canonical temporaries, entry rebased to 0; see strchr_avx2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (only the low byte c8 = c mod 256 matters);
            m = memory on entry.  K is the index of the first hit: the bytes
            s+0 .. s+K-1 are neither 0 nor c8, and the byte at s+K is 0 or c8
            (fhit m s c8 K; every NUL-terminated string has one, see
            fhit_of_slen).  s + K < 2^64.
   Output:  On return, RAX = s + K if the byte at s+K is c8, and 0 (NULL)
            otherwise; RSP is unchanged.  strchr writes no memory.
 *)

Require Import Picinae_amd64.
Require Import strchr_avx2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring amd64_simd amd64_avx2 amd64_strlen_avx2_proof.
Import ListNotations.
Open Scope N.

Theorem strchr_avx2_nwc: forall s2 s1, strchr_avx2_amd64 s1 = strchr_avx2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strchr_avx2_welltyped: welltyped_prog x64typctx strchr_avx2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strchr_avx2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strchr_avx2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Theorem strchr_avx2_preserves_memory:
  forall_endstates strchr_avx2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(** * Hits *)

Definition hitb (c b:N) := (b =? 0) || (b =? c).

Definition fhit (m:memory) p c K :=
  (forall k, k < K -> hitb c (m Ⓑ[p ⊕ k]) = false) /\ hitb c (m Ⓑ[p ⊕ K]) = true.

(* A NUL-terminated string has a first hit, at or before its terminator. *)
Lemma fhit_of_slen: forall m p L c, slen m p L -> exists K, K <= L /\ fhit m p c K.
Proof.
  intros m p L c [NZ Z].
  assert (EX: forall n, n <= L -> (forall k, k < n -> hitb c (m Ⓑ[p ⊕ k]) = false) \/
                                  exists K, K < n /\ fhit m p c K).
  { induction n as [|n IH] using N.peano_ind; intro N1.
    - left. intros k K. lia.
    - destruct (IH ltac:(lia)) as [H|H].
      + destruct (hitb c (m Ⓑ[p ⊕ n])) eqn:B.
        * right. exists n. split. lia. split. exact H. exact B.
        * left. intros k K. destruct (N.eq_dec k n) as [->|NE]. exact B. apply H. lia.
      + right. destruct H as [K [KL F]]. exists K. split. lia. exact F. }
  destruct (EX L (N.le_refl _)) as [H|[K [KL F]]].
  - exists L. split. lia. split. exact H. unfold hitb. rewrite Z. reflexivity.
  - exists K. split. lia. exact F.
Qed.

(* r is the hit mask of the 32 bytes at a *)
Definition hspec (r:N) (m:memory) a c :=
  r < 2^32 /\ forall j, j < 32 -> N.testbit r j = hitb c (m Ⓑ[j + a]).

Lemma h_none: forall r m a c, hspec r m a c -> r = 0 -> forall j, j < 32 -> hitb c (m Ⓑ[j + a]) = false.
Proof. intros r m a c [_ H] R0 j J. rewrite <- (H j J), R0. apply N.bits_0. Qed.

Lemma h_first: forall r m a c, hspec r m a c -> r <> 0 ->
  let t := fst (N.iter 33 (tz_step 32) (0, r)) in
  t < 32 /\ hitb c (m Ⓑ[t + a]) = true /\ forall j, j < t -> hitb c (m Ⓑ[j + a]) = false.
Proof.
  intros r m a c [RB H] NZ t.
  destruct (tz_result 32 r ltac:(lia) RB) as [_ T]. destruct (T NZ) as [T32 [TB TL]].
  change (N.succ 32) with 33 in T32, TB, TL. fold t in T32, TB, TL.
  split. exact T32. split.
  - rewrite <- (H t T32). exact TB.
  - intros j J. rewrite <- (H j ltac:(lia)). apply TL, J.
Qed.

Lemma fh_none: forall m p c K b a r, fhit m p c K -> b <= K -> a mod 2^64 = (p + b) mod 2^64 ->
  hspec r m a c -> r = 0 -> b + 32 <= K.
Proof.
  intros m p c K b a r [NH H] BK A HS R0. destruct (N.le_gt_cases (b + 32) K) as [L|L]. exact L.
  exfalso. pose proof (h_none r m a c HS R0 (K - b) ltac:(lia)) as F.
  rewrite (byte_rebase m a p b _ A) in F. replace (b + (K - b)) with K in F by lia. congruence.
Qed.

Lemma fh_hit: forall m p c K b a r, fhit m p c K -> b <= K -> a mod 2^64 = (p + b) mod 2^64 ->
  hspec r m a c -> r <> 0 ->
  K = b + fst (N.iter 33 (tz_step 32) (0, r)) /\ fst (N.iter 33 (tz_step 32) (0, r)) < 32.
Proof.
  intros m p c K b a r [NH H] BK A HS NZ.
  destruct (h_first r m a c HS NZ) as [T32 [TB TL]].
  set (t := fst (N.iter 33 (tz_step 32) (0, r))) in *.
  split; [|exact T32].
  rewrite (byte_rebase m a p b _ A) in TB.
  destruct (N.lt_trichotomy K (b + t)) as [LT|[EQ|GT]].
  - exfalso. pose proof (TL (K - b) ltac:(lia)) as F. rewrite (byte_rebase m a p b _ A) in F.
    replace (b + (K - b)) with K in F by lia. congruence.
  - exact EQ.
  - exfalso. rewrite (NH (b + t) GT) in TB. discriminate.
Qed.

(** * Hit masks from the SIMD values *)

Lemma byte_getmem: forall (m:memory) a i, i < 32 -> byte (getmem 64 LittleE 32 m a) i = m Ⓑ[i + a].
Proof.
  intros m a i I. unfold byte. rewrite byte_of_getmem by exact I.
  rewrite getmem_mod_l, N.add_comm. reflexivity.
Qed.

Lemma bit7_if: forall b:bool, N.testbit (if b then 255 else 0) 7 = b.
Proof. intros [|]; reflexivity. Qed.

Lemma testbit_byte7: forall y j, N.testbit y (8*j+7) = N.testbit (byte y j) 7.
Proof. intros y j. rewrite byte_testbit. change (7 <? 8) with true. cbn [andb]. f_equal. lia. Qed.

(* First and four-block checks: VPCMPEQB with c and with zero, VPOR, VPMOVMSKB. *)
Lemma hmask: forall y1 y2 B r (m:memory) a c,
  cmpeq_spec 32 y1 B (getmem 64 LittleE 32 m a) ->
  cmpeq_spec 32 y2 0 (getmem 64 LittleE 32 m a) ->
  (forall i, i < 32 -> byte B i = c) ->
  movmsk_spec 32 r ((y2 .| y1) mod 2^256) -> hspec r m a c.
Proof.
  intros y1 y2 B r m a c C1 C2 BC [RB M]. split. exact RB.
  intros j J. rewrite (M j J), Nmod_pow2_bits.
  replace (8 * j + 7 <? 256) with true by (symmetry; apply N.ltb_lt; lia). cbn [andb].
  rewrite N.lor_spec, !testbit_byte7, (C1 j J), (C2 j J), !bit7_if.
  rewrite (BC j J), byte_getmem by exact J.
  replace (byte 0 j) with 0 by (unfold byte, xbits; rewrite N.shiftr_0_l; reflexivity).
  unfold hitb. rewrite (N.eqb_sym 0), (N.eqb_sym c). reflexivity.
Qed.

(* Loop: VPMINUB(x, x XOR c) is zero exactly at the hits. *)
Lemma byte_lxor: forall a b j, byte (N.lxor a b) j = N.lxor (byte a j) (byte b j).
Proof.
  intros a b j. apply N.bits_inj. intro i. rewrite N.lxor_spec, !byte_testbit, N.lxor_spec.
  destruct (i <? 8); reflexivity.
Qed.

Lemma lxor_eq0: forall a b, N.lxor a b = 0 <-> a = b.
Proof.
  intros a b. split; intro H.
  - apply N.lxor_eq, H.
  - subst. apply N.lxor_nilpotent.
Qed.

Lemma loop_zb: forall w B x (m:memory) a c,
  (forall i, i < 32 -> byte B i = c) ->
  x = getmem 64 LittleE 32 m a ->
  pmin_spec 32 w x (N.lxor B x) -> forall j, j < 32 -> zbyte w j = hitb c (m Ⓑ[j + a]).
Proof.
  intros w B x m a c BC X PM j J. unfold zbyte, hitb. rewrite (PM j J), byte_lxor, (BC j J).
  subst x. rewrite byte_getmem by exact J. set (b := m Ⓑ[j + a]).
  destruct (N.eqb_spec b 0) as [->|B0].
  - rewrite N.min_l by lia. reflexivity.
  - destruct (N.eqb_spec b c) as [->|BNC].
    + rewrite N.lxor_nilpotent, N.min_r by lia. reflexivity.
    + cbn [orb]. apply N.eqb_neq. intro H.
      destruct (N.min_spec b (N.lxor c b)) as [[_ E]|[_ E]]; rewrite E in H;
        [contradiction | apply BNC; symmetry; exact (N.lxor_eq _ _ H)].
Qed.

(* Compare with zero: a VPCMPEQB against the zero register is a cmpz. *)
Lemma cmpeq0_cmpz: forall y x, cmpeq_spec 32 y 0 x -> cmpz_spec 32 y x.
Proof.
  intros y x C i I. rewrite (C i I). unfold zbyte.
  replace (byte 0 i) with 0 by (unfold byte, xbits; rewrite N.shiftr_0_l; reflexivity).
  rewrite N.eqb_sym. reflexivity.
Qed.

Lemma msk_hspec: forall r w (m:memory) a c, msk_spec 32 r w -> r < 2^32 ->
  (forall j, j < 32 -> zbyte w j = hitb c (m Ⓑ[j + a])) -> hspec r m a c.
Proof. intros r w m a c M RB Z. split. exact RB. intros j J. rewrite (M j J). apply Z, J. Qed.

Definition bcast (y c8:N) := forall i, i < 32 -> byte y i = c8.

Lemma mod32_8: forall c, (c mod 2^32) mod 2^8 = c mod 2^8.
Proof.
  intro c. change (2^32) with (256 * 16777216). rewrite N.mod_mul_r, N.mul_comm, N.mod_add by discriminate.
  apply N.mod_mod. discriminate.
Qed.

(* Turn the facts of the blocks checked so far into hit masks. *)
Ltac sc_norm MEM P Z9 :=
  repeat match goal with M: movmsk_spec _ _ _ |- _ => progress upd_in regs_not_temp M end;
  repeat match goal with C: cmpeq_spec _ _ _ _ |- _ => progress upd_in regs_not_temp C end;
  repeat match goal with C: cmpeq_spec _ _ _ _ |- _ => progress rewrite ?MEM, ?P, ?Z9 in C end;
  repeat match goal with
    M: movmsk_spec 32 ?r ((?y2 .| ?y1) mod 2^256), C1: cmpeq_spec 32 ?y1 _ _, C2: cmpeq_spec 32 ?y2 0 _,
    BB: bcast _ _ |- _ =>
      let HS := fresh "HS" in
      pose proof (hmask _ _ _ _ _ _ _ C1 C2 BB M) as HS; clear M C1 C2
  end;
  repeat match goal with H: hspec ?r _ _ _, B: (?r mod 2^32 =? 0) = _ |- _ =>
    rewrite (N.mod_small r) in B by exact (proj1 H) end.

(* Byte reads at addresses equal modulo 2^64. *)
Lemma byte_addr: forall (m:memory) x y, x mod 2^64 = y mod 2^64 -> m Ⓑ[x] = m Ⓑ[y].
Proof.
  intros m x y E. transitivity (m Ⓑ[x mod 2^64]). symmetry. apply getmem_mod_l.
  rewrite E. apply getmem_mod_l.
Qed.

(* An exit after TZCNT found the first hit at offset b + t: the byte there is
   compared with c (BC0), and the result is its address or NULL. *)
Lemma sc_result: forall (m:memory) p K c8 b t x base,
  K = b + t -> x mod 2^64 = (p + K) mod 2^64 -> base mod 2^64 = (p + b) mod 2^64 ->
  forall bv, (c8 =? m Ⓑ[x]) = bv ->
  (if bv then (t + base) mod 2^64 else 0) = (if m Ⓑ[p + K] =? c8 then (p + K) mod 2^64 else 0).
Proof.
  intros m p K c8 b t x base HK X B bv BV. subst bv.
  rewrite (byte_addr m x (p + K) X), N.eqb_sym.
  destruct (_ =? _); [|reflexivity].
  rewrite <- N.add_mod_idemp_r, B, N.add_mod_idemp_r by discriminate. f_equal. lia.
Qed.

(* Rounding down to a multiple of 2^k. *)
Lemma land_align: forall x k, x < 2^64 -> k <= 64 ->
  x .& N.ldiff (N.ones 64) (N.ones k) = x - x mod 2^k.
Proof.
  intros x k X K.
  assert (E: x - x mod 2^k = x >> k << k).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2.
    pose proof (N.div_mod x (2^k) (N.pow_nonzero 2 k ltac:(discriminate))). lia. }
  rewrite E. apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i k).
  - rewrite (N.ones_spec_low k i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high k i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - k + k) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      apply (bound_hibits_zero 64). exact X. exact H0.
Qed.

(* Close an address congruence: drop inner reductions, unfold p .| 31. *)
Ltac addr_cong p :=
  repeat rewrite N.add_mod_idemp_l by discriminate;
  repeat rewrite N.add_mod_idemp_r by discriminate;
  rewrite ?lor31; f_equal;
  let PM := fresh in let PL := fresh in
  pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL;
  lia.

Lemma none_hs: forall w (m:memory) a c, (forall j, j < 32 -> zbyte w j = false) ->
  (forall j, j < 32 -> zbyte w j = hitb c (m Ⓑ[j + a])) -> hspec 0 m a c.
Proof.
  intros w m a c ZF Z. split. reflexivity. intros j J. rewrite N.bits_0, <- (Z j J). symmetry. apply ZF, J.
Qed.

(* The exit of a hit at string offset K, found at address x: the result. *)
Ltac sc_exit_res p K HK :=
  match goal with H: (_ =? getmem _ _ 1 _ ?x) = _ |- _ =>
    rewrite (byte_addr _ x (p + K)) in H
      by (rewrite HK; rewrite ?N.mod_mod by discriminate; repeat rewrite N.add_mod_idemp_l by discriminate;
          repeat rewrite N.add_mod_idemp_r by discriminate; f_equal; clear; lia);
    rewrite N.eqb_sym in H; rewrite H
  end;
  first [ reflexivity
        | rewrite HK; rewrite ?N.mod_mod by discriminate; repeat rewrite N.add_mod_idemp_l by discriminate;
          repeat rewrite N.add_mod_idemp_r by discriminate; f_equal; clear; lia ].

(* The page-cross block: the hit mask of the aligned block holding p,
   shifted right by p mod 32 with SARX. *)
Lemma sarx_hit: forall m p c K r, fhit m p c K -> p + K < 2^64 ->
  hspec r m (msub 64 (p .| 31) 31) c ->
  let e := ashiftr 32 r (p mod 32) in
  (e = 0 -> 32 - p mod 32 <= K) /\ (e <> 0 -> fst (N.iter 33 (tz_step 32) (0, e)) = K).
Proof.
  intros m p c K r [NH H] NW [RB M] e.
  set (k := p mod 32). assert (KB: k < 32) by (apply N.mod_lt; discriminate).
  assert (KP: k <= p) by (apply N.mod_le; discriminate).
  set (a := msub 64 (p .| 31) 31) in M.
  assert (A: a = p - k).
  { subst a. rewrite lor31. fold k. rewrite msub_sub by lia.
    rewrite N.mod_small; change (2^64) with 18446744073709551616 in *; lia. }
  assert (EB: forall i, i + k < 32 -> N.testbit e i = hitb c (m Ⓑ[p ⊕ (0 + i)])).
  { intros i I. subst e. fold k. rewrite ashiftr_spec. change (N.pred 32) with 31.
    replace (i <? 32) with true by (symmetry; apply N.ltb_lt; lia). rewrite N.min_l by lia.
    cbn [andb]. rewrite (M (i + k) I). f_equal.
    replace (i + k + a) with (i + (k + a)) by lia.
    apply byte_rebase. rewrite A. f_equal. lia. }
  split.
  - intro E0. destruct (N.le_gt_cases (32 - k) K) as [L|L]. exact L.
    exfalso. pose proof (EB K ltac:(lia)) as B. rewrite E0, N.bits_0, N.add_0_l in B.
    rewrite H in B. discriminate.
  - intro NZ. destruct (tz_result 32 e ltac:(lia) (ashiftr32_bound r k)) as [_ T].
    destruct (T NZ) as [T32 [TB TL]]. change (N.succ 32) with 33 in T32, TB, TL.
    set (t := fst (N.iter 33 (tz_step 32) (0, e))) in *.
    assert (TK: t + k < 32).
    { destruct (N.lt_ge_cases (t + k) 32) as [L|L]. exact L. exfalso.
      assert (B31: N.testbit e (31 - k) = N.testbit e t).
      { subst e. fold k. rewrite !ashiftr_spec. change (N.pred 32) with 31.
        rewrite !N.min_r by lia.
        replace (31 - k <? 32) with true by (symmetry; apply N.ltb_lt; lia).
        replace (t <? 32) with true by (symmetry; apply N.ltb_lt; lia). reflexivity. }
      rewrite (TL (31 - k) ltac:(lia)), TB in B31. discriminate. }
    rewrite (EB t TK), N.add_0_l in TB.
    destruct (N.lt_trichotomy t K) as [LT|[EQ|GT]].
    + rewrite (NH t LT) in TB. discriminate.
    + exact EQ.
    + exfalso. pose proof (TL K GT) as B. rewrite (EB K ltac:(lia)), N.add_0_l, H in B. discriminate.
Qed.

(** * Specification *)

Definition sc_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 82 | 116 | 122 | 147 | 180 | 212 | 492 | 516 | 522 | 548 | 624 => true
  | _ => false
  end | _ => false end.

Definition sc_post (m p c K rsp:N) (s':store) :=
  s' R_RAX = (if m Ⓑ[p ⊕ K] =? c mod 2^8 then p ⊕ K else 0) /\ s' R_RSP = rsp /\ s' V_MEM64 = m.

Definition sc_invs (m p c K rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RSI = c /\ st R_RSP = rsp)
  (* the first, unaligned block *)
  | 36 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RSI = c /\ st R_RSP = rsp /\
                bcast (st R_YMM0) (c mod 2^8) /\ st R_YMM9 = 0)
  (* the four aligned blocks *)
  | 228 => Some (st V_MEM64 = m /\ st R_RDI = p .| 31 /\ st R_RSI = c /\ st R_RSP = rsp /\
                 bcast (st R_YMM0) (c mod 2^8) /\ st R_YMM9 = 0 /\ 32 - p mod 32 <= K)
  (* the 128-byte loop: no hit in the o bytes before RDI *)
  | 352 => Some (exists o, 0 < o <= K /\ st V_MEM64 = m /\ st R_RDI = p + o /\ st R_RSI = c /\
                 st R_RSP = rsp /\ bcast (st R_YMM0) (c mod 2^8) /\ st R_YMM9 = 0)
  (* the page-cross entry *)
  | 560 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RSI = c /\ st R_RSP = rsp /\
                 bcast (st R_YMM0) (c mod 2^8) /\ st R_YMM9 = 0)
  | 82 | 116 | 122 | 147 | 180 | 212 | 492 | 516 | 522 | 548 | 624 => Some (sc_post m p c K rsp st)
  | _ => None
  end | _ => None end.

Ltac cmpeq_rr := simd_step ltac:(fun XS =>
  apply vpcmpeqb_rr_exec in XS; [| reflexivity];
  let CE := fresh "CE" in let y := fresh "y" in
  destruct XS as [-> [y [CE ->]]]).

Ltac bcast0 := simd_step ltac:(fun XS =>
  apply vpbroadcastb0_exec in XS;
  let BB := fresh "BB" in let y := fresh "y" in
  destruct XS as [-> [y [BB ->]]]).

Ltac sc_simd :=
  lazymatch goal with |- nextinv _ _ _ _ ((Addr ?a0, _) :: _) =>
  let a := eval vm_compute in a0 in
  lazymatch a with
  | 15 => bcast0
  | 40 => cmpeq_rr | 45 => cmpeq_rr | 233 => cmpeq_rr | 238 => cmpeq_rr
  | 260 => cmpeq_rr | 265 => cmpeq_rr | 287 => cmpeq_rr | 292 => cmpeq_rr
  | 314 => cmpeq_rr | 319 => cmpeq_rr | 416 => cmpeq_rr | 432 => cmpeq_rr
  | 444 => cmpeq_rr | 456 => cmpeq_rr | 572 => cmpeq_rr | 577 => cmpeq_rr
  | 54 => movmsk | 247 => movmsk | 274 => movmsk | 301 => movmsk | 328 => movmsk
  | 420 => movmsk | 436 => movmsk | 448 => movmsk | 460 => movmsk | 586 => movmsk
  | 388 => pmin_reg | 392 => pmin_reg | 396 => pmin_reg | 400 => pmin_reg
  | 404 => pmin_reg | 408 => pmin_reg | 412 => pmin_reg
  | 66 => tz32 | 96 => tz32 | 128 => tz32 | 160 => tz32 | 192 => tz32
  | 496 => tz32 | 528 => tz32 | 603 => tz32
  | 471 => tz64
  end end.
Ltac sc_run := repeat (first [sc_simd | x64_step]).

Theorem strchr_avx2_correct:
  forall st t s' x' m p c K rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (P: st R_RDI = p) (C: st R_RSI = c) (RSP: st R_RSP = rsp)
         (FH: fhit m p (c mod 2^8) K) (NW: p + K < 2^64),
  satisfies_all strchr_avx2_amd64 (sc_invs m p c K rsp) sc_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_avx2_welltyped. intro MDL1.
  clear - PRE MDL1 FH NW. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [P [C RSP]]].
    sc_run.
    all: upd_in regs_not_temp BB; rewrite mod32_8 in BB.
    all: repeat split; try reflexivity; try assumption.
  - (* first block *)
    destruct PRE as [MEM [P [C [RSP [B0 Z9]]]]].
    sc_run.
    all: sc_norm MEM P Z9.
    + (* no hit in the first 32 bytes *)
      apply N.eqb_eq in BC.
      pose proof (fh_none m p _ K 0 p r FH (N.le_0_l _) ltac:(rewrite N.add_0_r; reflexivity) HS BC).
      repeat split; try assumption; try reflexivity.
      pose proof (N.mod_lt p 32 ltac:(discriminate)). clear - H H0. lia.
    + (* the first hit is c *)
      apply N.eqb_neq in BC. upd regs_not_temp.
      unfold xbits in *. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r) in * by exact (proj1 HS).
      destruct (fh_hit m p _ K 0 p r FH (N.le_0_l _) ltac:(rewrite N.add_0_r; reflexivity) HS BC) as [HK HT].
      split; [|split; reflexivity || assumption].
      rewrite N.add_0_l in HK. subst K.
      pose proof (sc_result m p _ _ 0 _ _ p eq_refl eq_refl ltac:(rewrite N.add_0_r; reflexivity) _ BC0) as R.
      cbv beta iota in R. exact R.
    + (* the first hit is the terminator *)
      apply N.eqb_neq in BC. upd_in regs_not_temp BC0.
      unfold xbits in BC0. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r) in BC0 by exact (proj1 HS).
      destruct (fh_hit m p _ K 0 p r FH (N.le_0_l _) ltac:(rewrite N.add_0_r; reflexivity) HS BC) as [HK HT].
      split; [|split; reflexivity || assumption].
      rewrite N.add_0_l in HK. subst K.
      pose proof (sc_result m p _ _ 0 _ _ p eq_refl eq_refl ltac:(rewrite N.add_0_r; reflexivity) _ BC0) as R.
      cbv beta iota in R. exact R.
  - (* four aligned blocks *)
    destruct PRE as [MEM [P [C [RSP [B0 [Z9 C0]]]]]].
    sc_run.
    all: sc_norm MEM P Z9.
    + (* no hit in the four blocks: enter the loop *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      assert (N33: 31 - p mod 32 + 33 + 32 <= K) by (match goal with H: hspec r0 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 33) a r0 FH); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC0] end).
      assert (N65: 31 - p mod 32 + 65 + 32 <= K) by (match goal with H: hspec r1 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 65) a r1 FH); [clear - C0 N1 N33; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC1] end).
      assert (N97: 31 - p mod 32 + 97 + 32 <= K) by (match goal with H: hspec r2 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 97) a r2 FH); [clear - C0 N1 N33 N65; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC2] end).
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      change 18446744073709551488 with (N.ldiff (N.ones 64) (N.ones 7)).
      rewrite land_align by (rewrite ?lor31; change (2^64) with 18446744073709551616; clear - NW N97 PM PL; lia).
      rewrite lor31. change (2^7) with 128.
      set (v := 129 + (p - p mod 32 + 31)).
      pose proof (N.mod_lt v 128 ltac:(discriminate)) as VM; pose proof (N.mod_le v 128 ltac:(discriminate)) as VL.
      exists (v - v mod 128 - p).
      split. subst v; clear - N97 PM PL VM VL; lia.
      split. reflexivity.
      split. subst v; clear - PM PL VM VL; lia.
      repeat split; assumption.
    + (* the first hit is in block 3 and is c *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      assert (N33: 31 - p mod 32 + 33 + 32 <= K) by (match goal with H: hspec r0 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 33) a r0 FH); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC0] end).
      assert (N65: 31 - p mod 32 + 65 + 32 <= K) by (match goal with H: hspec r1 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 65) a r1 FH); [clear - C0 N1 N33; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC1] end).
      apply N.eqb_neq in BC2.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r2 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 97) a r2 FH ltac:(clear - C0 N1 N33 N65 PM; lia) ltac:(addr_cong p) H BC2) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r2) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      addr_cong p.
    + (* the first hit is in block 3 and is the terminator *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      assert (N33: 31 - p mod 32 + 33 + 32 <= K) by (match goal with H: hspec r0 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 33) a r0 FH); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC0] end).
      assert (N65: 31 - p mod 32 + 65 + 32 <= K) by (match goal with H: hspec r1 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 65) a r1 FH); [clear - C0 N1 N33; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC1] end).
      apply N.eqb_neq in BC2.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r2 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 97) a r2 FH ltac:(clear - C0 N1 N33 N65 PM; lia) ltac:(addr_cong p) H BC2) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r2) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      reflexivity.
    + (* the first hit is in block 2 and is c *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      assert (N33: 31 - p mod 32 + 33 + 32 <= K) by (match goal with H: hspec r0 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 33) a r0 FH); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC0] end).
      apply N.eqb_neq in BC1.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r1 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 65) a r1 FH ltac:(clear - C0 N1 N33 PM; lia) ltac:(addr_cong p) H BC1) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r1) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      addr_cong p.
    + (* the first hit is in block 2 and is the terminator *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      assert (N33: 31 - p mod 32 + 33 + 32 <= K) by (match goal with H: hspec r0 _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 33) a r0 FH); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC0] end).
      apply N.eqb_neq in BC1.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r1 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 65) a r1 FH ltac:(clear - C0 N1 N33 PM; lia) ltac:(addr_cong p) H BC1) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r1) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      reflexivity.
    + (* the first hit is in block 1 and is c *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      apply N.eqb_neq in BC0.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r0 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 33) a r0 FH ltac:(clear - C0 N1 PM; lia) ltac:(addr_cong p) H BC0) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r0) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      addr_cong p.
    + (* the first hit is in block 1 and is the terminator *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= K) by (match goal with H: hspec r _ ?a _ |- _ => apply (fh_none m p _ K (31 - p mod 32 + 1) a r FH); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | addr_cong p | exact H | apply N.eqb_eq; exact BC] end).
      apply N.eqb_neq in BC0.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r0 _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 33) a r0 FH ltac:(clear - C0 N1 PM; lia) ltac:(addr_cong p) H BC0) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r0) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      reflexivity.
    + (* the first hit is in block 0 and is c *)
      apply N.eqb_neq in BC.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 1) a r FH ltac:(clear - C0  PM; lia) ltac:(addr_cong p) H BC) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      addr_cong p.
    + (* the first hit is in block 0 and is the terminator *)
      apply N.eqb_neq in BC.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp.
      match goal with H: hspec r _ ?a _ |- _ =>
        destruct (fh_hit m p _ K (31 - p mod 32 + 1) a r FH ltac:(clear - C0  PM; lia) ltac:(addr_cong p) H BC) as [HK HT];
        unfold xbits in *; rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r) in * by exact (proj1 H)
      end.
      split; [|split; reflexivity || assumption].
      match goal with H: (_ =? getmem _ _ 1 m ?x) = _ |- _ =>
        rewrite (byte_addr m x (p + K)) in H by (rewrite HK; addr_cong p); rewrite N.eqb_sym in H; rewrite H
      end.
      reflexivity.

  - (* the 128-byte loop *)
    destruct PRE as [o [O [MEM [P [C [RSP [B0 Z9]]]]]]].
    sc_run.
    all: repeat match goal with H: pmin_spec _ _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: repeat match goal with H: pmin_spec _ _ _ _ |- _ => progress rewrite ?MEM, ?P in H end.
    all: repeat match goal with H: cmpeq_spec _ _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: repeat match goal with H: cmpeq_spec _ _ _ _ |- _ => progress rewrite ?Z9 in H end.
    all: repeat match goal with H: cmpeq_spec 32 _ 0 _ |- _ => apply cmpeq0_cmpz in H end.
    all: blk_norm MEM P.
    (* the hit detector of each block *)
    all: repeat match goal with H: pmin_spec 32 ?w (getmem _ _ 32 ?mm ?a) (N.lxor _ _) |- _ =>
           let Z := fresh "Z" in pose proof (loop_zb _ _ _ mm a _ B0 eq_refl H) as Z; clear H end.
    all: assert (A1: (32 + p + o) mod 2^64 = (p + (o + 32)) mod 2^64) by (f_equal; clear; lia).
    all: assert (A2: (64 + p + o) mod 2^64 = (p + (o + 32 + 32)) mod 2^64) by (f_equal; clear; lia).
    all: assert (A3: (96 + p + o) mod 2^64 = (p + (o + 32 + 32 + 32)) mod 2^64) by (f_equal; clear; lia).
    all: assert (A0: (p + o) mod 2^64 = (p + o) mod 2^64) by reflexivity.
    + (* no hit in the 128 bytes: next iteration *)
      apply N.eqb_eq in BC.
      match goal with M: msk_spec 32 r _ |- _ => pose proof (zb_none _ _ M BC) as ZY5 end.
      destruct (pmin_none _ _ _ PM5 ZY5) as [ZY4 ZY3].
      destruct (pmin_none _ _ _ PM4 ZY4) as [ZW3 ZW2].
      destruct (pmin_none _ _ _ PM3 ZY3) as [ZW1 ZW0].
      pose proof (fh_none m p _ K o _ 0 FH ltac:(clear - O; lia) A0 (none_hs _ _ _ _ ZW0 Z2) eq_refl) as N0.
      pose proof (fh_none m p _ K (o + 32) _ 0 FH N0 A1 (none_hs _ _ _ _ ZW1 Z1) eq_refl) as N1.
      pose proof (fh_none m p _ K (o + 32 + 32) _ 0 FH N1 A2 (none_hs _ _ _ _ ZW2 Z0) eq_refl) as N2.
      pose proof (fh_none m p _ K (o + 32 + 32 + 32) _ 0 FH N2 A3 (none_hs _ _ _ _ ZW3 Z) eq_refl) as N3.
      exists (o + 128).
      split. clear - N3 O. lia.
      split. reflexivity.
      split. { change (2^7) with 128. rewrite N.mod_small. clear; lia. clear - N3 NW. lia. }
      repeat split; assumption.
    + (* the first hit is in block 2 or 3 and is c *)
      apply N.eqb_neq in BC. apply N.eqb_eq in BC0. apply N.eqb_eq in BC1.
      match goal with M: msk_spec 32 r1 _ |- _ => pose proof (zb_none _ _ M BC1) as ZY3 end.
      destruct (pmin_none _ _ _ PM3 ZY3) as [ZW1 ZW0].
      pose proof (fh_none m p _ K o _ 0 FH ltac:(clear - O; lia) A0 (none_hs _ _ _ _ ZW0 Z2) eq_refl) as N0.
      pose proof (fh_none m p _ K (o + 32) _ 0 FH N0 A1 (none_hs _ _ _ _ ZW1 Z1) eq_refl) as N1.
      match goal with M: msk_spec 32 r2 _ |- _ => rename M into M2 end.
      match goal with R: r2 < 4294967296 |- _ => rename R into RX2 end.
      match goal with M: msk_spec 32 r _ |- _ => rename M into MA end.
      match goal with R: r < 4294967296 |- _ => rename R into RXA end.
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end.
      destruct (tz64_split r2 r RX2 RXA BC) as [HE HZ].
      destruct (N.eq_dec r2 0) as [E0|E0].
      * pose proof (zb_none _ _ M2 E0) as ZW2.
        pose proof (fh_none m p _ K (o + 32 + 32) _ 0 FH N1 A2 (none_hs _ _ _ _ ZW2 Z0) eq_refl) as N2.
        pose proof (msk_hspec _ _ m _ _ (msk_drop_r _ _ _ _ (msk_drop_r _ _ _ _ MA PM5 ZY3) PM4 ZW2) RXA Z) as HS3.
        destruct (fh_hit m p _ K (o + 32 + 32 + 32) _ r FH N2 A3 HS3 BC) as [HK HT].
        rewrite (HZ E0) in *.
        split; [|split; reflexivity || assumption].
        sc_exit_res p K HK.
      * pose proof (msk_hspec _ _ m _ _ M2 RX2 Z0) as HS2.
        destruct (fh_hit m p _ K (o + 32 + 32) _ r2 FH N1 A2 HS2 E0) as [HK HT].
        rewrite (HE E0) in *.
        split; [|split; reflexivity || assumption].
        sc_exit_res p K HK.
    + (* the first hit is in block 2 or 3 and is the terminator *)
      apply N.eqb_neq in BC. apply N.eqb_eq in BC0. apply N.eqb_eq in BC1.
      match goal with M: msk_spec 32 r1 _ |- _ => pose proof (zb_none _ _ M BC1) as ZY3 end.
      destruct (pmin_none _ _ _ PM3 ZY3) as [ZW1 ZW0].
      pose proof (fh_none m p _ K o _ 0 FH ltac:(clear - O; lia) A0 (none_hs _ _ _ _ ZW0 Z2) eq_refl) as N0.
      pose proof (fh_none m p _ K (o + 32) _ 0 FH N0 A1 (none_hs _ _ _ _ ZW1 Z1) eq_refl) as N1.
      match goal with M: msk_spec 32 r2 _ |- _ => rename M into M2 end.
      match goal with R: r2 < 4294967296 |- _ => rename R into RX2 end.
      match goal with M: msk_spec 32 r _ |- _ => rename M into MA end.
      match goal with R: r < 4294967296 |- _ => rename R into RXA end.
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end.
      destruct (tz64_split r2 r RX2 RXA BC) as [HE HZ].
      destruct (N.eq_dec r2 0) as [E0|E0].
      * pose proof (zb_none _ _ M2 E0) as ZW2.
        pose proof (fh_none m p _ K (o + 32 + 32) _ 0 FH N1 A2 (none_hs _ _ _ _ ZW2 Z0) eq_refl) as N2.
        pose proof (msk_hspec _ _ m _ _ (msk_drop_r _ _ _ _ (msk_drop_r _ _ _ _ MA PM5 ZY3) PM4 ZW2) RXA Z) as HS3.
        destruct (fh_hit m p _ K (o + 32 + 32 + 32) _ r FH N2 A3 HS3 BC) as [HK HT].
        rewrite (HZ E0) in *.
        split; [|split; reflexivity || assumption].
        sc_exit_res p K HK.
      * pose proof (msk_hspec _ _ m _ _ M2 RX2 Z0) as HS2.
        destruct (fh_hit m p _ K (o + 32 + 32) _ r2 FH N1 A2 HS2 E0) as [HK HT].
        rewrite (HE E0) in *.
        split; [|split; reflexivity || assumption].
        sc_exit_res p K HK.
    + (* the first hit is in block 1 and is c *)
      apply N.eqb_neq in BC1. apply N.eqb_eq in BC0.
      match goal with M: msk_spec 32 r0 _ |- _ => pose proof (zb_none _ _ M BC0) as ZW0 end.
      pose proof (fh_none m p _ K o _ 0 FH ltac:(clear - O; lia) A0 (none_hs _ _ _ _ ZW0 Z2) eq_refl) as N0.
      match goal with M: msk_spec 32 r1 _, R: r1 < 4294967296 |- _ =>
        pose proof (msk_hspec _ _ m _ _ (msk_drop_r _ _ _ _ M PM3 ZW0) R Z1) as HS1 end.
      destruct (fh_hit m p _ K (o + 32) _ r1 FH N0 A1 HS1 BC1) as [HK HT].
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end. unfold xbits in *. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r1) in * by exact (proj1 HS1).
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
    + (* the first hit is in block 1 and is the terminator *)
      apply N.eqb_neq in BC1. apply N.eqb_eq in BC0.
      match goal with M: msk_spec 32 r0 _ |- _ => pose proof (zb_none _ _ M BC0) as ZW0 end.
      pose proof (fh_none m p _ K o _ 0 FH ltac:(clear - O; lia) A0 (none_hs _ _ _ _ ZW0 Z2) eq_refl) as N0.
      match goal with M: msk_spec 32 r1 _, R: r1 < 4294967296 |- _ =>
        pose proof (msk_hspec _ _ m _ _ (msk_drop_r _ _ _ _ M PM3 ZW0) R Z1) as HS1 end.
      destruct (fh_hit m p _ K (o + 32) _ r1 FH N0 A1 HS1 BC1) as [HK HT].
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end. unfold xbits in *. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r1) in * by exact (proj1 HS1).
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
    + (* the first hit is in block 0 and is c *)
      apply N.eqb_neq in BC0.
      match goal with M: msk_spec 32 r0 _, R: r0 < 4294967296 |- _ =>
        pose proof (msk_hspec _ _ m _ _ M R Z2) as HS0 end.
      destruct (fh_hit m p _ K o _ r0 FH ltac:(clear - O; lia) A0 HS0 BC0) as [HK HT].
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end. unfold xbits in *. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r0) in * by exact (proj1 HS0).
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
    + (* the first hit is in block 0 and is the terminator *)
      apply N.eqb_neq in BC0.
      match goal with M: msk_spec 32 r0 _, R: r0 < 4294967296 |- _ =>
        pose proof (msk_hspec _ _ m _ _ M R Z2) as HS0 end.
      destruct (fh_hit m p _ K o _ r0 FH ltac:(clear - O; lia) A0 HS0 BC0) as [HK HT].
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end. unfold xbits in *. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r0) in * by exact (proj1 HS0).
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
  - (* the page-cross entry *)
    destruct PRE as [MEM [P [C [RSP [B0 Z9]]]]].
    sc_run.
    all: sc_norm MEM P Z9.
    all: rewrite (sarx_norm r p) in BC by (change (2^32) with 4294967296; exact (proj1 HS)).
    all: destruct (sarx_hit m p _ K r FH NW HS) as [SN SH].
    + (* no hit before the end of the aligned block *)
      apply N.eqb_eq in BC.
      repeat split; try assumption; try reflexivity. exact (SN BC).
    + (* the first hit is there and is c *)
      apply N.eqb_neq in BC. pose proof (SH BC) as HK. symmetry in HK.
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end.
      try rewrite (sarx_norm r p) in * by (change (2^32) with 4294967296; exact (proj1 HS)).
      unfold xbits in *. rewrite ?N.shiftr_0_r, ?N.sub_0_r in *. rewrite ?(N.mod_small (ashiftr 32 r (p mod 32))) in * by apply ashiftr32_bound.
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
    + (* the first hit is the terminator *)
      apply N.eqb_neq in BC. pose proof (SH BC) as HK. symmetry in HK.
      upd regs_not_temp. repeat match goal with H: (_ =? getmem _ _ 1 _ _) = _ |- _ => progress upd_in regs_not_temp H end.
      try rewrite (sarx_norm r p) in * by (change (2^32) with 4294967296; exact (proj1 HS)).
      unfold xbits in *. rewrite ?N.shiftr_0_r, ?N.sub_0_r in *. rewrite ?(N.mod_small (ashiftr 32 r (p mod 32))) in * by apply ashiftr32_bound.
      split; [|split; reflexivity || assumption].
      sc_exit_res p K HK.
Qed.
