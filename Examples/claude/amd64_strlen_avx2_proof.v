(* strlen -- AVX2 implementation (__strlen_avx2)

   SEMANTICS
   ---------
   strlen(s) returns the number of bytes before the first NUL byte at s.
   On AVX2 machines glibc's IFUNC resolver selects __strlen_avx2, the
   seventh most-used libc function in our Firefox profile.  It compares
   32 bytes at a time against zero (VPCMPEQB), turns the comparison into a
   bit mask (VPMOVMSKB), and finds the first zero byte with TZCNT:
   * unless s is within 32 bytes of the end of a 4 KiB page, it checks the
     32 bytes at s (unaligned); otherwise it checks the aligned block that
     contains s and shifts the mask right by s mod 32 (SARX);
   * then it checks the next four aligned 32-byte blocks one by one;
   * then it loops over aligned 128-byte blocks, combining the four 32-byte
     vectors with VPMINUB so that one comparison detects a zero in any of
     them, and on a hit locates it in the four vectors (the last two with a
     64-bit TZCNT over the two masks).
   It reads past the end of the string, but never past the end of the page
   holding the terminator.  In Picinae all memory is readable, so the proof
   needs no page argument.

   The SIMD instructions are stepped with the instruction-level lemmas of
   amd64_avx2.v (vpcmpeqb_*_exec, vpmovmskb_rst_exec, vpminub_*_exec,
   tzcnt32/64_exec) instead of being executed symbolically.

   SPECIFICATION (man 3 strlen, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strlen(const char *s);

     DESCRIPTION
            The strlen() function calculates the length of the string pointed to by
            s, excluding the terminating null byte ('\0').

     RETURN VALUE
            The strlen() function returns the number of bytes in the string pointed
            to by s.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            __strlen_avx2 at 0x29d860 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            canonical temporaries, entry rebased to 0; see strlen_avx2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; m = memory on entry; slen m s L (the bytes at s+0 .. s+L-1
            are nonzero and the byte at s+L is zero), and s + L < 2^64 (the
            string does not wrap around the address space).
   Output:  On return, RAX = L and RSP is unchanged.  strlen writes no
            memory.
 *)

Require Import Picinae_amd64.
Require Import strlen_avx2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring amd64_simd amd64_avx2.
Import ListNotations.
Open Scope N.

Theorem strlen_avx2_nwc: forall s2 s1, strlen_avx2_amd64 s1 = strlen_avx2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strlen_avx2_welltyped: welltyped_prog x64typctx strlen_avx2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strlen_avx2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strlen_avx2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Theorem strlen_avx2_preserves_memory:
  forall_endstates strlen_avx2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(** * From masks to bytes *)

Lemma msk_byte: forall r m a j, msk_spec 32 r (getmem 64 LittleE 32 m a) -> j < 32 ->
  N.testbit r j = (m Ⓑ[j + a] =? 0).
Proof. intros r m a j M J. rewrite (M j J). apply zbyte_getmem. exact J. Qed.

(* A zero mask: no zero byte in the block. *)
Lemma msk_none: forall r m a, msk_spec 32 r (getmem 64 LittleE 32 m a) -> r = 0 ->
  forall j, j < 32 -> m Ⓑ[j + a] <> 0.
Proof.
  intros r m a M R0 j J. subst r. pose proof (msk_byte 0 m a j M J) as B.
  rewrite N.bits_0 in B. intro Z. rewrite Z in B. discriminate.
Qed.

(* A nonzero mask: TZCNT finds the first zero byte of the block. *)
Lemma msk_first: forall r m a, msk_spec 32 r (getmem 64 LittleE 32 m a) -> r < 2^32 -> r <> 0 ->
  let t := fst (N.iter 33 (tz_step 32) (0, r)) in
  t < 32 /\ m Ⓑ[t + a] = 0 /\ forall j, j < t -> m Ⓑ[j + a] <> 0.
Proof.
  intros r m a M RB NZ t.
  destruct (tz_result 32 r ltac:(lia) RB) as [_ T]. destruct (T NZ) as [T32 [TB TL]].
  change (N.succ 32) with 33 in T32, TB, TL. fold t in T32, TB, TL.
  split. exact T32. split.
  - rewrite (msk_byte r m a t M T32) in TB. apply N.eqb_eq, TB.
  - intros j J. rewrite <- N.eqb_neq. rewrite <- (msk_byte r m a j M ltac:(lia)). apply TL, J.
Qed.

(** * From blocks to the string length *)

Lemma slen_none: forall m p L b,
  slen m p L -> b <= L -> (forall j, j < 32 -> m Ⓑ[p ⊕ (b + j)] <> 0) -> b + 32 <= L.
Proof.
  intros m p L b [_ Z] BL NZ. destruct (N.le_gt_cases (b + 32) L) as [H|H]. exact H.
  exfalso. apply (NZ (L - b) ltac:(lia)). replace (b + (L - b)) with L by lia. exact Z.
Qed.

Lemma slen_hit: forall m p L b t,
  slen m p L -> b <= L -> m Ⓑ[p ⊕ (b + t)] = 0 ->
  (forall j, j < t -> m Ⓑ[p ⊕ (b + j)] <> 0) -> L = b + t.
Proof.
  intros m p L b t [NZ Z] BL ZT LT.
  destruct (N.lt_trichotomy L (b + t)) as [H|[H|H]].
  - exfalso. apply (LT (L - b) ltac:(lia)). replace (b + (L - b)) with L by lia. exact Z.
  - exact H.
  - exfalso. apply (NZ (b + t) H). exact ZT.
Qed.

(* Rebase a block's byte addresses (j + a) to string offsets (p + (b + j)). *)
Lemma byte_rebase: forall (m:memory) a p b j, a mod 2^64 = (p + b) mod 2^64 ->
  m Ⓑ[j + a] = m Ⓑ[p ⊕ (b + j)].
Proof.
  intros m a p b j A.
  assert (E: (j + a) mod 2^64 = (p + (b + j)) mod 2^64)
    by (rewrite <- N.add_mod_idemp_r, A, N.add_mod_idemp_r by discriminate; f_equal; lia).
  transitivity (m Ⓑ[(j + a) mod 2^64]). symmetry. apply getmem_mod_l.
  rewrite E. reflexivity.
Qed.

(* A block at offset b of the string: its mask is zero and the string goes
   on past it, or TZCNT of the mask is the remaining length. *)
Lemma blk_none: forall m p L a b r, slen m p L -> b <= L -> a mod 2^64 = (p + b) mod 2^64 ->
  msk_spec 32 r (getmem 64 LittleE 32 m a) -> r = 0 -> b + 32 <= L.
Proof.
  intros m p L a b r SL BL A M R0. apply (slen_none m p L b SL BL).
  intros j J. rewrite <- (byte_rebase m a p b j A). apply (msk_none r m a M R0 j J).
Qed.

Lemma blk_hit: forall m p L a b r, slen m p L -> b <= L -> a mod 2^64 = (p + b) mod 2^64 ->
  msk_spec 32 r (getmem 64 LittleE 32 m a) -> r < 2^32 -> r <> 0 ->
  L = b + fst (N.iter 33 (tz_step 32) (0, r)) /\ fst (N.iter 33 (tz_step 32) (0, r)) < 32.
Proof.
  intros m p L a b r SL BL A M RB NZ.
  destruct (msk_first r m a M RB NZ) as [T32 [TZ TL]].
  split; [|exact T32].
  apply (slen_hit m p L b _ SL BL).
  - rewrite <- (byte_rebase m a p b _ A). exact TZ.
  - intros j J. rewrite <- (byte_rebase m a p b j A). apply TL, J.
Qed.

(* The facts of one block: the mask in terms of the bytes at a. *)
Ltac blk_mask MEM CMP MSK :=
  upd_in regs_not_temp MSK; rewrite ?MEM in CMP;
  let MS := fresh "MS" in let RB := fresh "RB" in
  pose proof (movmsk_cmpz _ _ _ MSK CMP) as MS;
  pose proof (proj1 MSK) as RB; change (2^32) with 4294967296 in RB;
  clear MSK CMP.

(* Setting the low k bits. *)
Lemma lor_ones_eq: forall d k, N.lor d (N.ones k) = d - d mod 2^k + N.ones k.
Proof.
  intros d k.
  assert (E: d - d mod 2^k = N.ldiff d (N.ones k)).
  { rewrite N.ldiff_ones_r, N.shiftl_mul_pow2, N.shiftr_div_pow2.
    pose proof (N.div_mod d (2^k) (N.pow_nonzero 2 k ltac:(discriminate))). lia. }
  rewrite E, <- lor_plus.
  - apply N.bits_inj. intro i. rewrite !N.lor_spec, N.ldiff_spec.
    destruct (N.testbit d i), (N.testbit (N.ones k) i); reflexivity.
  - apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec, N.bits_0.
    destruct (N.testbit (N.ones k) i); cbn; rewrite ?Bool.andb_false_r; reflexivity.
Qed.

Lemma lor31: forall d, d .| 31 = d - d mod 32 + 31.
Proof. intro d. change 31 with (N.ones 5). rewrite lor_ones_eq. reflexivity. Qed.

Lemma lor127: forall d, d .| 127 = d - d mod 128 + 127.
Proof. intro d. change 127 with (N.ones 7). rewrite lor_ones_eq. reflexivity. Qed.

(* The aligned block addresses after p. *)
Lemma addr31: forall p k, (((p .| 31) + k) mod 2^64) mod 2^64 = (p + (31 - p mod 32 + k)) mod 2^64.
Proof.
  intros p k. rewrite N.mod_mod by discriminate. rewrite lor31. f_equal.
  pose proof (N.mod_lt p 32 ltac:(discriminate)). pose proof (N.mod_le p 32 ltac:(discriminate)). lia.
Qed.

(* Normalize the facts of the blocks checked so far: masks in terms of the
   bytes at the block address. *)
Ltac blk_norm MEM P :=
  repeat match goal with M: movmsk_spec _ _ _ |- _ => progress upd_in regs_not_temp M end;
  repeat match goal with C: cmpz_spec _ _ _ |- _ => progress upd_in regs_not_temp C end;
  repeat match goal with C: cmpz_spec _ _ _ |- _ => progress rewrite ?MEM, ?P in C end;
  repeat match goal with M: movmsk_spec 32 ?r ?y, C: cmpz_spec 32 ?y _ |- _ =>
    let MS := fresh "MS" in let RB := fresh "RB" in
    pose proof (movmsk_cmpz _ _ _ M C) as MS; pose proof (proj1 M) as RB;
    change (2^32) with 4294967296 in RB; clear M C end;
  repeat match goal with B: (?r mod 2^32 =? 0) = _, RB: ?r < 4294967296 |- _ =>
    rewrite (N.mod_small r) in B by (change (2^32) with 4294967296; exact RB) end.

(** * VPMINUB under VPCMPEQB-with-zero *)

Lemma pmin_zbyte: forall y a b j, pmin_spec 32 y a b -> j < 32 -> zbyte y j = zbyte a j || zbyte b j.
Proof.
  intros y a b j PM J. unfold zbyte. rewrite (PM j J).
  destruct (N.eqb_spec (byte a j) 0), (N.eqb_spec (byte b j) 0); cbn [orb];
    [apply N.eqb_eq | apply N.eqb_eq | apply N.eqb_eq | apply N.eqb_neq]; lia.
Qed.

Lemma msk_zb: forall r x j, msk_spec 32 r x -> j < 32 -> zbyte x j = N.testbit r j.
Proof. intros r x j M J. symmetry. apply M, J. Qed.

Lemma zb_none: forall r x, msk_spec 32 r x -> r = 0 -> forall j, j < 32 -> zbyte x j = false.
Proof. intros r x M R0 j J. rewrite (msk_zb r x j M J), R0. apply N.bits_0. Qed.

Lemma msk_of_none: forall x, (forall j, j < 32 -> zbyte x j = false) -> msk_spec 32 0 x.
Proof. intros x Z j J. rewrite N.bits_0. symmetry. apply Z, J. Qed.

Lemma pmin_none: forall y a b, pmin_spec 32 y a b -> (forall j, j < 32 -> zbyte y j = false) ->
  (forall j, j < 32 -> zbyte a j = false) /\ (forall j, j < 32 -> zbyte b j = false).
Proof.
  intros y a b PM Z. split; intros j J; specialize (Z j J); rewrite (pmin_zbyte y a b j PM J) in Z;
  apply Bool.orb_false_elim in Z; apply Z.
Qed.

(* The mask of a min whose other side has no zero byte. *)
Lemma msk_drop_l: forall r y a b, msk_spec 32 r y -> pmin_spec 32 y a b ->
  (forall j, j < 32 -> zbyte a j = false) -> msk_spec 32 r b.
Proof. intros r y a b M PM Z j J. rewrite (M j J), (pmin_zbyte y a b j PM J), (Z j J). reflexivity. Qed.

Lemma msk_drop_r: forall r y a b, msk_spec 32 r y -> pmin_spec 32 y a b ->
  (forall j, j < 32 -> zbyte b j = false) -> msk_spec 32 r a.
Proof. intros r y a b M PM Z j J. rewrite (M j J), (pmin_zbyte y a b j PM J), (Z j J). destruct (zbyte a j); reflexivity. Qed.

(** * 64-bit TZCNT over two 32-bit masks *)

Lemma lowest_unique: forall x t1 t2,
  N.testbit x t1 = true -> (forall j, j < t1 -> N.testbit x j = false) ->
  N.testbit x t2 = true -> (forall j, j < t2 -> N.testbit x j = false) -> t1 = t2.
Proof.
  intros x t1 t2 B1 L1 B2 L2. destruct (N.lt_trichotomy t1 t2) as [H|[H|H]].
  - rewrite (L2 t1 H) in B1. discriminate.
  - exact H.
  - rewrite (L1 t2 H) in B2. discriminate.
Qed.

Lemma tz64_split: forall e c, e < 2^32 -> c < 2^32 -> c <> 0 ->
  let t := fst (N.iter 65 (tz_step 64) (0, e .| (c << 32) mod 2^64)) in
  (e <> 0 -> t = fst (N.iter 33 (tz_step 32) (0, e))) /\
  (e = 0 -> t = 32 + fst (N.iter 33 (tz_step 32) (0, c))).
Proof.
  intros e c E C NZ t.
  set (v := e .| (c << 32) mod 2^64).
  assert (VB: forall j, N.testbit v j = if j <? 32 then N.testbit e j else N.testbit c (j - 32)).
  { intro j. subst v. rewrite N.lor_spec, Nmod_pow2_bits. destruct (N.ltb_spec j 32).
    - rewrite N.shiftl_spec_low by lia. rewrite Bool.andb_false_r, Bool.orb_false_r. reflexivity.
    - rewrite (bound_hibits_zero 32 e j E H). cbn [orb].
      rewrite N.shiftl_spec_high by lia. destruct (N.ltb_spec j 64). reflexivity.
      symmetry. apply (bound_hibits_zero 32). exact C. lia. }
  assert (V0: v <> 0).
  { intro V. destruct (lowest_set_bit 32 c C NZ) as [k [K [BK _]]].
    pose proof (VB (k + 32)) as H. rewrite V, N.bits_0 in H.
    replace (k + 32 <? 32) with false in H by (symmetry; apply N.ltb_ge; lia).
    replace (k + 32 - 32) with k in H by lia. congruence. }
  assert (VLT: v < 2^64).
  { subst v. apply lor_bound. eapply N.lt_le_trans. exact E. apply N.pow_le_mono_r; lia.
    apply N.mod_lt. discriminate. }
  destruct (tz_result 64 v ltac:(lia) VLT) as [_ T]. destruct (T V0) as [T64 [TB TL]].
  change (N.succ 64) with 65 in T64, TB, TL. fold t in T64, TB, TL.
  split.
  - intro ENZ. destruct (tz_result 32 e ltac:(lia) E) as [_ T']. destruct (T' ENZ) as [T32 [EB EL]].
    change (N.succ 32) with 33 in T32, EB, EL.
    apply (lowest_unique v); [exact TB | exact TL | |].
    + rewrite VB. replace (_ <? 32) with true by (symmetry; apply N.ltb_lt; exact T32). exact EB.
    + intros j J. rewrite VB. replace (j <? 32) with true by (symmetry; apply N.ltb_lt; lia). apply EL, J.
  - intro E0. subst e. destruct (tz_result 32 c ltac:(lia) C) as [_ T']. destruct (T' NZ) as [T32 [CB CL]].
    change (N.succ 32) with 33 in T32, CB, CL.
    apply (lowest_unique v); [exact TB | exact TL | |].
    + rewrite VB. replace (32 + _ <? 32) with false by (symmetry; apply N.ltb_ge; lia).
      replace (32 + _ - 32) with (fst (N.iter 33 (tz_step 32) (0, c))) by lia. exact CB.
    + intros j J. rewrite VB. destruct (N.ltb_spec j 32). apply N.bits_0. apply CL. lia.
Qed.

(** * The page-cross block: SARX by s mod 32 *)

Lemma ashiftr32_bound: forall r k, ashiftr 32 r k < 2^32.
Proof.
  intros r k. apply hibits_zero_bound. intros b B. rewrite ashiftr_spec.
  replace (b <? 32) with false by (symmetry; apply N.ltb_ge; exact B). reflexivity.
Qed.

Lemma sarx_norm: forall r p, r < 2^32 ->
  ashiftr 32 ((r >> 0) mod 2^32) ((p >> 0) mod 2^32 .& 31) mod 2^32 = ashiftr 32 r (p mod 32).
Proof.
  intros r p R. rewrite !N.shiftr_0_r, (N.mod_small r) by exact R.
  rewrite N.mod_small by apply ashiftr32_bound. f_equal.
  change 31 with (N.ones 5). rewrite N.land_ones. change (2^5) with 32.
  change (2^32) with (32 * 134217728). rewrite N.mod_mul_r, N.mul_comm, N.mod_add by discriminate.
  apply N.mod_mod. discriminate.
Qed.

Lemma sarx_block: forall m p L r, slen m p L -> p + L < 2^64 ->
  msk_spec 32 r (getmem 64 LittleE 32 m (((p .| 31) + 18446744073709551585) mod 2^64)) -> r < 2^32 ->
  let e := ashiftr 32 r (p mod 32) in
  (e = 0 -> 32 - p mod 32 <= L) /\ (e <> 0 -> fst (N.iter 33 (tz_step 32) (0, e)) = L).
Proof.
  intros m p L r SL NW M R e.
  set (k := p mod 32). assert (K: k < 32) by (apply N.mod_lt; discriminate).
  assert (KP: k <= p) by (apply N.mod_le; discriminate).
  set (a := ((p .| 31) + 18446744073709551585) mod 2^64) in M.
  assert (A: a = p - k).
  { subst a. rewrite lor31. fold k. change (2^64) with 18446744073709551616 in *.
    replace (p - k + 31 + 18446744073709551585) with (p - k + 1 * 18446744073709551616) by lia.
    rewrite N.mod_add, N.mod_small by lia. reflexivity. }
  (* bit i of e, for i + k < 32: the byte at p + i is zero *)
  assert (EB: forall i, i + k < 32 -> N.testbit e i = (m Ⓑ[p ⊕ (0 + i)] =? 0)).
  { intros i I. subst e. fold k. rewrite ashiftr_spec. change (N.pred 32) with 31.
    replace (i <? 32) with true by (symmetry; apply N.ltb_lt; lia). rewrite N.min_l by lia.
    cbn [andb]. rewrite (msk_byte r m a (i + k) M I). f_equal.
    replace (i + k + a) with (i + (k + a)) by lia.
    apply byte_rebase. rewrite A. f_equal. lia. }
  split.
  - intro E0. destruct (N.le_gt_cases (32 - k) L) as [H|H]. exact H.
    exfalso. destruct SL as [_ Z].
    pose proof (EB L ltac:(lia)) as B. rewrite E0, N.bits_0, N.add_0_l in B.
    rewrite Z in B. discriminate.
  - intro NZ. destruct (tz_result 32 e ltac:(lia) (ashiftr32_bound r k)) as [_ T].
    destruct (T NZ) as [T32 [TB TL]]. change (N.succ 32) with 33 in T32, TB, TL.
    set (t := fst (N.iter 33 (tz_step 32) (0, e))) in *.
    assert (TK: t + k < 32).
    { destruct (N.lt_ge_cases (t + k) 32) as [H|H]. exact H. exfalso.
      assert (B31: N.testbit e (31 - k) = N.testbit e t).
      { subst e. fold k. rewrite !ashiftr_spec. change (N.pred 32) with 31.
        rewrite !N.min_r by lia.
        replace (31 - k <? 32) with true by (symmetry; apply N.ltb_lt; lia).
        replace (t <? 32) with true by (symmetry; apply N.ltb_lt; lia). reflexivity. }
      rewrite (TL (31 - k) ltac:(lia)), TB in B31. discriminate. }
    symmetry. apply (slen_hit m p L 0 t SL (N.le_0_l _)).
    + rewrite (EB t TK) in TB. apply N.eqb_eq, TB.
    + intros j J. pose proof (TL j J) as B. rewrite (EB j ltac:(lia)) in B. apply N.eqb_neq, B.
Qed.

(** * Specification *)

Definition sl_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 48 | 77 | 94 | 110 | 126 | 289 | 318 | 334 | 369 => true
  | _ => false
  end | _ => false end.

Definition sl_post (m L rsp:N) (s':store) :=
  s' R_RAX = L /\ s' R_RSP = rsp /\ s' V_MEM64 = m.

Definition sl_invs (m p L rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RSP = rsp)
  (* the first, unaligned block *)
  | 29 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RDX = p /\ st R_RSP = rsp /\ st R_YMM0 = 0)
  (* the four aligned blocks after the first (partial) one *)
  | 132 => Some (st V_MEM64 = m /\ st R_RDI = p .| 31 /\ st R_RDX = p /\ st R_RSP = rsp /\
                 st R_YMM0 = 0 /\ 32 - p mod 32 <= L)
  (* the 128-byte loop: the o bytes before RDI + 1 are nonzero *)
  | 192 => Some (exists o, 0 < o <= L /\ st V_MEM64 = m /\ st R_RDI = p + o - 1 /\ st R_RDX = p /\
                 st R_RSP = rsp /\ st R_YMM0 = 0)
  (* the page-cross entry *)
  | 336 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RDX = p /\ st R_RSP = rsp /\ st R_YMM0 = 0)
  | 48 | 77 | 94 | 110 | 126 | 289 | 318 | 334 | 369 => Some (sl_post m L rsp st)
  | _ => None
  end | _ => None end.

(** * Stepping the SIMD instructions *)

Ltac nt := let k := fresh "k" in let H := fresh "H" in intros k H; discriminate.

(* Step one instruction with an instruction-level lemma; L applies the lemma
   to the statement XS and leaves x1 = None and the next state. *)
Ltac simd_step L :=
  eapply NIStep; [reflexivity|reflexivity|];
  let c1 := fresh "c" in let s1 := fresh "s" in let x1 := fresh "x" in let XS := fresh "XS" in
  intros c1 s1 x1 XS; L XS;
  try rewrite exitof_none;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try lazymatch goal with |- context [ Addr (N.add ?m ?n) ] => simpl (N.add m n) end.

Ltac cmpeq_ld Y0 := simd_step ltac:(fun XS =>
  apply vpcmpeqb_ld_exec in XS; [| upd regs_not_temp; exact Y0 | reflexivity | reflexivity | nt];
  let CMP := fresh "CMP" in let y := fresh "y" in
  destruct XS as [-> [y [CMP ->]]]).

Ltac cmpeq_ldo Y0 := simd_step ltac:(fun XS =>
  apply vpcmpeqb_ldo_exec in XS; [| upd regs_not_temp; exact Y0 | reflexivity | reflexivity | nt];
  let CMP := fresh "CMP" in let y := fresh "y" in
  destruct XS as [-> [y [CMP ->]]]).

Ltac cmpeq_reg Y0 := simd_step ltac:(fun XS =>
  apply vpcmpeqb_reg_exec in XS; [| upd regs_not_temp; exact Y0 | reflexivity];
  let CMP := fresh "CMP" in let y := fresh "y" in
  destruct XS as [-> [y [CMP ->]]]).

Ltac movmsk := simd_step ltac:(fun XS =>
  apply vpmovmskb_rst_exec in XS; [| nt | reflexivity];
  let MSK := fresh "MSK" in let r := fresh "r" in
  destruct XS as [-> [r [MSK ->]]]).

Ltac pmin_ldo := simd_step ltac:(fun XS =>
  apply vpminub_ldo_exec in XS; [| reflexivity | reflexivity | nt | nt];
  let PM := fresh "PM" in let y := fresh "y" in
  destruct XS as [-> [y [PM ->]]]).

Ltac pmin_reg := simd_step ltac:(fun XS =>
  apply vpminub_reg_exec in XS; [| reflexivity];
  let PM := fresh "PM" in let y := fresh "y" in
  destruct XS as [-> [y [PM ->]]]).

Ltac tz32 := simd_step ltac:(fun XS =>
  apply tzcnt32_exec in XS; cbv zeta in XS; destruct XS as [-> ->]).

Ltac tz64 := simd_step ltac:(fun XS =>
  apply tzcnt64_exec in XS; cbv zeta in XS; destruct XS as [-> ->]).

(* Step one instruction: SIMD addresses with their lemmas, others with
   x64_step. *)
Ltac sl_simd Y0 :=
  lazymatch goal with |- nextinv _ _ _ _ ((Addr ?a, _) :: _) =>
  lazymatch a with
  | 29 => cmpeq_ld Y0
  | 132 => cmpeq_ldo Y0
  | 145 => cmpeq_ldo Y0
  | 158 => cmpeq_ldo Y0
  | 171 => cmpeq_ldo Y0
  | 340 => cmpeq_ldo Y0
  | 216 => cmpeq_reg Y0
  | 232 => cmpeq_reg Y0
  | 247 => cmpeq_reg Y0
  | 259 => cmpeq_reg Y0
  | 33 => movmsk
  | 137 => movmsk
  | 150 => movmsk
  | 163 => movmsk
  | 176 => movmsk
  | 220 => movmsk
  | 236 => movmsk
  | 251 => movmsk
  | 263 => movmsk
  | 345 => movmsk
  | 197 => pmin_ldo
  | 207 => pmin_ldo
  | 212 => pmin_reg
  | 41 => tz32
  | 64 => tz32
  | 80 => tz32
  | 96 => tz32
  | 112 => tz32
  | 304 => tz32
  | 320 => tz32
  | 362 => tz32
  | 274 => tz64
  end end.

Ltac sl_run Y0 := repeat (first [sl_simd Y0 | x64_step]).

(* These paths branch only on ZF (and CF for the page test), so abstract
   away the other flags. *)
Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true
| _ => false end).

Theorem strlen_avx2_correct:
  forall st t s' x' m p L rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (P: st R_RDI = p) (RSP: st R_RSP = rsp)
         (SL: slen m p L) (NW: p + L < 2^64),
  satisfies_all strlen_avx2_amd64 (sl_invs m p L rsp) sl_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strlen_avx2_welltyped. intro MDL1.
  clear - PRE MDL1 SL NW. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [P RSP]].
    repeat x64_step.
    all: repeat split; reflexivity || assumption.
  - (* first block *)
    destruct PRE as [MEM [P [PD [RSP Y0]]]].
    sl_run Y0.
    all: blk_norm MEM P.
    + (* no zero in the first 32 bytes *)
      apply N.eqb_eq in BC.
      pose proof (blk_none m p L p 0 r SL (N.le_0_l _) ltac:(rewrite N.add_0_r; reflexivity) MS BC).
      repeat split; try assumption; try reflexivity.
      pose proof (N.mod_lt p 32 ltac:(discriminate)). clear - H H0. lia.
    + (* the first zero is in the first 32 bytes *)
      apply N.eqb_neq in BC.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r) by exact RB.
      split; [|split; assumption].
      rewrite (proj1 (blk_hit m p L p 0 r SL (N.le_0_l _) ltac:(rewrite N.add_0_r; reflexivity) MS RB BC)).
      reflexivity.
  - (* four aligned blocks *)
    destruct PRE as [MEM [P [PD [RSP [Y0 C0]]]]].
    sl_run Y0.
    all: blk_norm MEM P.
    + (* no zero in the four blocks: enter the loop *)
    assert (N1: 31 - p mod 32 + 1 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 1) r SL); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC]).
    assert (N33: 31 - p mod 32 + 33 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 33) r0 SL); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC0]).
    assert (N65: 31 - p mod 32 + 65 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 65) r1 SL); [clear - C0 N1 N33; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC1]).
    assert (N97: 31 - p mod 32 + 97 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 97) r2 SL); [clear - C0 N1 N33 N65; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC2]).
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      assert (Q: 1 ⊕ (p .| 31) = p - p mod 32 + 32).
      { rewrite lor31, N.mod_small. lia. clear - NW N97 PM PL. change (2^64) with 18446744073709551616 in *. lia. }
      rewrite Q, lor127.
      pose proof (N.mod_lt (p - p mod 32 + 32) 128 ltac:(discriminate)) as QM.
      pose proof (N.mod_le (p - p mod 32 + 32) 128 ltac:(discriminate)) as QL.
      exists (p - p mod 32 + 32 - (p - p mod 32 + 32) mod 128 + 128 - p).
      split. clear - N97 PM PL QM QL. lia.
      split. assumption.
      split. clear - PM PL QM QL. lia.
      repeat split; assumption.
    + (* the first zero is in block 3 *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 1) r SL); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC]).
      assert (N33: 31 - p mod 32 + 33 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 33) r0 SL); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC0]).
      assert (N65: 31 - p mod 32 + 65 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 65) r1 SL); [clear - C0 N1 N33; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC1]).
      apply N.eqb_neq in BC2.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r.
      match goal with M: msk_spec 32 r2 _, RBx: r2 < 4294967296 |- _ =>
        rewrite (N.mod_small r2) by (change (2^32) with 4294967296; exact RBx);
        destruct (blk_hit m p L _ (31 - p mod 32 + 97) r2 SL ltac:(clear - C0 N1 N33 N65 PM; lia) (addr31 p 97) M RBx BC2) as [HL HT]
      end.
      split; [|split; assumption].
      rewrite HL, lor31, msub_sub by (clear - PL; lia).
      rewrite N.mod_small; clear - HT PM PL; change (2^32) with 4294967296; lia.
    + (* the first zero is in block 2 *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 1) r SL); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC]).
      assert (N33: 31 - p mod 32 + 33 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 33) r0 SL); [clear - C0 N1; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC0]).
      apply N.eqb_neq in BC1.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r.
      match goal with M: msk_spec 32 r1 _, RBx: r1 < 4294967296 |- _ =>
        rewrite (N.mod_small r1) by (change (2^32) with 4294967296; exact RBx);
        destruct (blk_hit m p L _ (31 - p mod 32 + 65) r1 SL ltac:(clear - C0 N1 N33 PM; lia) (addr31 p 65) M RBx BC1) as [HL HT]
      end.
      split; [|split; assumption].
      rewrite HL, lor31, msub_sub by (clear - PL; lia).
      rewrite N.mod_small; clear - HT PM PL; change (2^32) with 4294967296; lia.
    + (* the first zero is in block 1 *)
      assert (N1: 31 - p mod 32 + 1 + 32 <= L) by (eapply (blk_none m p L _ (31 - p mod 32 + 1) r SL); [clear - C0 ; pose proof (N.mod_lt p 32 ltac:(discriminate)); lia | apply addr31 | eassumption | apply N.eqb_eq; exact BC]).
      apply N.eqb_neq in BC0.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r.
      match goal with M: msk_spec 32 r0 _, RBx: r0 < 4294967296 |- _ =>
        rewrite (N.mod_small r0) by (change (2^32) with 4294967296; exact RBx);
        destruct (blk_hit m p L _ (31 - p mod 32 + 33) r0 SL ltac:(clear - C0 N1 PM; lia) (addr31 p 33) M RBx BC0) as [HL HT]
      end.
      split; [|split; assumption].
      rewrite HL, lor31, msub_sub by (clear - PL; lia).
      rewrite N.mod_small; clear - HT PM PL; change (2^32) with 4294967296; lia.
    + (* the first zero is in block 0 *)
      apply N.eqb_neq in BC.
      pose proof (N.mod_lt p 32 ltac:(discriminate)) as PM; pose proof (N.mod_le p 32 ltac:(discriminate)) as PL.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r.
      match goal with M: msk_spec 32 r _, RBx: r < 4294967296 |- _ =>
        rewrite (N.mod_small r) by (change (2^32) with 4294967296; exact RBx);
        destruct (blk_hit m p L _ (31 - p mod 32 + 1) r SL ltac:(clear - C0  PM; lia) (addr31 p 1) M RBx BC) as [HL HT]
      end.
      split; [|split; assumption].
      rewrite HL, lor31, msub_sub by (clear - PL; lia).
      rewrite N.mod_small; clear - HT PM PL; change (2^32) with 4294967296; lia.

  - (* the 128-byte loop *)
    destruct PRE as [o [O [MEM [P [PD [RSP Y0]]]]]].
    sl_run Y0.
    all: blk_norm MEM P.
    all: repeat match goal with H: pmin_spec _ _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: repeat match goal with H: pmin_spec _ _ _ _ |- _ => progress rewrite ?MEM, ?P in H end.
    all: assert (OB: o + 128 <= L \/ True) by (right; exact I).
    all: assert (A0: (1 + (p + o - 1)) mod 2^64 = (p + o) mod 2^64) by (f_equal; clear - O; lia).
    all: assert (A1: ((p + o - 1) ⊕ 33) mod 2^64 = (p + (o + 32)) mod 2^64) by
           (rewrite N.mod_mod by discriminate; f_equal; clear - O; lia).
    all: assert (A2: (65 + (p + o - 1)) mod 2^64 = (p + (o + 64)) mod 2^64) by (f_equal; clear - O; lia).
    all: assert (A3: ((p + o - 1) ⊕ 97) mod 2^64 = (p + (o + 96)) mod 2^64) by
           (rewrite N.mod_mod by discriminate; f_equal; clear - O; lia).
    all: clear OB.
    + (* no zero in the 128 bytes: next iteration *)
      apply N.eqb_eq in BC.
      match goal with M: msk_spec 32 r _ |- _ => pose proof (zb_none _ _ M BC) as ZY1 end.
      destruct (pmin_none _ _ _ PM1 ZY1) as [ZY0 ZY].
      destruct (pmin_none _ _ _ PM0 ZY0) as [Z2 Z3].
      destruct (pmin_none _ _ _ PM ZY) as [Z0 Z1].
      pose proof (blk_none m p L _ o 0 SL ltac:(clear - O; lia) A0 (msk_of_none _ Z0) eq_refl) as N0.
      pose proof (blk_none m p L _ (o + 32) 0 SL N0 A1 (msk_of_none _ Z1) eq_refl) as N1.
      pose proof (blk_none m p L _ (o + 32 + 32) 0 SL N1 ltac:(rewrite A2; f_equal; clear - O; lia) (msk_of_none _ Z2) eq_refl) as N2.
      pose proof (blk_none m p L _ (o + 32 + 32 + 32) 0 SL N2 ltac:(rewrite A3; f_equal; clear - O; lia) (msk_of_none _ Z3) eq_refl) as N3.
      exists (o + 128).
      split. clear - N3 O. lia.
      split. reflexivity.
      split. { change (2^7) with 128. rewrite N.mod_small. clear - O; lia. clear - N3 O NW. lia. }
      repeat split; assumption.
    + (* the first zero is in block 2 or 3: 64-bit TZCNT over both masks *)
      apply N.eqb_neq in BC. apply N.eqb_eq in BC0. apply N.eqb_eq in BC1.
      match goal with M: msk_spec 32 r0 _ |- _ => rename M into M0 end.
      match goal with M: msk_spec 32 r1 _ |- _ => rename M into M1 end.
      match goal with M: msk_spec 32 r2 _ |- _ => rename M into M2 end.
      match goal with M: msk_spec 32 r _ |- _ => rename M into MA end.
      match goal with H: r2 < 4294967296 |- _ => rename H into RX2 end.
      match goal with H: r < 4294967296 |- _ => rename H into RXA end.
      pose proof (zb_none _ _ M1 BC1) as ZY. destruct (pmin_none _ _ _ PM ZY) as [Z0 Z1].
      pose proof (blk_none m p L _ o 0 SL ltac:(clear - O; lia) A0 (msk_of_none _ Z0) eq_refl) as N0.
      pose proof (blk_none m p L _ (o + 32) 0 SL N0 A1 (msk_of_none _ Z1) eq_refl) as N1.
      upd regs_not_temp.
      destruct (tz64_split r2 r RX2 RXA BC) as [HE HZ].
      split; [|split; reflexivity || assumption].
      destruct (N.eq_dec r2 0) as [E0|E0].
      * rewrite (HZ E0).
        pose proof (zb_none _ _ M2 E0) as Z2.
        pose proof (blk_none m p L _ (o + 32 + 32) 0 SL N1 ltac:(rewrite A2; f_equal; clear - O; lia) (msk_of_none _ Z2) eq_refl) as N2.
        pose proof (msk_drop_l _ _ _ _ (msk_drop_r _ _ _ _ MA PM1 ZY) PM0 Z2) as M3.
        destruct (blk_hit m p L _ (o + 32 + 32 + 32) r SL N2 ltac:(rewrite A3; f_equal; clear - O; lia) M3 RXA BC) as [HL HT].
        change (2^7) with 128 in *.
        rewrite msub_sub by (clear - HL O; lia). rewrite N.mod_small; clear - HL HT NW O; lia.
      * rewrite (HE E0).
        destruct (blk_hit m p L _ (o + 32 + 32) r2 SL N1 ltac:(rewrite A2; f_equal; clear - O; lia) M2 RX2 E0) as [HL HT].
        rewrite msub_sub by (clear - HL O; lia). rewrite N.mod_small; clear - HL HT NW O; lia.
    + (* the first zero is in block 1 *)
      apply N.eqb_neq in BC1. apply N.eqb_eq in BC0.
      match goal with M: msk_spec 32 r0 _ |- _ => rename M into M0 end.
      match goal with M: msk_spec 32 r1 _ |- _ => rename M into M1 end.
      match goal with H: r1 < 4294967296 |- _ => rename H into RX1 end.
      pose proof (zb_none _ _ M0 BC0) as Z0.
      pose proof (blk_none m p L _ o r0 SL ltac:(clear - O; lia) A0 M0 BC0) as N0.
      pose proof (msk_drop_l _ _ _ _ M1 PM Z0) as M1'.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r1) by (change (2^32) with 4294967296; exact RX1).
      destruct (blk_hit m p L _ (o + 32) r1 SL N0 A1 M1' RX1 BC1) as [HL HT].
      split; [|split; reflexivity || assumption].
      rewrite msub_sub by (clear - HL O; lia). rewrite N.mod_small; clear - HL HT NW O; lia.
    + (* the first zero is in block 0 *)
      apply N.eqb_neq in BC0.
      match goal with M: msk_spec 32 r0 _ |- _ => rename M into M0 end.
      match goal with H: r0 < 4294967296 |- _ => rename H into RX0 end.
      upd regs_not_temp. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r, (N.mod_small r0) by (change (2^32) with 4294967296; exact RX0).
      destruct (blk_hit m p L _ o r0 SL ltac:(clear - O; lia) A0 M0 RX0 BC0) as [HL HT].
      split; [|split; reflexivity || assumption].
      rewrite msub_sub by (clear - HL O; lia). rewrite N.mod_small; clear - HL HT NW O; lia.
  - (* the page-cross entry *)
    destruct PRE as [MEM [P [PD [RSP Y0]]]].
    sl_run Y0.
    all: blk_norm MEM P.
    all: rewrite (sarx_norm r p) in BC by (change (2^32) with 4294967296; exact RB).
    all: destruct (sarx_block m p L r SL NW MS ltac:(change (2^32) with 4294967296; exact RB)) as [SN SH].
    + (* no zero before the end of the aligned block *)
      apply N.eqb_eq in BC.
      repeat split; try assumption; try reflexivity. exact (SN BC).
    + (* the first zero is there *)
      apply N.eqb_neq in BC.
      upd regs_not_temp. rewrite (sarx_norm r p) by (change (2^32) with 4294967296; exact RB).
      unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r, N.mod_small by apply ashiftr32_bound.
      split; [exact (SH BC)|split; assumption].
Qed.
