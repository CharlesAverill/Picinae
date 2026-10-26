(* strcmp -- AVX2 implementation (__strcmp_avx2), short-string case

   SEMANTICS
   ---------
   strcmp(p, q) compares the C strings at p and q and returns the signed
   difference of the first bytes that differ (or 0 at a common terminator).
   On AVX2 machines glibc's IFUNC resolver selects __strcmp_avx2.  It compares
   32 bytes at a time: VPCMPEQB marks equal bytes, VPMINUB with the first
   operand turns a NUL into a zero lane, and VPCMPEQB against zero then marks
   each "stop" lane -- a byte that differs or is the terminator.  VPMOVMSKB
   and TZCNT find the first stop, and the two bytes there are subtracted.

   This file proves the common short-string case: the first stop is within the
   first 32 bytes (K < 32) and both pointers are at least 128 bytes from a
   page end, so the first 32-byte block decides the result.  The four-block
   path, the 128-byte loop and the page-straddling path are unreachable under
   these preconditions (refuted by False invariants) and a full proof of them
   is left for later.

   SPECIFICATION (man 3 strcmp, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------
     int strcmp(const char *s1, const char *s2);
     RETURN VALUE: an integer less than, equal to, or greater than zero if s1
     is found, respectively, to be less than, to match, or be greater than s2.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            __strcmp_avx2 at 0x2989c0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            canonical temporaries, entry rebased to 0; see strcmp_avx2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 4.8
            (claude-opus-4-8), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = p, RSI = q; m = memory on entry.  K is the index of the
            first stop: the bytes p+0..p+K-1 equal q+0..q+K-1 and are nonzero,
            and the byte at p+K either differs from q+K or is 0 (scmp m p q K).
            K < 32, and (p | q) mod 4096 <= 0xf80 (both at least 128 bytes from
            a page end).
   Output:  On return, EAX = (m[p+K] - m[q+K]) mod 2^32 (zero-extended bytes
            subtracted as 32-bit); RSP is unchanged.  strcmp writes no memory.
 *)

Require Import Picinae_amd64.
Require Import strcmp_avx2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_simd amd64_avx2.
Import ListNotations.
Open Scope N.

Theorem strcmp_avx2_nwc: forall s2 s1, strcmp_avx2_amd64 s1 = strcmp_avx2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strcmp_avx2_welltyped: welltyped_prog x64typctx strcmp_avx2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strcmp_avx2_preserves_memory:
  forall_endstates strcmp_avx2_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem strcmp_avx2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strcmp_avx2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(** * The stop condition and its mask *)

(* First stop index: p and q agree and are nonzero up to K, and at K they
   differ or p terminates. *)
Definition scmp (m:memory) p q K :=
  (forall k, k < K -> m Ⓑ[p ⊕ k] = m Ⓑ[q ⊕ k] /\ m Ⓑ[p ⊕ k] <> 0) /\
  (m Ⓑ[p ⊕ K] <> m Ⓑ[q ⊕ K] \/ m Ⓑ[p ⊕ K] = 0).

Definition stopb (a b:N) := negb (a =? b) || (a =? 0).

(* r is the stop mask of the 32 bytes at p/q. *)
Definition sspec (r:N) (m:memory) p q :=
  r < 2^32 /\ forall j, j < 32 -> N.testbit r j = stopb (m Ⓑ[p ⊕ j]) (m Ⓑ[q ⊕ j]).

Lemma byte_getmem_mod: forall (m:memory) a i, i < 32 -> byte (getmem 64 LittleE 32 m a) i = m Ⓑ[a ⊕ i].
Proof.
  intros m a i I. unfold byte. apply byte_of_getmem. exact I.
Qed.

Lemma bit7_if: forall b:bool, N.testbit (if b then 255 else 0) 7 = b.
Proof. intros [|]; reflexivity. Qed.

Lemma testbit_byte7: forall y j, N.testbit y (8*j+7) = N.testbit (byte y j) 7.
Proof. intros y j. rewrite byte_testbit. change (7 <? 8) with true. cbn [andb]. f_equal. lia. Qed.

Lemma byte_lt256: forall x i, byte x i < 256.
Proof. intros. apply byte_lt. Qed.

(* The VPCMPEQB(p,q); VPMINUB(_,p); VPCMPEQB(_,0) chain yields the stop mask. *)
Lemma sspec_build: forall y1 y0 y0' r (m:memory) p q,
  cmpeq_spec 32 y1 (getmem 64 LittleE 32 m p) (getmem 64 LittleE 32 m q) ->
  pmin_spec 32 y0 y1 (getmem 64 LittleE 32 m p) ->
  cmpeq_spec 32 y0' y0 0 ->
  movmsk_spec 32 r y0' ->
  sspec r m p q.
Proof.
  intros y1 y0 y0' r m p q C1 PM C0 [RB M]. split. exact RB.
  intros j J. rewrite (M j J), testbit_byte7, (C0 j J).
  replace (byte 0 j) with 0 by (unfold byte, xbits; rewrite N.shiftr_0_l; reflexivity).
  (* byte y0' j = if byte y0 j =? 0 then 255 else 0 *)
  rewrite N.eqb_sym, bit7_if.
  rewrite (PM j J), (C1 j J), !byte_getmem_mod by exact J.
  set (a := m Ⓑ[p ⊕ j]). set (b := m Ⓑ[q ⊕ j]).
  assert (AL: a < 256) by (unfold a; change 256 with (2^(1*8)); apply getmem_bound). unfold stopb.
  destruct (N.eqb_spec a b) as [->|NE]; cbn [negb orb].
  - destruct (N.eqb_spec b 0) as [->|NZ].
    + rewrite N.min_r by lia. reflexivity.
    + rewrite N.min_r by lia. apply N.eqb_neq. apply not_eq_sym; exact NZ.
  - rewrite N.min_l by lia. reflexivity.
Qed.

(* cmpeq against the zero register is cmpz. *)
Lemma cmpeq_r0_cmpz: forall y x, cmpeq_spec 32 y x 0 -> cmpz_spec 32 y x.
Proof.
  intros y x C i I. rewrite (C i I). unfold zbyte.
  replace (byte 0 i) with 0 by (unfold byte, xbits; rewrite N.shiftr_0_l; reflexivity).
  reflexivity.
Qed.

(* No stop in a nonzero mask that scmp says has none before K; with K < 32 the
   mask is nonzero and TZCNT lands on K. *)
Lemma sspec_first: forall r m p q K, sspec r m p q -> scmp m p q K -> K < 32 ->
  r <> 0 /\ fst (N.iter 33 (tz_step 32) (0, r)) = K.
Proof.
  intros r m p q K [RB M] [NH ST] K32.
  assert (BK: N.testbit r K = true).
  { rewrite (M K K32). unfold stopb. destruct ST as [D|Z].
    - rewrite (proj2 (N.eqb_neq _ _) D). reflexivity.
    - rewrite Z. rewrite N.eqb_refl, Bool.orb_true_r. reflexivity. }
  assert (BL: forall j, j < K -> N.testbit r j = false).
  { intros j J. rewrite (M j ltac:(lia)). destruct (NH j J) as [EQ NZ]. unfold stopb.
    rewrite EQ, N.eqb_refl. cbn [negb orb]. apply N.eqb_neq.
    rewrite <- EQ. exact NZ. }
  assert (NZr: r <> 0) by (intro Z; rewrite Z, N.bits_0 in BK; discriminate).
  split. exact NZr.
  destruct (tz_result 32 r ltac:(lia) RB) as [_ T]. destruct (T NZr) as [T32 [TB TL]].
  change (N.succ 32) with 33 in T32, TB, TL. set (t := fst (N.iter 33 (tz_step 32) (0, r))) in *.
  destruct (N.lt_trichotomy t K) as [H|[H|H]].
  - rewrite (BL t H) in TB. discriminate.
  - exact H.
  - rewrite (TL K H) in BK. discriminate.
Qed.

(* The page-safety test (JG after CMP (p|q)&0xfff, 0xf80) is not taken when
   the value is <= 0xf80.  The OF bit-expression is identically zero. *)
Lemma bit01: forall b, b < 2 -> b .& (b .^ 1) = 0.
Proof. intros b Hb. assert (H: b = 0 \/ b = 1) by lia. destruct H as [E|E]; rewrite E; reflexivity. Qed.

Lemma slt_0_32: forall x, x < 2^32 -> slt 32 x 0 = (2^31 <=? x).
Proof.
  intros x X. unfold slt. change (toZ 32 0) with 0%Z.
  pose proof (toZ_sign x 32) as TS. change (N.pred 32) with 31 in TS.
  rewrite (N.mod_small x (2^32) X) in TS.
  destruct (N.leb_spec (2^31) x) as [H|H].
  - apply Z.ltb_lt. destruct (Z.le_gt_cases 0 (toZ 32 x)) as [L|L]; [apply TS in L; lia | exact L].
  - apply Z.ltb_ge. apply TS. exact H.
Qed.

Lemma page_test0: forall w, w < 4096 -> w <= 3968 ->
  (if (msub 32 w 3968 >> 31 .& (msub 32 w 3968 >> 31 .^ 1) =?
       (if slt 32 (msub 32 ((w >> 0) mod 2^32) 3968) 0 then 1 else 0))
   then (if w =? 3968 then 0 else 1) else 0) = 0.
Proof.
  intros w W4 W3. rewrite N.shiftr_0_r, (N.mod_small w (2^32)) by (eapply N.lt_trans; [exact W4|reflexivity]).
  rewrite (bit01 (msub 32 w 3968 >> 31)).
  2:{ rewrite N.shiftr_div_pow2. apply N.div_lt_upper_bound. discriminate.
      change (2^31 * 2) with (2^32). apply msub_lt. }
  rewrite slt_0_32 by apply msub_lt.
  destruct (N.leb_spec (2^31) (msub 32 w 3968)) as [H|H]; cbn [N.eqb].
  - reflexivity.
  - (* msub 32 w 3968 < 2^31, with w <= 3968 < 4096, forces w = 3968 *)
    assert (w = 3968).
    { destruct (N.eq_dec w 3968) as [E|NE]. exact E.
      exfalso. unfold msub in H.
      change (3968 mod 2^32) with 3968 in H. change (2^32 - 3968) with 4294963328 in H.
      rewrite N.mod_small in H by (change (2^32) with 4294967296; lia).
      change (2^31) with 2147483648 in H. lia. }
    subst w. reflexivity.
Qed.


(** * Specification *)

Definition sc_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 71 => true | _ => false end | _ => false end.

Definition sc_post (m p q K rsp:N) (s':store) :=
  s' R_RAX mod 2^32 = msub 32 (m Ⓑ[p ⊕ K]) (m Ⓑ[q ⊕ K]) /\ s' R_RSP = rsp /\ s' V_MEM64 = m.

Definition sc_invs (m p q K rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = p /\ st R_RSI = q /\ st R_RSP = rsp)
  | 71 => Some (sc_post m p q K rsp st)
  (* four-block path, page-straddle path: unreachable when K < 32 and page-safe *)
  | 176 | 880 => Some False
  | _ => None
  end | _ => None end.

(** * Per-instruction SIMD stepping *)

Ltac simd_step L :=
  eapply NIStep; [reflexivity|reflexivity|];
  let c1 := fresh "c" in let s1 := fresh "s" in let x1 := fresh "x" in let XS := fresh "XS" in
  intros c1 s1 x1 XS; L XS; try rewrite exitof_none;
  try lazymatch goal with |- context [ exitof (N.add ?a ?b) ] => simpl (N.add a b) end;
  try lazymatch goal with |- context [ Addr (N.add ?a ?b) ] => simpl (N.add a b) end.

Ltac nt := let k := fresh in let H := fresh in intros k H; discriminate.

Ltac cmpeq_rld := simd_step ltac:(fun XS =>
  apply vpcmpeqb_rld_exec in XS; [| reflexivity | reflexivity | nt | nt | discriminate];
  let CE := fresh "CE" in let y := fresh "y" in destruct XS as [-> [y [CE ->]]]).
Ltac pmin_reg := simd_step ltac:(fun XS =>
  apply vpminub_reg_exec in XS; [| reflexivity];
  let PM := fresh "PM" in let y := fresh "y" in destruct XS as [-> [y [PM ->]]]).
Ltac cmpeq_rr := simd_step ltac:(fun XS =>
  apply vpcmpeqb_rr_exec in XS; [| reflexivity];
  let CE := fresh "CE" in let y := fresh "y" in destruct XS as [-> [y [CE ->]]]).
Ltac movmsk := simd_step ltac:(fun XS =>
  apply vpmovmskb_rst_exec in XS; [| nt | reflexivity];
  let MK := fresh "MK" in let r := fresh "r" in destruct XS as [-> [r [MK ->]]]).
Ltac tz32 := simd_step ltac:(fun XS =>
  apply tzcnt32_dc_exec in XS; cbv zeta in XS; destruct XS as [-> ->]).

Ltac sc_simd :=
  lazymatch goal with |- nextinv _ _ _ _ ((Addr ?a0, _) :: _) =>
  let a := eval vm_compute in a0 in
  lazymatch a with
  | 34 => cmpeq_rld | 38 => pmin_reg | 42 => cmpeq_rr | 46 => movmsk | 54 => tz32
  end end.
Ltac sc_run := repeat (first [sc_simd | x64_step]).

Ltac ignore_vars v ::= constr:(match v with R_AF | R_PF => true | _ => false end).

Theorem strcmp_avx2_correct:
  forall st t s' x' m p q K rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (P: st R_RDI = p) (Q: st R_RSI = q) (RSP: st R_RSP = rsp)
         (SC: scmp m p q K) (K32: K < 32) (PS: (p .| q) mod 4096 <= 3968),
  satisfies_all strcmp_avx2_amd64 (sc_invs m p q K rsp) sc_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcmp_avx2_welltyped. intro MDL1.
  clear - PRE MDL1 SC K32 PS. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry through the page test and the first block *)
    destruct PRE as [MEM [P [Q RSP]]].
    sc_run.
    (* normalize the SIMD hyps to concrete getmem/0 operands, build the stop mask *)
    all: repeat match goal with H: movmsk_spec _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: repeat match goal with H: cmpeq_spec _ _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: repeat match goal with H: pmin_spec _ _ _ _ |- _ => progress upd_in regs_not_temp H end.
    all: try match goal with
         | CE: cmpeq_spec 32 ?ya (getmem _ _ 32 ?mm ?pp) (getmem _ _ 32 ?mm ?qq),
           PM: pmin_spec 32 ?y0 ?ya (getmem _ _ 32 ?mm ?pp),
           CE0: cmpeq_spec 32 ?y0' ?y0 0,
           MK: movmsk_spec 32 ?r ?y0' |- _ =>
             pose proof (sspec_build _ _ _ _ mm pp qq CE PM CE0 MK) as SS;
             pose proof (sspec_first _ mm pp qq _ SS SC K32) as [RNZ RTZ]
         end.
    (* three goals: page-slow (False), four-block (False), and the result *)
    + (* four-block entry unreachable: the first-block mask is nonzero *)
      exfalso. rewrite N.mod_small in BC0 by exact (proj1 SS).
      apply N.eqb_eq in BC0. apply RNZ. exact BC0.
    + (* the result at the first stop *)
      upd regs_not_temp.
      replace (xbits r 0 32) with r
        by (unfold xbits; rewrite N.shiftr_0_r, N.mod_small by exact (proj1 SS); reflexivity).
      rewrite RTZ.
      split; [|split; [exact RSP | reflexivity]].
      reflexivity.
    + (* page-straddle entry unreachable: both pointers are page-safe *)
      exfalso. change (2^12) with 4096 in BC.
      rewrite (page_test0 ((p .| q) mod 4096)) in BC
        by (first [apply N.mod_lt; discriminate | exact PS]).
      discriminate.
Qed.
