(* a64l -- convert a base-64 string to a long

   SEMANTICS
   ---------
   a64l(str64) reads up to six base-64 digits from str64, least significant
   digit first, and returns their value.  It stops at the first byte that is
   not a digit.  glibc looks each byte up in a 77-entry table (a64l_table, in
   .rodata) indexed by c - '.', where 64 marks "not a digit", and accumulates
   the result in a 32-bit register.

   SPECIFICATION (man 3 a64l, Linux man-pages 5.10, Ubuntu 22.04)
   ---------------------------------------------------------------

     long a64l(const char *str64);

     These functions provide a conversion between 32-bit long integers and
     little-endian base-64 ASCII strings (of length zero to six).  If the
     string used as argument for a64l() has length greater than six, only
     the first six bytes are used.  If the type long has more than 32 bits,
     then l64a() uses only the low order 32 bits of value, and a64l() sign-
     extends its 32-bit result.

     The 64 digits in the base-64 system are:
            '.'  represents a 0
            '/'  represents a 1
            0-9  represent  2-11
            A-Z  represent 12-37
            a-z  represent 38-63

   FINDING
   -------
   glibc's a64l does NOT sign-extend.  The result is built in EDX/ECX/R8D
   and returned with MOV RAX,R8, so bits 32-63 of RAX are always zero.
   a64l_correct proves RAX = (digit sum) mod 2^32 on every path, and
   a64l_no_sign_extension instantiates it at ".....0", whose 32-bit result
   is 2^31: the man page requires -2^31, glibc returns +2^31.  This matches
   running the system libc: printf("%ld", a64l(".....0")) prints 2147483648.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol a64l at 0x151540 (Ghidra image base 0x100000); a64l_table
            at 0x2ccb00
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see a64l_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = str64; m = memory on entry, which holds glibc's a64l_table
            at 0x2ccb00 (it is in the read-only image).
   Output:  Let k <= 6 be the number of leading base-64 digits of str64
            (counting at most six).  On return
              RAX = (sum_{i<k} val(str64[i]) * 64^i) mod 2^32,
            where val is the man page's digit value.  Memory and RSP are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import a64l_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem a64l_nwc: forall s2 s1, a64l_amd64 s1 = a64l_amd64 s2.
Proof. reflexivity. Qed.

Theorem a64l_welltyped: welltyped_prog x64typctx a64l_amd64.
Proof. Picinae_typecheck. Qed.

Theorem a64l_preserves_memory:
  forall_endstates a64l_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem a64l_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates a64l_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The man page's digit alphabet and values. *)
Definition digitb (c:N) : bool :=
  ((46 <=? c) && (c <=? 57)) || ((65 <=? c) && (c <=? 90)) || ((97 <=? c) && (c <=? 122)).
Definition val (c:N) : N :=
  if c <=? 57 then c - 46 else if c <=? 90 then c - 53 else c - 59.

(* Value of the leading digits of the string at s + i, reading at most k. *)
Fixpoint digits (m:memory) (s i:N) (k:nat) : N :=
  match k with
  | O => 0
  | S k' => let c := m Ⓑ[s ⊕ i] in
            if digitb c then val c * 2^(6*i) + digits m s (i+1) k' else 0
  end.

Definition a64l_spec (m:memory) (s:N) : N := digits m s 0 6 mod 2^32.

(* glibc's table: entry c - '.' is val c for a digit c, and 64 otherwise. *)
Definition a64l_table : list N :=
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 64; 64; 64; 64; 64; 64; 64; 12; 13; 14;
   15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33;
   34; 35; 36; 37; 64; 64; 64; 64; 64; 64; 38; 39; 40; 41; 42; 43; 44; 45; 46;
   47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63].

Definition table_loaded (m:memory) :=
  forall i, i < 77 -> m Ⓑ[0x2ccb00 + i] = nth (N.to_nat i) a64l_table 0.

(* Value of the first k digits, when they are all digits. *)
Fixpoint psum (m:memory) (s:N) (k:nat) : N :=
  match k with
  | O => 0
  | S k' => psum m s k' + val (m Ⓑ[s ⊕ N.of_nat k']) * 2^(6 * N.of_nat k')
  end.

Definition alldig (m:memory) (s:N) (k:nat) :=
  forall i, i < N.of_nat k -> digitb (m Ⓑ[s ⊕ i]) = true.

Definition a64l_exit (t:trace) :=
  match t with (Addr 1381891,_)::_ => true | _ => false end.

(* After digit k (k = 1..4) the running value is in ECX (k odd) or EDX
   (k even).  The last segment covers digits 4 and 5. *)
Definition digit_inv (m:memory) (s rsp:N) (k:nat) (acc:var) (st:store) :=
  st V_MEM64 = m /\ st R_RDI = s /\ st R_RSI = 0x2ccb00 /\ st R_RSP = rsp /\
  alldig m s k /\ st acc = psum m s k.

Definition a64l_invs (m:memory) (s rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1381696 => Some (st V_MEM64 = m /\ st R_RDI = s /\ st R_RSP = rsp)
  | 1381735 => Some (digit_inv m s rsp 1 R_RCX st)
  | 1381768 => Some (digit_inv m s rsp 2 R_RDX st)
  | 1381797 => Some (digit_inv m s rsp 3 R_RCX st)
  | 1381826 => Some (digit_inv m s rsp 4 R_RDX st)
  | 1381891 => Some (st R_RAX = a64l_spec m s /\ st R_RSP = rsp)
  | _ => None
  end | _ => None end.

(* The digit test and table lookup glibc performs on one byte b:
   ja b <> 0 is "c - '.' > 76 (unsigned)", and tval b is the table entry. *)
Definition ja (b:N) : N :=
  ((if msub 32 (scast 8 32 b) 46 <? 76 then 1 else 0) .| (if scast 8 32 b mod 2^32 =? 122 then 1 else 0)) .^ 1.
Definition tval (b:N) : N := nth (N.to_nat (msub 32 (scast 8 32 b) 46)) a64l_table 0.
Definition byte_ok (b:N) : bool :=
  if ja b =? 0 then
    (msub 32 (scast 8 32 b) 46 <? 77) &&
    Bool.eqb (scast 8 32 (tval b) mod 2^32 =? 64) (negb (digitb b)) &&
    (negb (digitb b) || (scast 8 32 (tval b) mod 2^32 =? val b))
  else negb (digitb b).

(* glibc's table agrees with the man page's alphabet on every byte. *)
Lemma all_bytes_ok: forall b, b < 256 -> byte_ok b = true.
Proof.
  assert (H: forallb byte_ok (map N.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  intros b B. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (N.to_nat b).
  split. apply N2Nat.id. apply in_seq. lia.
Qed.

Lemma byte_nondigit: forall b, b < 256 -> ja b <> 0 -> digitb b = false.
Proof.
  intros b B J. pose proof (all_bytes_ok b B) as H. unfold byte_ok in H.
  destruct (N.eqb_spec (ja b) 0) as [E|_]. contradiction. apply Bool.negb_true_iff, H.
Qed.

Lemma byte_digit: forall b, b < 256 -> ja b = 0 ->
  msub 32 (scast 8 32 b) 46 < 77 /\
  (scast 8 32 (tval b) mod 2^32 =? 64) = negb (digitb b) /\
  (digitb b = true -> scast 8 32 (tval b) mod 2^32 = val b).
Proof.
  intros b B J. pose proof (all_bytes_ok b B) as H. unfold byte_ok in H. rewrite J in H. cbn [N.eqb] in H.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  split. apply N.ltb_lt, H1. split. apply Bool.eqb_prop, H2.
  intro D. rewrite D in H3. apply N.eqb_eq, H3.
Qed.

Lemma table_read: forall (m:memory) b, table_loaded m -> b < 256 -> ja b = 0 ->
  m Ⓑ[2935552 ⊕ msub 32 (scast 8 32 b) 46 ⊗ 1] = tval b.
Proof.
  intros m b T B J. destruct (byte_digit b B J) as [E _].
  unfold tval. rewrite <- T by exact E. f_equal.
  change (2^64) with 18446744073709551616. rewrite N.mul_1_r.
  rewrite (N.mod_small (msub 32 _ _)) by lia. apply N.mod_small. lia.
Qed.

Lemma lor_shift_add: forall p v n, p < 2^n -> (v << n) .| p = v * 2^n + p.
Proof.
  intros p v n P. rewrite N.lor_comm, lor_plus. rewrite N.shiftl_mul_pow2. lia.
  apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0.
  destruct (N.ltb_spec i n).
  - rewrite N.shiftl_spec_low by assumption. apply Bool.andb_false_r.
  - rewrite <- (N.mod_small p (2^n)) by exact P. rewrite N.mod_pow2_bits_high by assumption. reflexivity.
Qed.

Lemma digits_split:
  forall m s k, (k <= 6)%nat -> alldig m s k ->
  digits m s 0 6 = psum m s k + digits m s (N.of_nat k) (6 - k).
Proof.
  intros m s k. induction k as [|k IH]; intros K A.
  - reflexivity.
  - rewrite IH by (lia || (intros i I; apply A; lia)).
    replace (6 - k)%nat with (S (6 - S k)) by lia. cbn [digits psum].
    rewrite A by lia. rewrite Nat2N.inj_succ, <- N.add_1_r. lia.
Qed.

Lemma val_lt: forall c, digitb c = true -> val c < 64.
Proof.
  intros c D. unfold digitb in D. unfold val.
  repeat match goal with H: context [?a <=? ?b] |- _ => destruct (N.leb_spec a b) end;
  repeat match goal with |- context [?a <=? ?b] => destruct (N.leb_spec a b) end;
  cbn in *; try discriminate; lia.
Qed.

Lemma psum_lt: forall m s k, alldig m s k -> psum m s k < 2^(6 * N.of_nat k).
Proof.
  intros m s k. induction k as [|k IH]; intro A.
  - cbn. lia.
  - cbn [psum]. rewrite Nat2N.inj_succ, N.mul_succ_r, N.pow_add_r.
    assert (V: val (m Ⓑ[s ⊕ N.of_nat k]) < 64) by (apply val_lt, A; lia).
    assert (P: psum m s k < 2^(6 * N.of_nat k)) by (apply IH; intros i I; apply A; lia).
    change (2^6) with 64. nia.
Qed.

Lemma spec_stop: forall m s k, (k < 6)%nat -> alldig m s k -> digitb (m Ⓑ[s ⊕ N.of_nat k]) = false ->
  a64l_spec m s = psum m s k.
Proof.
  intros m s k K A D. unfold a64l_spec. rewrite (digits_split m s k) by (lia || exact A).
  replace (6 - k)%nat with (S (5 - k)) by lia. cbn [digits]. rewrite D, N.add_0_r.
  apply N.mod_small. eapply N.lt_le_trans. apply psum_lt, A.
  apply N.pow_le_mono_r. discriminate. lia.
Qed.

Lemma spec_full: forall m s, alldig m s 6 -> a64l_spec m s = psum m s 6 mod 2^32.
Proof.
  intros m s A. unfold a64l_spec. rewrite (digits_split m s 6) by (lia || exact A).
  cbn [digits Nat.sub]. rewrite N.add_0_r. reflexivity.
Qed.

Lemma alldig_succ: forall m s k, alldig m s k -> digitb (m Ⓑ[s ⊕ N.of_nat k]) = true -> alldig m s (S k).
Proof.
  intros m s k A D i I. rewrite Nat2N.inj_succ in I.
  destruct (N.lt_ge_cases i (N.of_nat k)). apply A, H. replace i with (N.of_nat k) by lia. exact D.
Qed.

Lemma psum_succ: forall m s k, psum m s (S k) = psum m s k + val (m Ⓑ[s ⊕ N.of_nat k]) * 2^(6 * N.of_nat k).
Proof. reflexivity. Qed.

(* The two ways a segment ends: the byte at offset k is not a digit (return
   the value so far), or it is (add its value at bit 6k). *)
Lemma stop_goal: forall m s k acc, (k < 6)%nat -> alldig m s k ->
  digitb (m Ⓑ[s ⊕ N.of_nat k]) = false -> acc = psum m s k -> acc mod 2^32 = a64l_spec m s.
Proof.
  intros m s k acc K A D E. subst acc. rewrite (spec_stop m s k K A D). apply N.mod_small.
  eapply N.lt_le_trans. apply psum_lt, A. apply N.pow_le_mono_r. discriminate. lia.
Qed.

Lemma cont_goal: forall m s k tv, alldig m s k -> digitb (m Ⓑ[s ⊕ N.of_nat k]) = true ->
  scast 8 32 tv mod 2^32 = val (m Ⓑ[s ⊕ N.of_nat k]) ->
  (scast 8 32 tv << (6 * N.of_nat k) .| psum m s k) mod 2^32 = psum m s (S k) mod 2^32.
Proof.
  intros m s k tv A D V. rewrite N.mod_small in V by apply ofZ_bound. rewrite V.
  rewrite lor_shift_add by (apply psum_lt, A). rewrite psum_succ. f_equal. lia.
Qed.

Lemma cont_exact: forall m s k tv, alldig m s k -> digitb (m Ⓑ[s ⊕ N.of_nat k]) = true ->
  scast 8 32 tv mod 2^32 = val (m Ⓑ[s ⊕ N.of_nat k]) ->
  (scast 8 32 tv << (6 * N.of_nat k) .| psum m s k) = psum m s (S k).
Proof.
  intros m s k tv A D V. rewrite N.mod_small in V by apply ofZ_bound. rewrite V.
  rewrite lor_shift_add by (apply psum_lt, A). rewrite psum_succ. lia.
Qed.

Lemma psum_small: forall m s k, (k <= 5)%nat -> alldig m s k -> psum m s k mod 2^32 = psum m s k.
Proof.
  intros m s k K A. apply N.mod_small. eapply N.lt_le_trans. apply psum_lt, A.
  apply N.pow_le_mono_r. discriminate. lia.
Qed.

Ltac a64l_classify m TBL :=
  repeat match goal with H: context [(if msub 32 (scast 8 32 ?b) 46 <? 76 then 1 else 0)] |- _ =>
    change (((if msub 32 (scast 8 32 b) 46 <? 76 then 1 else 0) .| (if scast 8 32 b mod 2^32 =? 122 then 1 else 0)) .^ 1)
      with (ja b) in H end;
  repeat match goal with
  | H: ja ?b = N.pos _ |- _ =>
      let ND := fresh "ND" in
      assert (ND: digitb b = false) by (apply byte_nondigit; [apply (getmem_bound 64 LittleE 1) | rewrite H; discriminate]);
      clear H
  | H: ja ?b = 0 |- _ =>
      let Bb := fresh "Bb" in let T := fresh "T" in let V := fresh "V" in
      assert (Bb: b < 256) by apply (getmem_bound 64 LittleE 1);
      rewrite (table_read m b TBL Bb H) in *;
      destruct (byte_digit b Bb H) as [_ [T V]]; rewrite T in *; clear H T
  end;
  repeat match goal with H: negb ?x = true |- _ => apply Bool.negb_true_iff in H
                       | H: negb ?x = false |- _ => apply Bool.negb_false_iff in H end.

Theorem a64l_correct:
  forall st t s' x' m s rsp
         (ENTRY: startof t (x',s') = (Addr 1381696, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (S: st R_RDI = s) (RSP: st R_RSP = rsp)
         (TBL: table_loaded m),
  satisfies_all a64l_amd64 (a64l_invs m s rsp) a64l_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply a64l_welltyped. intro MDL1.
  clear - PRE MDL1 TBL. rename t1 into t.
  destruct_inv 64 PRE.
  (* digit 0 *)
  1: { destruct PRE as [MEM [SRDI RSP]].
    repeat x64_step; a64l_classify m TBL.
    all: assert (B0: m Ⓑ[s ⊕ N.of_nat 0] = m Ⓑ[s]) by (cbn [N.of_nat]; rewrite N.add_0_r; apply getmem_mod_l).
    1,3: split; [ rewrite <- (N.mod_0_l (2^32)) at 1 by discriminate;
                  apply (stop_goal m s 0); [lia | intros i I; cbn in I; lia | rewrite B0; assumption | reflexivity]
                | assumption ].
    repeat (split; [reflexivity|]). split. assumption. split.
      apply (alldig_succ m s 0). intros i I; cbn in I; lia. rewrite B0; assumption.
      rewrite V by assumption. rewrite psum_succ, B0. cbn. lia. }
  (* digits 1-3: the running value is in RCX, RDX, RCX *)
  all: destruct PRE as [MEM [SRDI [RSI [RSP [A ACC]]]]]; repeat x64_step; a64l_classify m TBL.
  all: try match goal with A: alldig ?m ?s ?k |- _ mod 2^32 = a64l_spec ?m ?s /\ _ =>
         split; [ apply (stop_goal m s k); [lia | exact A | assumption | reflexivity] | assumption ] end.
  all: try match goal with A: alldig ?m ?s ?k |- _ = _ /\ _ = _ /\ _ = _ /\ _ = _ /\ alldig ?m ?s _ /\ _ =>
         repeat (split; [reflexivity|]); split; [assumption|]; split;
         [ apply (alldig_succ m s k); [exact A | assumption]
         | rewrite <- (psum_small m s (S k)) by (lia || (apply (alldig_succ m s k); [exact A | assumption]));
           apply (cont_goal m s k); [exact A | assumption | apply V; assumption] ] end.
  (* digits 4 and 5: stop after digit 4, or after all six *)
  all: assert (A5: alldig m s 5) by (apply (alldig_succ m s 4); [exact A | assumption]).
  all: change 24 with (6 * N.of_nat 4).
  all: rewrite (cont_exact m s 4) by
         (exact A || assumption ||
          match goal with H: digitb (_ Ⓑ[_ ⊕ 4]) = true -> _ |- _ => apply H; assumption end).
  1,3: split; [ apply (stop_goal m s 5); [lia | exact A5 | assumption | reflexivity] | assumption ].
  split; [|assumption].
  rewrite (spec_full m s) by (apply (alldig_succ m s 5); [exact A5 | assumption]).
  change 30 with (6 * N.of_nat 5).
  apply (cont_goal m s 5); [exact A5 | assumption |].
  match goal with H: digitb (_ Ⓑ[_ ⊕ 5]) = true -> _ |- _ => apply H; assumption end.
Qed.

(* The result is always zero-extended: bits 32-63 of RAX are clear. *)
Theorem a64l_zero_extends: forall m s, a64l_spec m s < 2^32.
Proof. intros. apply N.mod_lt. discriminate. Qed.

(* The man page says a64l sign-extends its 32-bit result.  For ".....0" the
   32-bit result is 2^31, so a sign-extending a64l would return -2^31
   (0xffffffff80000000 in RAX); glibc returns +2^31. *)
Theorem a64l_no_sign_extension:
  forall (m:memory) s,
  m Ⓑ[s ⊕ 0] = 46 -> m Ⓑ[s ⊕ 1] = 46 -> m Ⓑ[s ⊕ 2] = 46 ->
  m Ⓑ[s ⊕ 3] = 46 -> m Ⓑ[s ⊕ 4] = 46 -> m Ⓑ[s ⊕ 5] = 48 ->
  a64l_spec m s = 2^31 /\ a64l_spec m s <> scast 32 64 (a64l_spec m s).
Proof.
  intros m s B0 B1 B2 B3 B4 B5.
  assert (E: a64l_spec m s = 2^31).
  { unfold a64l_spec. cbn [digits N.add Pos.add Pos.succ]. rewrite B0, B1, B2, B3, B4, B5. vm_compute. reflexivity. }
  split. exact E. rewrite E. vm_compute. discriminate.
Qed.
