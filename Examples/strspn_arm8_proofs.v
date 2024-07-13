(* Proofs using Picinae for ARM8 Architecture

   Picinae System:
     Copyright (c) 2023 Kevin W. Hamlen
     Computer Science Department
     The University of Texas at Dallas

   These proofs written by:
     Ilan Buzzetti      (Ilan.Buzzetti@UTDallas.edu)
     Navaneeth Nambiar  (Navaneeth.Nambiar@UTDallas.edu)
     Cole Salvato       (Cole.Salvato@UTDallas.edu)
     William Zhuo       (William.Zhuo@UTDallas.edu)

   Any use, commercial or otherwise, requires the express permission of
   the author.

   To run this module, first load and compile:
   * Picinae_core
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_armv8_pcode
   * strspn_arm8
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import strspn_arm8.
Require Import Lia.
Require Import Bool.

(* Only used for bookkeeping *)
Require Import String.


Import ARM8Notations.
Open Scope N.


(* Define post-condition points for strlen: *)
Definition strspn_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1093664872 => true (* UPDATED *)
  | _ => false
  end | _ => false end.

(* The ARM8 lifter creates non-writable code sections. *)
Theorem strspn_nwc: ∀ s2 s1, musl_armv8_a_strspn_armv8 s1 = musl_armv8_a_strspn_armv8 s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem strspn_welltyped: welltyped_prog arm8typctx musl_armv8_a_strspn_armv8.
Proof.
  Picinae_typecheck.
Qed.

(* Strspn does not corrupt memory. *)
Theorem strspn_preserves_memory32:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Strspn does not modify page permissions. *)
Theorem strspn_preserves_readable:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Strspn does not corrupt the LR register (call-return safety). *)
Theorem strspn_preserves_lr:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.


(* Extract a bit from a bit-array. *)
Definition bit mem (p:addr) (i:N) := xbits (mem Ⓑ[p + (i >> 3)]) (i mod 2^3) 1.

(* Define what it means for a nil-terminated string to not have internal nils. *)
Definition nilfree mem p len :=
  ∀ i, i < len -> 0 < mem Ⓑ[ p ⊕ i ].

(* Added the two fixpoints below to describe a memory state that's been updated
   to reflect the characters from an accept string in a bitmap datastructure.

   TODO: Change the invariants to describe an updated memory and prove
         the lemma bitarray_nstr_incr to prove the map-maker loop invariant.
 *)
Fixpoint nilfree_b mem p (len:nat) : bool :=
  (0 <? mem Ⓑ[ p ⊕ (N.of_nat len) ]) &&
  match len with
    | O => true
    | S len' => nilfree_b mem p len'
  end.

Fixpoint bitmap_updated (m:addr->N) (bitmap_ptr accept_ptr:addr) (k:nat) : addr -> N :=
  let m' := match k with
           | O => m
           | S k' => bitmap_updated m bitmap_ptr accept_ptr k'
           end
    in
  if nilfree_b m' accept_ptr k then
    (* This formula copy-pasted-modified from picinae' *)
    (* m [Ⓠ bitmap_ptr + (m Ⓑ[ accept_ptr + k ] >> 6 << 3)
                  := 1 << m Ⓑ[ accept_ptr + k ] mod 64
                     .| m Ⓠ[ bitmap_ptr + (m Ⓑ[ accept_ptr + k ] >> 6 << 3) ] *)
    let char := m' Ⓑ[ accept_ptr + (N.of_nat k) ] in
    let quadrant_index := char >> 6 << 3 in
    let char_offset := char mod 64 in
    m' [Ⓠ bitmap_ptr + quadrant_index
                  := 1 << char_offset
                     .| m' Ⓠ[ bitmap_ptr + quadrant_index ]]
  else m'.

Lemma bitarray_nstr_incr:
  forall m m' L accept_ptr bitmap_ptr
  (MEM: m' = m [Ⓠ bitmap_ptr + (m Ⓑ[ accept_ptr + L ] >> 6 << 3)
                  := 1 << m Ⓑ[ accept_ptr + L ] mod 64
                     .| m Ⓠ[ bitmap_ptr + (m Ⓑ[ accept_ptr + L ] >> 6 << 3) ]])
  (BITNSTR: bitarray_nstr m bitmap_ptr accept_ptr L)
  (CHAR: m Ⓑ[ accept_ptr + L ] ≠ 0),
  bitarray_nstr m' bitmap_ptr accept_ptr (L+1).
Proof.
Admitted.

(* Question: bitarray_nstr is for i < 256, while we expect only
   characters with value 127 or less. This means our map will
   only be half (128) of the maximum (256) size.
   Will this be an issue? *)
(* Define a "correct" bit array. *)
(* nilfree m p **(1+j)** so that p[j] != 0.
   This makes it so a bitmap never records the null-terminating character
   as an acceptable character which is the behavior used in this implementation
   of strspn. This is practical in this case but may not be in others. *)
Definition bitarray_nstr mem bitmap_ptr str_ptr len : Prop :=
  ∀ i, i < 256 -> (0 < bit mem bitmap_ptr i <-> 
                       (∃ j, j < len /\ nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr ⊕ j] = i)).

(* bitmap bit is on iff the string has a corresponding character before or on \0 *)
Definition bitarray_str mem bitmap_ptr str_ptr : Prop :=
  ∀ i, i < 256 -> (0 < bit mem bitmap_ptr i <-> 
                       (∃ j, nilfree mem str_ptr (1+j) /\ mem Ⓑ[str_ptr ⊕ j] = i)).

(* accept string contains all characters of str's i-length prefix.
 *)
Definition post_satis_i (i:N) (m:addr -> N) (str_ptr:addr) (accept_ptr:addr):= 
  ∀j, j < i -> 
  (∃ k : N, nilfree m accept_ptr (k + 1)
    ∧ m Ⓑ[ accept_ptr ⊕ k ] = m Ⓑ[ str_ptr ⊕ j ]).

Lemma npred_1_plus_i : forall i, N.pred (1+i) = i.
Proof.
Admitted.

Lemma lt_succ_imp_lte_pred : forall j i, j < 1 + i -> j <= i.
Proof.
  intros. 
  apply N.lt_le_pred in H. rewrite npred_1_plus_i in H.
  assumption.
Qed.

Lemma le_imp_lt_eq: forall i x, i <= x -> i < x \/ i = x.
Proof. Admitted.

Lemma byte_upper_bound: forall i mem, mem Ⓑ[ i ] < 256.
Proof.
 intros.
 apply (getmem_bound 64 LittleE 1 mem i).
Qed.

Lemma zero_or_gtz: forall n:N, n = 0 \/ 0 < n.
Proof.
  intros. destruct n. left. reflexivity. right. reflexivity.
Qed.

Lemma nilfree_prefx :
  ∀ mem p x y
    (NILFREE : nilfree mem p x)
    (LT : y < x),
  nilfree mem p y.
Proof.
  intros. unfold nilfree in NILFREE; unfold nilfree.
  intros. apply NILFREE. apply (N.lt_trans i y x); repeat assumption.
Qed.

(* If the post condition is satisfied for a prefix of length i, and the next character (index i)
   is not zero and in the bitmap then the post condition is satisfied for a prefix of length i+1
 *)
Lemma post_satis_incr :
  ∀ i char mem str_ptr accept_ptr bitmap_ptr 
     (POST:   post_satis_i i mem str_ptr accept_ptr   )
     (BITMAP: bitarray_str mem bitmap_ptr accept_ptr  )
     (NEXT:   mem Ⓑ[ str_ptr ⊕ i ] = char            )
     (CHAR_BIT:     bit mem bitmap_ptr char = 1       )
     (CHAR_NOT_NIL: 0 < char                          ),
     post_satis_i (1+i) mem str_ptr accept_ptr.
Proof.
  intros.
  remember BITMAP as BITMAP2. clear HeqBITMAP2.
  unfold post_satis_i. intros. 
  apply lt_succ_imp_lte_pred in H.
  apply le_imp_lt_eq in H. destruct H.
    unfold post_satis_i in POST. specialize (POST j). apply POST in H. assumption.
    unfold bitarray_str in BITMAP; specialize (BITMAP char); destruct BITMAP.
    rewrite <-NEXT; apply byte_upper_bound.
    rewrite CHAR_BIT in H0; destruct H0. apply N.lt_0_1. subst j.
    destruct H0 as [NILFREE CHAR].
    exists x. split.
    assert (H: ∃ j : N, nilfree mem accept_ptr j ∧ mem Ⓑ[ accept_ptr ⊕ j ] = char).
      { exists x. split; repeat assumption. 
        apply (nilfree_prefx mem accept_ptr (1+x) x). assumption. lia. }
      rewrite N.add_comm; assumption.
    subst char; assumption.
Qed.

Lemma mod_comm:
  ∀ x y, x ⊕ y = y ⊕ x.
Proof.
  intros. simpl. rewrite N.add_comm. reflexivity.
Qed.


Lemma nilfree_lte :
  ∀ mem accept_ptr j len, 
  nilfree mem accept_ptr j /\ mem Ⓑ[ accept_ptr ⊕ len ] = 0 
  -> j <= len.
Proof.
  intros mem accept_ptr j len [J Len].
  unfold nilfree in J.
  specialize (N.le_gt_cases j len); intro Disj.
  destruct Disj as [Lte | Gt].
  assumption.
  specialize J with len. apply J in Gt. rewrite Len in Gt. discriminate.
Qed.

Lemma bitarray_nstr_str :
  ∀ len mem accept_ptr bitmap_ptr
     (BITNSTR: bitarray_nstr mem bitmap_ptr accept_ptr len)
     (NIL: mem Ⓑ[ accept_ptr ⊕ len ] = 0),
     bitarray_str mem bitmap_ptr accept_ptr.
Proof.
unfold bitarray_nstr.
unfold bitarray_str.
intros. 
split.
  * intro BIT. apply BITNSTR in BIT. destruct BIT as [j [LEN [NILFREE MEM]]]. exists j. split.
  assumption. assumption. assumption.
  *
 intro H2; destruct H2 as [j [NILFREE MEM]]. apply BITNSTR. assumption. exists j. split.
  assert (TRI:= N.lt_trichotomy j len). destruct TRI as [LT | [EQ | GT]].
    assumption.
    subst j. unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + len). { lia. } apply NILFREE in H1. 
      rewrite NIL in H1. discriminate.
    unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + j). { lia. } apply NILFREE in H1.
      rewrite  NIL in H1. discriminate.
  split; assumption; assumption.
Qed.

Definition strspn_invs (m:addr->N) (str_ptr accept_ptr sp:addr) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  (* 0x4130001c: Entry invariant *)
  |  0x4130001c => Some ( s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠaccept_ptr /\ s R_X3 = Ⓠsp)
  (* 0x41300054: Degenerative Loop (len(accept)==1) *)
  |  0x41300054 => Some( 
     ∃ invariant_loc, invariant_loc = "0x41300054"%string ->
     ∃ L : N, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(str_ptr ⊕ L) /\
     ∀ i : N,  i < L → m Ⓑ[ accept_ptr ] = m Ⓑ[ str_ptr + i ])
  (* 0x4130002c: Map Maker Loop *)
  |  0x4130002c =>  Some( 
     ∃ invariant_loc, invariant_loc = "0x4130002c"%string ->
     ∃ bitmap_ptr L : N, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(accept_ptr ⊕ L)
      /\ s R_X6 = Ⓠ1 /\
     m Ⓑ[ accept_ptr ] ≠ 0 /\ m Ⓑ[ 1 + accept_ptr ] ≠ 0 /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_nstr m bitmap_ptr accept_ptr L)
  (* 0x41300094: Map Maker->Checker Transition 
                 Just turn bitarray_nstr to bitarray_str to make
                 the map checker loop simpler. *)
  |  0x41300094 => Some(
     ∃ invariant_loc, invariant_loc = "0x41300094"%string ->
     ∃ bitmap_ptr L, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(accept_ptr ⊕ L) /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m bitmap_ptr accept_ptr)
  (* 0x41300078: Map Checker Loop *)
  |  0x41300078 => Some( 
     ∃ invariant_loc, invariant_loc = "0x41300078"%string ->
     ∃ bitmap_ptr L : N, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(str_ptr ⊕ L) /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m bitmap_ptr accept_ptr /\
     post_satis_i L m str_ptr accept_ptr)
  (* 0x41300068: Return Invariant *)
  |  0x41300068 => Some(
     ∃ invariant_loc, invariant_loc = "0x41300068"%string ->
     ∃ L : N,
     s R_X0 = ⓆL ∧ post_satis_i L m str_ptr accept_ptr
                    ∧ ¬ post_satis_i (L+1) m str_ptr accept_ptr)
  | _ => None
  end | _ => None end.


Lemma byte0_bits0: 
  ∀ m bp i, i<8 /\ m Ⓑ[ bp ] = 0 -> bit m bp i = 0.
Proof.
  intros. destruct H.
  unfold bit. unfold xbits. psimpl. destruct i.
    psimpl. rewrite H0. psimpl. reflexivity.
    rewrite H0. psimpl. reflexivity. 
Qed.

(* Induction Example: Picinary_theory.getmem_bound *)
(* First version is not quite right because with len = 0
   we're not getting any bits out of memory, but we're 
   claiming `bit m a 0 = 0`, which we can't guarantee.
   We can't guarantee something given nothing.

   The real base case we have in mind is when len = 1.
   This gives us information about, namely it equals 0
   and for this we can show that all bits are 0. See
   the lemma `byte0_bits0` above. *)
Lemma val0_bits0_v1:
  ∀ len m a, getmem 64 LittleE len m a = 0 -> ∀ i, i < 2^(Mb*len) -> bit m a i = 0.
Proof.
  induction len using N.peano_ind; intros. simpl in H0. destruct i.
Abort.


Lemma val0_bits0_v2:
  ∀  len m a, getmem 64 LittleE len m a = 0 /\ 0 < len
    ->  ∀ i, i < 2^(Mb*len) -> bit m a i = 0.
Proof.
  induction len using N.peano_ind; intros; destruct H. inversion H1.
  unfold bit. unfold xbits. 
Abort.


Lemma bitmap_0:
  ∀ m sp ap, m Ⓨ[ sp ] = 0 -> bitarray_nstr m sp ap 0.
Proof.
  intros.
  unfold bitarray_nstr.

  intros. split; intros.
  unfold bit in H1. unfold xbits in H1.
Admitted.

(* Main correctness theorem (and proof): *)

(* TODO:
      *  Prove the admits...
*)
Theorem strspn_partial_correctness:
  ∀ s str_ptr accept_ptr sp m t s' x'
         (* Enter right after "st1" instruction that prepares
            the bitmap. This skips 2 things worth mentioning:
              1) The stackpointer is subtracted 0x20 to make room
                 for the bitmap.
              2) the first character of 'accept_ptr' is loaded
                 into w2. *)
         (ENTRY: startof t (x',s') = (Addr 0x4130001c,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = Ⓜm) 
         (STR: s R_X0 = Ⓠstr_ptr) 
         (ACPT:  s R_X1 = Ⓠaccept_ptr)
         (SP: s R_X3 = Ⓠsp)
         (* Assume the bitmap addressed by X3 is zero'd because
            the lifted "st1" instruction that does this isn't
            implemented. *)
         (BITMAP: m Ⓨ[ sp ] = 0)
         (CHAR0: Ⓠ (m Ⓑ[ accept_ptr ]) = s R_X2) 
,
  satisfies_all musl_armv8_a_strspn_armv8 (strspn_invs m str_ptr accept_ptr sp) strspn_exit ((x',s')::t).
Proof.
Local Ltac step := time arm8_step.
intros.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY. step. split; try (assumption || split; assumption).

  (* Inductive cases *)
  intros. 
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strspn_welltyped).
  (* erewrite strspn_preserves_memory32 in MEM by eassumption. *)
  assert (MEM': s1 V_MEM64 = Ⓜm). { admit. }
  (* ASSUMPTION PRESERVATION
     Our capturing of str_ptr and accept_ptr means we rely on 
     s - the initial state.
     How do we update the hypotheses into s1?
     The assert+admits below are a placeholder. *)
  (*assert (STR': s1 R_X0 = Ⓠstr_ptr). { admit. }
  assert (ACPT' : s1 R_X1 = Ⓠaccept_ptr). { admit. }*)
  assert (SP' : s1 R_X3 = Ⓠsp). { admit. }
  assert (BITMAP': m Ⓨ[ sp ] = 0). { admit. }
  assert (CHAR0': s1 R_X2 = Ⓠ (m Ⓑ[ accept_ptr ])). { admit. }
  clear - PRE MDL MEM' SP' BITMAP' CHAR0'. rename t1 into t. rename s1 into s.
  rename SP' into SP.
  rename BITMAP' into BITMAP. rename CHAR0' into CHAR0.
  rename MEM' into MEM.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 64 PRE.
  destruct PRE as [STR [ACPT BMP]].
  step. step. step. 
  
  (* RET: Accept string empty *)
  step. exists "0x41300068"%string. intro LOC. 
  apply Neqb_ok in BC.
  exists 0. split. reflexivity. split.
  Check N.nlt_0_r.
  unfold post_satis_i.
  intros. apply N.nlt_0_r in H. contradiction.
  unfold post_satis_i. unfold not. intros.
    specialize (H 0). simpl N.add in H. destruct H. apply N.lt_0_1.
    psimpl in H. assert (Disj:= N.lt_trichotomy x 0). destruct Disj as [Lt | [Eq | Gt]].
    apply N.nlt_0_r in Lt. contradiction.
    subst x. psimpl in H. destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0).
      assert (H:= N.lt_0_1). apply NILFREE in H. psimpl in H. rewrite BC in H. lia.
    destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0). assert (H: 0<1+x). lia.
      apply NILFREE in H. psimpl in H; rewrite BC in H; lia.

  (* TODO: clean and rename m0 into m. *)
  apply N.eqb_neq in BC; remember BC as ACPT_0_NNULL; clear HeqACPT_0_NNULL.
  step. 
  step. step. 
  (* SINGLE CHARACTER: This is the first loop iteration. *)
  step. exists "0x41300054"%string. intro LOC.
    exists 0. split; try (assumption || reflexivity). split.
    psimpl; reflexivity. intros. apply N.nlt_0_r in H. contradiction.

  apply N.eqb_neq in BC0; remember BC0 as ACPT_1_NNULL; clear HeqACPT_1_NNULL.
  step.
  (* MAP BUILDER: This is the first loop iteration. *)
  apply N.eqb_neq in BC. apply N.eqb_neq in BC0.
  exists "0x4130002c"%string. intro LOC.
  (* sp was stored in R_X3 *) 
  exists sp.
  (* First loop iteration, length should be 0 *)
  exists 0. psimpl. split; try assumption. split; try reflexivity. split; try assumption. split.
  split; try assumption. split; try assumption. split; try assumption.
  (* Figure out why ACPT_1_NNUL uses m0 while ACPT_0_NNULL uses m.
     Maybe strspn relies on accept string not overlapping with the bitmap. *)
  apply bitmap_0. apply BITMAP.

  destruct PRE as [loc [bitmap_ptr [L [H0 H1]]]].
  (* Our bookkeeping strategy introduces a new goal
     when destructing invariants:
    ------------------------------------(1/4)
     loc = "0x41300030"%string
  *)
  admit.
  destruct H1 as [ACCEPTL [X6_EQ_1 [ACPT_0_NNULL [ACPT_1_NNULL [BITMAP_PTR BITNSTR]]]]].

  (* MAP BUILDER->CHECKER TRANSITION: only executed once*)
  step. step. (* For map-maker inv at *2c: step. apply Neqb_ok in BC. contradiction.*)
  exists "0x41300094"%string. intros. exists bitmap_ptr. exists L.
  split. assumption. split. reflexivity. split. assumption. apply bitarray_nstr_str with (len:=L). assumption.
  apply Neqb_ok in BC.
  (*
  BC : m0 Ⓑ[ accept_ptr + L ] = 0
  ______________________________________(1/5)
  m Ⓑ[ accept_ptr ⊕ L ] = 0
  *)
  admit.

  step. step.
  (* n introduced: 
      lsl x2, x6, x2 == x2 := x6 << (0x3f & x6) 
   *) step.
  step.  step. 
  (* Store the character-bit in the bitmap: *) step.
  step.
  (* MAP BUILDER: This is the arbitrary loop iteration. *)
  exists "0x41300030"%string. intro LOC.
  exists bitmap_ptr. exists (L+1). psimpl; split;
    try assumption; split; try reflexivity; split; try assumption.
    split; try assumption.
  split. rewrite <-BITMAP_PTR; rewrite <-SP; reflexivity.
  unfold bitarray_nstr.
  admit.




  destruct PRE as [loc [p H]]. admit. destruct H as [L [STR_PTR [LEN PREFIX]]].
  step. step.  step.
  (* SINGLE CHARACTER: This is the arbitrary loop iteration. *)
  step. exists "0x41300054"%string. intro LOC.
  exists p. exists (1+L). 
    split. assumption.
    split. psimpl. reflexivity.
    intros. apply PREFIX.
  admit.

  
  step. 
  (* RET: Single character fall-through *)
  step. exists "0x41300068"%string. intro LOC.
  exists L. split. admit.
    split. unfold post_satis. exists 0. split.
      psimpl. admit.
      psimpl. apply PREFIX. apply H.
    unfold post_satis.
    admit.

  destruct PRE as [loc [bitmap_ptr H]]. admit. destruct H as [p [L [STR_PTR [LEN [BITMAP_PTR [BITARRAY POST]]]]]].
  step. step. step.
  (* RET: Map checker fails to match *) 
  step. exists "0x41300068"%string. intro LOC. 
  exists (L mod 2 ^ 64). split.
    reflexivity.
    intros. split.

      (* apply post_satis_prev *) admit.
      admit.

  step. step. step. step. step. step.
  (* RET: Map checker reaches end of string *)
  step. exists "0x41300068"%string. intro LOC.
  exists L. split.
    (* apply Q_address_eq. *) psimpl. admit. (* Q_address_eq was the unproven statement Ⓠa = Ⓠb <-> a mod 64 = b mod 64*)
    intros. split. 
      (* apply post_satis_prev *) admit.
      admit.


  (* MAP CHECKER: This is the first loop iteration. *)
  step. exists "0x41300078"%string. intro LOC.
  exists bitmap_ptr. exists p. exists (L+1). psimpl.
  split. assumption. split. try reflexivity. split. symmetry in SP. 
  rewrite BITMAP_PTR in SP. assumption.
  split. assumption.
  (* TODO: continue here restructuring the proof and breaking the PREs*)
  (* k is unknown, but the statement is still true *)
  unfold post_satis.
  intros. 
  admit.
  (* intros. destruct H1 as [j [HL _]]. apply N.nlt_0_r in HL. contradiction. *)

  step. step. (* step. step. step. step. step. *)

  
  destruct PRE as [locstring [p H1]]. admit. destruct H1 as [p0 [L [sRx0 [sRx1 [sRx3 IH]]]]].
  (* step. step. step. step. step. step. *)


  (* MAP CHECKER: This is the arbitrary loop iteration. *)
  exists "0x41300078"%string. intro LOC.
  exists (p). exists p0. exists (0).
  rewrite <- sRx0. 
      split. symmetry. assumption.
      split. rewrite sRx0 in Hsv. inversion Hsv. rewrite <- H0. psimpl. reflexivity.
      split. assumption.
      split.
        apply IH. 
        unfold post_satis. 
          psimpl.
          admit.

Abort.