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
Theorem strspn_nwc: forall s2 s1, musl_armv8_a_strspn_armv8 s1 = musl_armv8_a_strspn_armv8 s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem strspn_welltyped: welltyped_prog arm8typctx musl_armv8_a_strspn_armv8.
Proof.
  Picinae_typecheck.
Qed.

(* Strspn does not corrupt memory. *)
Theorem strspn_preserves_memory:
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
  forall i, i < len -> 0 < mem Ⓑ[ p ⊕ i ].

(* Question: bitarray_nstr is for i < 256, while we expect only
   characters with value 127 or less. This means our map will
   only be half (128) of the maximum (256) size.
   Will this be an issue? *)
(* Define a "correct" bit array. *)
Definition bitarray_nstr mem bitmap_ptr str_ptr len : Prop :=
  forall i, i < 256 -> (0 < bit mem bitmap_ptr i <-> 
                       (exists j, j < len /\ nilfree mem str_ptr j /\ mem Ⓑ[str_ptr + j] = i)).

Definition bitarray_str mem bitmap_ptr str_ptr : Prop :=
  forall i, i < 256 -> (0 < bit mem bitmap_ptr i <-> 
                       (exists j, nilfree mem str_ptr j /\ mem Ⓑ[str_ptr + j] = i)).

Definition post_satis (i:N) (m:addr -> N) (str_ptr:addr) (accept_ptr:addr):= 
  (∃ k : N, nilfree m accept_ptr (k + 1)
    ∧ m Ⓑ[ accept_ptr + k ] = m Ⓑ[ str_ptr + i ]).

Lemma post_satis_incr :
  forall i char mem str_ptr accept_ptr bitmap_ptr, 
     post_satis i mem str_ptr accept_ptr 
     /\ bitarray_str mem bitmap_ptr str_ptr
     /\ mem Ⓑ[ 1 ⊕ i ⊕ str_ptr ] = char
     /\ bit mem bitmap_ptr char = 1
     -> post_satis (i+1) mem str_ptr accept_ptr.
Proof. Admitted.

Lemma post_satis_prev:
  forall i L m str_ptr accept_ptr, 
      i < L 
      /\ post_satis L m str_ptr accept_ptr 
      -> post_satis i m str_ptr accept_ptr.
Proof.
  intros.
  destruct H.
  inversion H0; destruct H1.
  unfold post_satis.
  (* This isn't exists x. *)
Abort.


Lemma mod_comm:
  forall x y, x ⊕ y = y ⊕ x.
Proof.
  intros. simpl. rewrite N.add_comm. reflexivity.
Qed.


Lemma nilfree_lt :
  forall mem accept_ptr j len, 
  nilfree mem accept_ptr j /\ mem Ⓑ[ len ⊕ accept_ptr ] = 0 
  -> j < len.
Proof.
Admitted.

Lemma bitarray_nstr_str :
  forall len mem accept_ptr bitmap_ptr,
     bitarray_nstr mem bitmap_ptr accept_ptr len
     /\ mem Ⓑ[ len ⊕ accept_ptr ] = 0
     -> bitarray_str mem bitmap_ptr accept_ptr.
Proof.
unfold bitarray_nstr.
unfold bitarray_str.
intros. destruct H.
split.
  intro. apply H in H2. destruct H2 as [j [LEN [NILFREE MEM]]]. exists j. split.
  assumption. assumption. assumption.
intros. destruct H2 as [j [NILFREE MEM]]. apply H. assumption. exists j. split.
  unfold nilfree in NILFREE.
  apply nilfree_lt with (mem:=mem) (accept_ptr:=accept_ptr). split; assumption.
  split; assumption.
Qed.



Definition strspn_invs (m:addr->N) (str_ptr accept_ptr sp:addr) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  (* 0x4130001c: Entry invariant *)
  |  0x4130001c => Some ( s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠaccept_ptr /\ s R_X3 = Ⓠsp)
  (* 0x41300054: Degenerative Loop (len(accept)==1) *)
  |  0x41300054 => Some( 
     exists invariant_loc, invariant_loc = "0x41300054"%string ->
     ∃ p L : N, s R_X0 = Ⓠp /\ s R_X1 = Ⓠ(p ⊕ L) /\
     ∀ i : N,  i < L → m Ⓑ[ accept_ptr ] = m Ⓑ[ str_ptr + i ])
  (* 0x41300030: Map Maker Loop *)
  |  0x41300030 =>  Some( 
     exists invariant_loc, invariant_loc = "0x41300030"%string ->
     ∃ bitmap_ptr L : N, s R_X1 = Ⓠ(accept_ptr ⊕ L) /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_nstr m bitmap_ptr accept_ptr L)
  (* 0x41300094: Map Maker->Checker Transition 
                 Just turn bitarray_nstr to bitarray_str to make
                 the map checker loop simpler. *)
  |  0x41300094 => Some(
     exists invariant_loc, invariant_loc = "0x41300094"%string ->
     ∃ bitmap_ptr p L, s R_X0 = Ⓠp /\ s R_X1 = Ⓠ(accept_ptr ⊕ L) /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m bitmap_ptr accept_ptr)
  (* 0x41300078: Map Checker Loop *)
  |  0x41300078 => Some( 
     exists invariant_loc, invariant_loc = "0x41300078"%string ->
     ∃ bitmap_ptr p L : N, s R_X0 = Ⓠp /\ s R_X1 = Ⓠ(p ⊕ L) /\
     s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m bitmap_ptr accept_ptr /\
     post_satis L m str_ptr accept_ptr)
  (* 0x41300068: Return Invariant *)
  |  0x41300068 => Some(
     exists invariant_loc, invariant_loc = "0x41300068"%string ->
     ∃ L : N,
     s R_X0 = ⓆL ∧ (∀ i : N, i < L → 
                    post_satis i m str_ptr accept_ptr 
                    ∧ ¬ post_satis L m str_ptr accept_ptr))
  | _ => None
  end | _ => None end.


Lemma byte0_bits0: 
  forall m bp i, i<8 /\ m Ⓑ[ bp ] = 0 -> bit m bp i = 0.
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
  forall len m a, getmem 64 LittleE len m a = 0 -> forall i, i < 2^(Mb*len) -> bit m a i = 0.
Proof.
  induction len using N.peano_ind; intros. simpl in H0. destruct i.
Abort.


Lemma val0_bits0_v2:
  forall  len m a, getmem 64 LittleE len m a = 0 /\ 0 < len
    ->  forall i, i < 2^(Mb*len) -> bit m a i = 0.
Proof.
  induction len using N.peano_ind; intros; destruct H. inversion H1.
  unfold bit. unfold xbits. 
Abort.


Lemma bitmap_0:
  forall m sp ap, m Ⓨ[ sp ] = 0 -> bitarray_nstr m sp ap 0.
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
  forall s str_ptr accept_ptr sp m t s' x'
         (* Enter right after "st1" instruction that prepares
            the bitmap. This skips 2 things worth mentioning:
              1) The stackpointer is subtracted 0x20 to make room
                 for the bitmap.
              2) the first character of 'accept_ptr' is loaded
                 into w2. *)
         (ENTRY: startof t (x',s') = (Addr 0x4130001c,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM32 = Ⓜm) 
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
  erewrite strspn_preserves_memory in MEM by eassumption.
  (* ASSUMPTION PRESERVATION
     Our capturing of str_ptr and accept_ptr means we rely on 
     s - the initial state.
     How do we update the hypotheses into s1?
     The assert+admits below are a placeholder. *)
  (*assert (STR': s1 R_X0 = Ⓠstr_ptr). { admit. }
  assert (ACPT' : s1 R_X1 = Ⓠaccept_ptr). { admit. }*)
  assert (SP' : s1 R_X3 = Ⓠsp). { admit. }
  assert (BITMAP': m Ⓨ[ sp ] = 0). { admit. }
  assert (CHAR0': Ⓠ (m Ⓑ[ accept_ptr ]) = s1 R_X2). { admit. }
  clear - PRE MDL MEM SP' BITMAP' CHAR0'. rename t1 into t. rename s1 into s.
  rename SP' into SP.
  rename BITMAP' into BITMAP. rename CHAR0' into CHAR0.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 64 PRE.
  destruct PRE as [STR [ACPT BMP]].
  Print step. Print arm8_step.
  step. step. step. 
  
  (* RET: Accept string empty *)
  step. exists "0x41300068"%string. intro LOC. 
  apply Neqb_ok in BC.
  exists 0. split. reflexivity.
  intros. apply N.nlt_0_r in H. contradiction.

  (* TODO: clean and rename m0 into m. *)
  step. step. step. 
  (* SINGLE CHARACTER: This is the first loop iteration. *)
  step. exists "0x41300054"%string. intro LOC.
    exists str_ptr. exists 0. split; try (assumption || reflexivity). split.
    psimpl; reflexivity. intros. apply N.nlt_0_r in H. contradiction.


  step.
  (* MAP BUILDER: This is the first loop iteration. *)
  apply N.eqb_neq in BC. apply N.eqb_neq in BC0.
  step. exists "0x41300030"%string. intro LOC.
  (* sp was stored in R_X3 *) 
  exists sp.
  (* First loop iteration, length should be 0 *)
  exists 0. psimpl. split; try reflexivity; split; try assumption.  unfold bitarray_nstr.
  apply bitmap_0. apply BITMAP.
  (* intros. split. intro.
  (* I think we need to prove that there is a contradiction because
     all the bits in the map are 0 - so no `i` can exist. This should
     be true because this is the first loop. *)
    admit.
  intros. destruct H0 as [x [H01 [H02 H03]]]. 
  apply N.nlt_0_r in H01. contradiction. *)
  destruct PRE as [loc [bitmap_ptr [L [H0 H1]]]].
  (* Our bookkeeping strategy introduces a new goal
     when destructing invariants:
    ------------------------------------(1/4)
     loc = "0x41300030"%string
  *)
  admit.

  (* Hmmmm.... Why is the BITMAP assumption not updated to reflect
     a change to it??? *)
  destruct H1 as [BITMAP_PTR BITMAP_2].

  (* MAP BUILDER->CHECKER TRANSITION: only executed once*)
  step. exists "0x41300094"%string. intros. exists sp. exists str_ptr. exists L.
  split. admit. split. assumption. split. assumption. apply bitarray_nstr_str with (len:=L).
  split. assert (BLA:sp=bitmap_ptr). { admit. }
 rewrite <-BLA in BITMAP_2. assumption. 
  (* TODO: Resume here showing that ... 
     We have a problem; `accept_ptr` is being used 2 ways:
        1) Describing the pointer to the current character
        2) Describing the original location (index 0)*) admit.

  step. step.  step. step.  step. step.
  step.
  (* MAP BUILDER: This is the arbitrary loop iteration. *)
  step. exists "0x41300030"%string. intro LOC.
  exists sp. exists (L+1). psimpl; split; try reflexivity. split; try reflexivity.
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