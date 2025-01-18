(* Proofs using Picinae for ARM8 Architecture

   Picinae System:
     Copyright (c) 2024 Kevin W. Hamlen
     Computer Science Department
     The University of Texas at Dallas

   These proofs written by:
     Ilan Buzzetti      (Ilan.Buzzetti@UTDallas.edu)
     Shreya Soman       (Shreya.Soman@UTDallas.edu)

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
Require Import arm8_strspn.
Require Import arm8_strspn_lemmas.
Require Import Lia.
Require Import Bool.

Require Import Picinae_numbers.
Import ARM8Notations.
Open Scope N.

(* Define post-condition points for strspn: *)
Definition strspn_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1048680 => true
  | _ => false
  end | _ => false end.

(* The ARM8 lifter creates non-writable code sections. *)
Theorem strspn_nwc: ∀ s2 s1, strspn2 s1 = strspn2 s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem strspn_welltyped: welltyped_prog arm8typctx strspn2.
Proof.
  Picinae_typecheck.
Qed.

(* Strspn does not modify page permissions. *)
Theorem strspn_preserves_readable:
  forall_endstates strspn2 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Strspn does not corrupt the LR register (call-return safety). *)
Theorem strspn_preserves_lr:
  forall_endstates strspn2 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* acpt string contains all characters of str's i-length prefix. *)
Definition post_satis_i (i:N) (m:memory) (str_ptr:addr) (acpt_ptr:addr):=
  ∀j, j < i ->
  (∃ k : N, nilfree m acpt_ptr (k + 1)
    ∧ m Ⓑ[ acpt_ptr ⊕ k ] = m Ⓑ[ str_ptr ⊕ j ]).

Ltac MS0 H:= 
  let a := fresh "memsame" in
  assert (a:=H 0 (N.lt_0_succ _)); psimpl in a.

(*Invariants*)
Section Invariants.

  Variable m : memory.
  Variable sp : addr.
  Variable str_ptr : addr.
  Variable acpt_ptr : addr.
  Variable acpt_len : N.

  Definition sp' := sp ⊖ 32.

  Definition strspn_invs (t:trace) := match t with (Addr a,s)::_ => match a with
  (* 0x00100000: Entry Invariant *)
  |  0x00100000 => Some ( s V_MEM64 = m 
                          /\ s R_SP = sp /\ m Ⓨ[ 0x00100000 + 0xb0 ] = 0
                          /\ s R_X0 = str_ptr /\ s R_X1 = acpt_ptr )

 (* 0x0010001c: Old Entry invariant *)
  |  0x0010001c => Some ( exists m', s V_MEM64 = m' 
                          /\ s R_SP = sp' /\ m' Ⓨ[ sp'] = 0 /\ s R_X0 = str_ptr 
                          /\ s R_X1 = acpt_ptr /\ s R_X2 = (m Ⓑ[ acpt_ptr ]) /\ s R_X3 = sp'
                          /\ mem_region_unchanged m m' acpt_ptr (N.succ acpt_len) 
                          /\ strlen m' acpt_ptr acpt_len )

  (* 0x00100054: Degenerative Loop (len(acpt)==1) *)
  |  0x00100054 => Some( exists m' (L:N), s V_MEM64 = m'  
                          /\ s R_X0 = str_ptr 
                          /\ s R_X2 = (m' Ⓑ[ acpt_ptr ]) /\ s R_X1 = (str_ptr ⊕ L)
                          /\ m' Ⓑ[ acpt_ptr ] ≠ 0 /\ m' Ⓑ[ 1 + acpt_ptr ] = 0 
                          /\ nilfree m' str_ptr L 
                          /\ ∀ i : N,  i < L → m' Ⓑ[ acpt_ptr ] = m' Ⓑ[ str_ptr + i ] )

  (* 0x0010002c: Map Maker Loop *)
  |  0x0010002c =>  Some(∃ m' bitmap_ptr L, 
                          s R_X3 = sp' /\ s R_X0 = str_ptr /\ s R_X1 = (acpt_ptr ⊕ L) 
                          /\ s R_X6 = 1 /\ s V_MEM64 = m'
                          /\ m' Ⓑ[ acpt_ptr ] ≠ 0 /\ m' Ⓑ[ 1 + acpt_ptr ] ≠ 0 
                          /\ strlen m' acpt_ptr acpt_len /\ L <= acpt_len 
                          /\ s R_X3 = bitmap_ptr ∧ bitarray_nstr m' bitmap_ptr acpt_ptr L 
                          /\ mem_region_unchanged m m' acpt_ptr (N.succ acpt_len))

  (* 0x00100094: Map Maker->Checker Transition
                 Just turn bitarray_nstr to bitarray_str to make
                 the map checker loop simpler. *)
  |  0x00100094 => Some(∃ m' bitmap_ptr L,
                         s R_X0 = str_ptr /\ s R_X1 = (acpt_ptr ⊕ L) 
                         /\ s V_MEM64 = m' /\ s R_X3 = bitmap_ptr 
                         /\ bitarray_str m' bitmap_ptr acpt_ptr 
                         /\ mem_region_unchanged m m' acpt_ptr (N.succ acpt_len))

  (* 0x00100078: Map Checker Loop *)
  |  0x00100078 => Some(∃ m' bitmap_ptr L,
                         s R_X0 = str_ptr /\ s R_X1 = (str_ptr ⊕ L) 
                         /\ s V_MEM64 = m' /\ s R_X3 = bitmap_ptr 
                         /\ bitarray_str m' bitmap_ptr acpt_ptr 
                         /\ post_satis_i L m' str_ptr acpt_ptr 
                         /\ nilfree m' str_ptr L 
                         /\ mem_region_unchanged m m' acpt_ptr (N.succ acpt_len))

  (* 0x00100068: Return Invariant *)
  |  0x00100068 => Some(∃ L m',
                         s V_MEM64 = m' 
                         /\ s R_X0 = L 
                         /\ post_satis_i L m' str_ptr acpt_ptr
                         /\ ¬ post_satis_i (L+1) m' str_ptr acpt_ptr)
  | _ => None
  end | _ => None end.
End Invariants.

(* * * * * * * * * *        ~~ Glossary ~~        * * * * * * * * * -)

  str_ptr : N
      pointer to the string whose prefix is checked
  acpt_ptr : N
      pointer to the string whose characters comprise an OK prefix
  acpt_len : N
      the length of the string starting at acpt_ptr
  s : store
      initial store
  sp : N
      stack pointer
  m : addr -> N
      memory at the start of execution
  t : trace
      execution trace that begins at the entry to the function and
      ends right before the one of the exit points registered in 
      strspn_exit is reach (only one exit point registered)
  s' : store
      the store when exit point x' is reached
  x' : exit
      the exit point that terminates trace t

( * * * * * * * * *         ~~ ~~~~~~~~ ~~        * * * * * * * * * *)
Theorem strspn_partial_correctness:
  ∀ s str_ptr acpt_ptr acpt_len sp m t s' x'
         (ENTRY: startof t (x',s') = (Addr 0x00100000,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = m)
         (STR: s R_X0 = str_ptr)
         (SP: s R_SP = sp)
         (ACPT:  s R_X1 = acpt_ptr)
         (ACPT_LEN: strlen m acpt_ptr acpt_len)
         (NO: ~overlap 64 acpt_ptr (N.succ acpt_len) (sp ⊖ 0x20) 32)
         (BITMAP: m Ⓨ[  0x00100000 + 0xb0  ] = 0)
,
  satisfies_all strspn2 (strspn_invs m sp str_ptr acpt_ptr acpt_len) strspn_exit ((x',s')::t).
Proof.
Local Ltac step := time arm8_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base Case *)
  simpl. rewrite ENTRY. step. repeat (split || assumption).

  (* Inductive Case *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strspn_welltyped).

  clear - PRE MDL NO ACPT_LEN. rename t1 into t. rename s1 into s.
  rename m into m0.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 64 PRE.
  destruct PRE as [MEM [SP [BITMAP_0 [STR ACPT]]]].

  step. step. step.

  step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                  Old ENTRY Invariant                        * * *)
  (* * *               0x00100024: cbz w2,0x001000a4                 * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  {
    eexists. unfold sp'.
    rewrite <-setmem_mod_l.
    repeat match goal with
    | [ |- mem_region_unchanged _ _ _ _] => idtac
    | [ |- strlen _ _ _] => idtac
    | _ => split; try (reflexivity || assumption)
    end.
    (* Proving that the reading of these 2 16-byte values from
      memory where all bytes are 0 is the same as reading a single 32-byte 0
    *)
    * psimpl. (* mic drop *)
      psimpl (_+_) in BITMAP_0. rewrite <- BITMAP_0. change 32 with (16+16). 
      rewrite getmem_split. (* mic drop x2 *)
      reflexivity.
      (* Fatality *)
    * psimpl. apply entry_memory_unchanged ; assumption.
    * eapply strlen_unchanged; [
        psimpl; apply entry_memory_unchanged; assumption
        | apply ACPT_LEN].
  }
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  
  clear ACPT_LEN.
  destruct PRE as [m [SMEM [SP [SP_1 [STR [ACPT [X2_EQ [X3_EQ [MEMSAME ACPT_LEN]]]]]]]]].
  step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                   Empty Accept String                       * * *)
  (* * *                     0x00100068: Ret                         * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
    apply Neqb_ok in BC.
    exists 0, m. repeat (split || reflexivity || assumption).
    unfold post_satis_i.
      intros j H1. apply N.nlt_0_r in H1. contradiction.
    apply empty_accept_exit with (m0:=m0) (acpt_len:=acpt_len); try assumption.
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

  apply N.eqb_neq in BC; pose proof BC as ACPT_0_NULL.
  step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                   Single Character                          * * *)
  (* * *                0x00100054: ldrb w3, [x1]                    * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Loop Iteration 0           * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    eexists. exists 0. apply Neqb_ok in BC0.
    MS0 MEMSAME.
    rewrite <-memsame.
    psimpl; repeat (split; try easy).
    apply nilfree0.
    intros. apply N.nlt_0_r in H. contradiction.
  (* * * * * * * * * * * * * * * * * * * * * * * *)


  3: {
  destruct PRE as  [m [L [MEM [STR_PTR [ACPT_CHAR_0 [X1_VALUE [ACPT_0_NNULL [ACPT_1_NULL [NF PREFIX]]]]]]]]].
  step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Loop Iteration N           * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  {
    apply Neqb_ok in BC.
    exists m, (L+1). psimpl.
    repeat (split; try easy).
      * apply nilfree_grow; try assumption. now rewrite <-BC in ACPT_0_NNULL.
      * intros. destruct (N.lt_trichotomy i L) as [LT | [EQ | GT]].
        apply PREFIX; easy.
        rewrite EQ; easy.
        lia.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  step. step.
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *        Single Character Ret         * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    psimpl. exists L, m. 
    repeat (split || easy).
    * enough (LSMALL: L mod 2 ^ 64 = L); try now rewrite LSMALL. apply N.mod_small.
      apply (nflen_lt m str_ptr L (1+acpt_ptr)); assumption.
    * apply single_char_ret; assumption.
    * apply single_char_ret_fail; assumption.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)


  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                       Map Maker                             * * *)
  (* * *                0x0010002c:  ldrb w2, [x1]                   * * *)
  (* * *                0x00100094:  mov  x1,  x0                    * * *)
  (* * *                0x00100078:  ldrb w4, [x1]                   * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

  step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Map Maker Loop 0           * * *)
  (* * *     0x0010002c:  ldrb w2, [x1]      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    apply N.eqb_neq in BC, BC0; unfold sp' in *.
    exists m, ( sp' sp). exists 0. psimpl.
    MS0 MEMSAME. rewrite memsame in *.
    repeat match goal with
    | [ |- strlen _ _ _] => idtac
    | [ |- bitarray_nstr _ _ _ _] => idtac
    | _ => split; try (easy || lia)
    end.
    apply bitmap_0_new with (acpt_len:=acpt_len); try assumption.
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  destruct PRE as [m' [bitmap_ptr [L [SP [STR_PTR [ACPT_L [X6_EQ_1
    [MEM' [ACPT_0_NNULL [ACPT_1_NNULL [STRLEN [L_LT_STRLEN [BITMAP_PTR [BITNSTR ACPT_SAME]]]]]]]]]]]]]].
  step. step. all: cycle 1.
  step. step. step. step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Map Maker Loop N           * * *)
  (* * *     0x0010002c:  ldrb w2, [x1]      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  {
    eexists. exists bitmap_ptr, (L+1).
    apply N.eqb_neq in BC.
    clear t t0.

    rewrite BITMAP_PTR in SP; inversion SP. pose proof NO as H'.
    eapply overlap_transform_rewrite with (sp:= sp) (m':= m') (L:= L) in H'; try easy.
    destruct H'. change (sp ⊖ 32) with (sp' sp) in *. unfold strlen in STRLEN. replace (N.succ acpt_len) with (acpt_len + 1) in H0 by lia.
    repeat (
      match goal with| [|- bitarray_nstr _ _ _ _] => idtac | _  =>  split; psimpl; try (easy )
      end
    ).
      * rewrite getmem_noverlap. assumption. specialize (H0 0). assert (0 < acpt_len + 1) by lia. apply H0 in H2. psimpl in H2. assumption.
      
      * rewrite getmem_noverlap. assumption. specialize (H0 1).
        assert (1 < acpt_len + 1). eapply accept_len_gte_2 with (m':=m') (acpt_ptr:=acpt_ptr) (L:=L). 
        all: try assumption. apply H0 in H2; psimpl in H2. assumption. 
      
      * apply nilfree_noverlap. psimpl in H1. assumption.
        destruct STRLEN as [T _]; assumption.
      
      * rewrite getmem_noverlap. destruct STRLEN as [NF NULL]. assumption. specialize (H0 acpt_len).
        assert (acpt_len < acpt_len + 1) by lia. apply H0 in H2. assumption.

      * eapply L_lte_acpt_len with (m':= m') (acpt_ptr:= acpt_ptr). all: assumption.

      * apply bitarray_nstr_str_final with (acpt_len:= acpt_len). all: try assumption. rewrite <- H. assumption.
        eapply noverlap_shrink with (a1:= acpt_ptr) (len1:= N.succ acpt_len). 
        assert(acpt_ptr mod 2 ^ 64 = acpt_ptr mod 2 ^ 64). lia. rewrite <- msub_move_0_r in H2. rewrite H2. lia. assumption.

      * unfold mem_region_unchanged in ACPT_SAME |- *. intros i Lti.
        rewrite getmem_noverlap. specialize (ACPT_SAME i (Lti)). assumption.  
        replace (N.succ acpt_len) with (acpt_len + 1) in Lti by lia. specialize (H0 i Lti). assumption.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  all: cycle -1.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *     Maker -> Checker Transition     * * *)
  (* * *      0x00100094:  mov  x1,  x0      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    eexists. exists bitmap_ptr, L.
    apply Neqb_ok in BC.
    do 4 (split; try easy). split; try easy.
    apply bitarray_nstr_str with (len:=L); assumption.
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  all: cycle 1.
  destruct PRE as [m' [bitmap_ptr [L [STR_PTR [ACPT_L [MEM' [BITMAP_PTR [BITARRAY ACPT_SAME]]]]]]]].
  step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *         Map Checker Loop 0          * * *)
  (* * *      0x00100078:  ldrb w4, [x1]     * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    exists m', bitmap_ptr, 0. psimpl.
    repeat (split; try easy).
    unfold post_satis_i. intros.
    apply N.nlt_0_r in H. contradiction.
    intros i Ilt0; now apply N.nlt_0_r in Ilt0.
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  destruct PRE as [m' [bitmap_ptr [L [STR_PTR [STR_L [MEM' [BITMAP_PTR [BITARRAY_STR [POST [NF ACPT_SAME]]]]]]]]]].
  step. step.

  all: cycle 1.
  step. step. step. step.
  all: cycle 1. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *         Map Checker Loop N          * * *)
  (* * *      0x00100078:  ldrb w4, [x1]     * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  {
    clear t t0.  
    eexists. exists bitmap_ptr, (L+1).
    apply N.eqb_neq in BC, BC0. rewrite (N.add_comm L 1).
    do 6 (split ; try (psimpl; easy)).
    * apply post_satis_incr' with (char:=m' Ⓑ[ str_ptr + L ]) (bitmap_ptr:=bitmap_ptr);
      try (assumption || reflexivity || now symmetry).
    * split; try apply nilfree_grow; assumption.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *        Ret: Checker Found \0        * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  {
    clear t t0.
    exists L, m'. 
    apply Neqb_ok in BC.
    repeat (split || reflexivity || assumption).
      eapply (prefix_no_wrap L); try eassumption.
      eapply (nil_terminator_postfix_fail L); try eassumption.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *   Ret: Checker Found Unlisted Char  * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  {
    clear t0 t.
    apply N.eqb_neq in BC. apply Neqb_ok in BC0.

    exists L, m'.
    repeat (split || reflexivity || assumption).
        eapply (prefix_no_wrap L); try eassumption.
        eapply (map_lookup_fail_postfix_fail L); try eassumption.
  }
  (* * * * * * * * * * * * * * * * * * * * * * * *)

Qed. 
