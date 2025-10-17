Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.
Require Import i386_wcsspn.
Import X86Notations.
Open Scope N.

(* The x86 lifter models non-writable code. *)
Theorem wcsspn_nwc: forall s2 s1, wcsspn_i386 s1 = wcsspn_i386 s2.
Proof. reflexivity. Qed.

(* Type safety:
   We first prove that the program is well-typed (automated by the Picinae_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem wcsspn_welltyped: welltyped_prog x86typctx wcsspn_i386.
Proof.
  Picinae_typecheck.
Qed.

(* Define function exit points *)
Definition wcsspn_exit (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 65 | 86 => true
  | _ => false
  end | _ => false end.


(* Correctness specification: *)

(* String p in memory state m contains wide-character c. *)
Definition contains m p c :=
  c <> 0 /\ ∃ n, (∀ i, i < n -> m Ⓓ[p + 4*i] <> 0) /\ m Ⓓ[p + 4*n] = c.

(* wcsspn returns a correct value iff all wide-characters in string p1 before returned index r
   are contained within string p2, and the character at r is not contained within p2. *)
Definition postcondition m p1 p2 r :=
  (∀ i, i < r -> contains m p2 (m Ⓓ[p1 + 4*i])) /\ ~contains m p2 (m Ⓓ[p1 + 4*r]).


(* Invariants (untrusted, machine-verified later): *)

Section Invariants.

  Variable s0 : store.          (* initial cpu state *)
  Definition mem := s0 V_MEM32. (* initial memory state *)
  Definition esp := s0 R_ESP.   (* initial stack pointer *)

  Definition p1 := mem Ⓓ[4+esp]. (* first stack argument *)
  Definition p2 := mem Ⓓ[8+esp]. (* second stack argument *)

  (* Define the memory state AFTER pushing the callee stack frame.  The post-
     condition of wcsspn is defined in terms of this memory state so that callers
     only get guarantees about string arguments that don't overlap the callee's
     local stack.  Parameter fbytes denotes the (arbitrary) bytes that the callee
     stores in the local frame, so that callers cannot assume their values. *)
  Definition mem' fbytes := mem [Ⓧ esp ⊖ 16 := fbytes ].

  (* outer loop invariant: *)
  Definition outer_inv s eax fb :=
    s V_MEM32 = mem' fb /\
    s R_EDI = p1 /\ s R_EBP = p2 /\ s R_ESI = mem' fb Ⓓ[p2] /\
    s R_EAX = eax /\
    s R_EBX = mem' fb Ⓓ[p1 + 4*eax] /\ mem' fb Ⓓ[p1 + 4*eax] <> 0 /\
    ∀ i, i < eax -> contains (mem' fb) p2 (mem' fb Ⓓ[p1 + 4*i]).

  (* full invariant set: *)
  Definition wcsspn_invs t :=
    match t with (Addr a,s)::_ => match a with

    (* function entry point *)
    | 0 => Some (s V_MEM32 = mem /\ s R_ESP = esp)

    (* start of outer loop *)
    | 32 => Some (∃ eax fb, outer_inv s eax fb)

    (* start of inner loop *)
    | 52 => Some (∃ eax edx fb,
        outer_inv s eax fb /\ s R_EDX = p2 ⊕ 4*edx /\
         ∀ i, i <= edx -> mem' fb Ⓓ[p2 + 4*i] <> mem' fb Ⓓ[p1 + 4*eax] /\ mem' fb Ⓓ[p2 + 4*i] <> 0
      )

    (* function exit points *)
    | 65 | 86 => Some (∃ eax fb, s V_MEM32 = mem' fb /\ s R_EAX = eax /\
                                 postcondition (mem' fb) p1 p2 eax)

    (* last half of outer loop (where several control-flows meet) *)
    | 72 => Some (∃ eax fb, outer_inv s eax fb /\ contains (mem' fb) p2 (mem' fb Ⓓ[p1 + 4*eax]))

    |_ => None
    end | _ => None end.

End Invariants.



(* Main correctness theorem & proof: *)

Theorem wcsspn_correctness:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr 0, s))
         (MDL: models x86typctx s),
  satisfies_all wcsspn_i386 (wcsspn_invs s) wcsspn_exit ((x',s')::t).
Proof.
    Local Ltac step := time x86_step.

    intros. eapply prove_invs.
    simpl. rewrite ENTRY. step. split; reflexivity.

    (* Optional: The following proof ignores all flag values except CF and ZF, so
      we can make evaluation faster and shorter by telling Picinae to ignore the
      other flags (i.e., abstract their values away). *)
    Ltac ignore_vars v ::= constr:(match v with
      R_AF | R_DF | R_OF | R_PF | R_SF => true
    | _ => false end).

    (* Address 0 *)
    intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply wcsspn_welltyped. intro MDL1.
    clear - PRE MDL1. rename t1 into t. rename s into s0. rename s1 into s.

    destruct_inv 32 PRE.

    (* Address 0 (function start) *)
    destruct PRE as [MEM ESP].
    step. step. step. step. step. step. step.
    generalize_frame (mem s0) as fb.
    step. step. step.

      (* Jump 18 -> 61 (wcs1 end reached) *)
      step. step. step. step.
      exists 0,fb. do 3 split.
        intros i H. contradict H. apply N.nlt_0_r.
        intro H. rewrite N.add_0_r in H. apply H. symmetry. apply N.eqb_eq, BC.

      (* Address 18 -> 20 fallthru (enter outer loop) *)
      step. step. step.
      exists 0,fb. repeat (split; psimpl; [reflexivity|]). split.
        apply not_eq_sym, N.eqb_neq, BC.
        intros. contradict H. apply N.nlt_0_r.

    (* Address 32 (start outer loop body) *)
    destruct PRE as [eax [fb [MEM [EDI [EBP [ESI [EAX [EBX [NZ PRE]]]]]]]]].
    step. step.

      (* Jump 34 -> 61 (wcs1 has zero length) *)
      step. step. step. step.
      exists eax,fb. split. reflexivity. split. assumption. split. assumption.
      apply N.eqb_eq in BC. symmetry in BC. intro H. destruct H as [NZ2 [k H]]. destruct k.
        apply NZ. rewrite <- (proj2 H), N.add_0_r. apply BC.
        apply (proj1 H 0). reflexivity. rewrite N.add_0_r. apply BC.

      (* Address 34 -> 36 fallthru *)
      step. step.

        (* Jump 38 -> 72 (wcs1[0] is in wcs2) *)
        exists eax,fb. split. repeat (split; psimpl; [assumption+reflexivity|]). apply PRE.
        split. assumption. exists 0. split.
          intros j H'. contradict H'. apply N.nlt_0_r.
          rewrite N.add_0_r. apply N.eqb_eq, BC0.

        (* Address 38 -> 40 fallthru (enter inner loop) *)
        step. step.
        exists eax,0,fb. split. repeat (split; psimpl; [assumption+reflexivity|]). apply PRE. split.
          psimpl. reflexivity.
          intros i H. apply N.le_0_r in H. subst i. psimpl. split.
            apply N.eqb_neq, BC0.
            apply not_eq_sym, N.eqb_neq, BC.

    (* Address 52 (start inner loop) *)
    destruct PRE as [eax [edx [fb [[MEM [EDI [EBP [ESI [EAX [EBX [NZ PRE]]]]]]] [EDX NU]]]]].
    step. step. step. step.

      (* Address 59 -> 61 fallthru (wcs2 end reached) *)
      step. step. step. step. apply N.eqb_eq in BC. symmetry in BC.
      exists eax,fb. split. reflexivity. split. assumption. split. assumption. intro H.
      destruct H as [H1 [i [H2 H3]]]. destruct (N.lt_trichotomy i (N.succ edx)) as [H|[H|H]].
        contradict H3. apply NU, N.lt_succ_r, H.
        contradict H1. subst i. rewrite <- H3, N.mul_succ_r. psimpl. apply BC.
        apply (H2 _ H). rewrite N.mul_succ_r. psimpl. apply BC.

      (* Jump 59 -> 48 (wcs2 not yet ended, so re-iterate inner loop) *)
      step. step.

        (* Jump 50 -> 72 (found wcs2 member in wcs1) *)
        exists eax,fb. split. repeat (split; psimpl; [assumption+reflexivity|]). apply PRE. split.
          apply N.eqb_eq in BC0. rewrite <- BC0. apply not_eq_sym, N.eqb_neq, BC.
          exists (N.succ edx). split.
            intros i H. apply NU, N.lt_succ_r, H.
            rewrite N.mul_succ_r. psimpl. apply N.eqb_eq, BC0.

        (* Address 50 -> 52 fallthru (found wcs2 non-member in wcs1) *)
        exists eax, (1+edx), fb. rewrite N.mul_add_distr_l. psimpl. split.
          repeat (split; [assumption+reflexivity|]). apply PRE. split. reflexivity.
          intros i H. apply N.le_lteq in H. destruct H.
            apply NU. apply N.lt_succ_r. rewrite <- N.add_1_l. assumption.
            subst i. rewrite N.mul_add_distr_l. psimpl. split.
              apply N.eqb_neq. assumption.
              apply not_eq_sym, N.eqb_neq. assumption.

    (* Address 72 (continue outer loop after wcs2 member found) *)
    destruct PRE as [eax [fb [[MEM [EDI [EBP [ESI [EAX [EBX [NZ PRE1]]]]]]] PRE2]]].
    step. step. step. step.

      (* Address 80 -> 82 fallthru (wcs1 end reached) *)
      step. step. step. step.
      exists (1 ⊕ eax), fb. split. reflexivity. split. reflexivity. split.
        intros i H. rewrite N.add_1_l in H. eapply N.lt_le_trans, N.lt_succ_r, N.le_lteq in H; [|apply mp2_mod_le]. destruct H.
          apply PRE1, H.
          subst i. assumption.
        psimpl. intro H.
          apply N.eqb_eq in BC. rewrite N.shiftl_mul_pow2, N.mul_comm in BC. psimpl in BC. rewrite <- BC in H.
          destruct H as [H1 H2]. apply H1. reflexivity.

      (* Jump 80 -> 32 (wcs1 not ended, so re-iterate outer loop) *)
      exists (1 ⊕ eax),fb. rewrite N.shiftl_mul_pow2, N.mul_comm in BC. apply N.eqb_neq, not_eq_sym in BC.
      rewrite N.shiftl_mul_pow2, N.mul_comm. repeat (split; psimpl; [assumption+reflexivity|]).
      rewrite N.add_1_l. intros i H. eapply N.lt_le_trans, N.lt_succ_r, N.le_lteq in H; [|apply mp2_mod_le]. destruct H.
        apply PRE1, H.
        subst i. apply PRE2.
Qed.
