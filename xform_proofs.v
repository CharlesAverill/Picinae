(* Example proofs using Picinae for reasoning about x86 code transformations

   Copyright (c) 2022 Kevin W. Hamlen
   Computer Science Department
   The University of Texas at Dallas

   Any use, commercial or otherwise, requires the express permission of
   the author.

   To run this module, first load and compile:
   * Picinae_syntax
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_slogic
   * Picinae_i386
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_i386.

Import X86Notations.
Open Scope N.


(* We here prove correctness of register reallocation code transformations.  First, define
   how a register remapping function f is applied to transform code: *)

Fixpoint varmap_exp f e :=
  match e with
  | Var v => Var (f v)
  | Word _ _ | Unknown _ => e
  | Load e1 e2 en w => Load (varmap_exp f e1) (varmap_exp f e2) en w
  | Store e1 e2 e3 en w => Store (varmap_exp f e1) (varmap_exp f e2) (varmap_exp f e3) en w
  | BinOp b e1 e2 => BinOp b (varmap_exp f e1) (varmap_exp f e2)
  | UnOp u e1 => UnOp u (varmap_exp f e1)
  | Cast c w e1 => Cast c w (varmap_exp f e1)
  | Let v e1 e2 => Let (f v) (varmap_exp f e1) (varmap_exp f e2)
  | Ite e1 e2 e3 => Ite (varmap_exp f e1) (varmap_exp f e2) (varmap_exp f e3)
  | Extract n1 n2 e1 => Extract n1 n2 (varmap_exp f e1)
  | Concat e1 e2 => Concat (varmap_exp f e1) (varmap_exp f e2)
  end.

Fixpoint varmap_stmt f q :=
  match q with
  | Nop | Exn _ => q
  | Move v e => Move (f v) (varmap_exp f e)
  | Jmp e => Jmp (varmap_exp f e)
  | Seq q1 q2 => Seq (varmap_stmt f q1) (varmap_stmt f q2)
  | If e q1 q2 => If (varmap_exp f e) (varmap_stmt f q1) (varmap_stmt f q2)
  | Rep e q1 => Rep (varmap_exp f e) (varmap_stmt f q1)
  end.

Definition reg_realloc f (p:program) :=
  fun s a => match p s a with None => None
                            | Some (sz,q) => Some (sz, varmap_stmt f q) end.


(* The register remapping must be bijective.  To avoid axiom of choice, we define
   this in terms of invertibility (which implies injectivity) and surjectivity.
   It also must not remap pseudo-registers that have special meaning to the cpu,
   such as the page memory access bits. *)

Definition invertible {A B:Type} (f:A->B) := exists f', forall a, f' (f a) = a.

Definition surjective {A B:Type} (f:A->B) := forall b, exists a, f a = b.

Definition preserves_access f := f A_READ = A_READ /\ f A_WRITE = A_WRITE.

(* Invertibility implies injectivity. *)
Theorem injective {A B:Type}:
  forall (f:A->B), invertible f -> (forall a1 a2, f a1 = f a2 -> a1 = a2).
Proof.
  intros. destruct H as [f' H]. rewrite <- (H a1), <- (H a2), H0. reflexivity.
Qed.

Definition bijective {A B:Type} (f:A->B) := invertible f /\ surjective f.


(* The register reallocation transformation above is correct if it computes
   cpu states that are the composition of each original state s with register
   remapping function f. *)

Definition varmap_store f (s:store) : store := fun id => s (f id).

Theorem varmap_store_inv:
  forall f s (BI: bijective f), exists s', s = varmap_store f s'.
Proof.
  intros. destruct (proj1 BI) as [f' H].
  exists (fun id => s (f' id)). extensionality id.
  unfold varmap_store. rewrite H. reflexivity.
Qed.

Lemma varmap_update:
  forall f s v u (INJ: invertible f),
  varmap_store f (s[f v := u]) = (varmap_store f s)[v := u].
Proof.
  intros. extensionality v0. unfold varmap_store. destruct (vareq v0 v).
    subst v0. rewrite !update_updated. reflexivity.
    rewrite !update_frame. reflexivity. assumption. intro H. eapply n, injective.
      apply INJ.
      assumption.
Qed.

Lemma varmap_store_eq:
  forall f s1 s2 (SUR: surjective f),
  varmap_store f s1 = varmap_store f s2 -> s1=s2.
Proof.
  intros. extensionality v.
  destruct (SUR v) as [v0 H']. subst v.
  change (s1 (f v0)) with (varmap_store f s1 v0).
  rewrite H. reflexivity.
Qed.

Lemma reg_realloc_exp:
  forall f e h s u (INV: invertible f) (PA: preserves_access f) (E: eval_exp h (varmap_store f s) e u),
  eval_exp h s (varmap_exp f e) u.
Proof.
  intros. revert s u E. induction e; intros; inversion E; subst; simpl;
  try (econstructor; try match goal with
    [ IH: forall _ _, _ -> eval_exp ?h _ ?e _ |- eval_exp ?h _ ?e _ ] => eapply IH; eassumption
  end).

  unfold varmap_store. apply EVar.
  unfold mem_readable. rewrite <- (proj1 PA). assumption.
  unfold mem_writable. rewrite <- (proj2 PA). assumption.
  eapply IHe2; try eassumption. rewrite varmap_update. assumption. apply INV.
  assumption.
  destruct n1.
    eapply IHe3; eassumption.
    eapply IHe2; eassumption.
Qed.

Lemma reg_realloc_stmt:
  forall f h q s s' x (BI: bijective f) (PA: preserves_access f)
         (XS: exec_stmt h (varmap_store f s) q (varmap_store f s') x),
  exec_stmt h s (varmap_stmt f q) s' x.
Proof.
  intros. revert s s' x XS. induction q using stmt_ind2; intros; inversion XS; subst.
    apply varmap_store_eq in H. subst s'. apply XNop. apply BI.
    rewrite <- varmap_update in H by apply BI. apply varmap_store_eq in H.
      subst s'. apply XMove. apply reg_realloc_exp. apply BI. apply PA. assumption.
      apply BI.
    apply varmap_store_eq in H.
      subst s'. eapply XJmp. apply reg_realloc_exp. apply BI. apply PA. eassumption.
      apply BI.
    apply varmap_store_eq in H. subst s'. apply XExn. apply BI.
    apply XSeq1. fold varmap_stmt. eapply IHq1. assumption.
    destruct (varmap_store_inv f s2 BI) as [s2' H]. subst s2. eapply XSeq2; fold varmap_stmt.
      apply IHq1. exact XS1.
      apply IHq2. exact XS0.
    eapply XIf.
      apply reg_realloc_exp. apply BI. exact PA. exact E.
      fold varmap_stmt. destruct c; [ apply IHq2 | apply IHq1 ]; assumption.
    simpl. eapply XRep.
      apply reg_realloc_exp. apply BI. exact PA. exact E.
      replace (N.iter n _ Nop) with (varmap_stmt f (N.iter n (Seq q) Nop)).
        apply IHq2. exact XS0.
        clear w E XS0. induction n using N.peano_ind.
          reflexivity.
          rewrite !Niter_succ. simpl. rewrite IHn. reflexivity.
Qed.

Theorem register_reallocation_correct:
  forall f h p n a s s' x
         (BI: bijective f) (PA: preserves_access f)
         (NWC: forall s1 s2, p s1 = p s2)
         (XP: exec_prog h p a (varmap_store f s) n (varmap_store f s') x),
    exec_prog h (reg_realloc f p) a s n s' x.
Proof.
  intros. revert a s s' x XP. induction n; intros; inversion XP; subst.
    apply varmap_store_eq in H. subst s'. apply XDone. apply BI.
    destruct (varmap_store_inv f s2 BI) as [s2' H]. subst s2. eapply XStep.
      unfold reg_realloc. erewrite NWC. rewrite LU. reflexivity.
      apply reg_realloc_stmt. apply BI. apply PA. exact XS.
      exact EX.
      apply IHn. assumption.
    eapply XAbort.
      unfold reg_realloc. erewrite NWC. rewrite LU. reflexivity.
      apply reg_realloc_stmt. apply BI. apply PA. exact XS.
Qed.
