Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import PArith.
Require Import Picinae_armv7.
Require Import strspn_arm.

Import ARMNotations.
Open Scope N.
Open Scope list_scope.
Import List.ListNotations.
Import List.

Definition fh := htotal.

Theorem strspn_nwc: forall s2 s1, strspn_arm s1 = strspn_arm s2.
Proof. reflexivity. Qed.

Theorem strspn_welltyped: welltyped_prog armtypctx strspn_arm.
Proof.
  Picinae_typecheck.
Qed.

Definition cstring m loc s :=
  m Ⓑ[loc ⊕ N.of_nat (length s)] = 0 /\
  ~In 0 s /\
  forall n, (n < length s)%nat -> m Ⓑ[loc ⊕ N.of_nat n] = nth n s 0.

Definition strspn_post strloc acceptloc accept m (_ : exit) s :=
  exists answer,
    (* s V_MEM32 = Ⓜm /\ *)
    (* s R_R0 = Ⓓstr /\ *)
    (* s R_R1 = Ⓓacceptloc /\ *)
    s R_R0 = Ⓓanswer /\
    cstring m acceptloc accept /\
    (forall n c, n < answer -> m Ⓑ[strloc+n] = c -> In c accept) /\
    (forall c, m Ⓑ[strloc + answer] = c -> ~(In c accept)).

Definition strspn_invs strloc acceptloc accept m a s :=
  (* let common n m := *)
  (*     s R_R0 = n /\ *)
  (*     s R_R1 = acceptloc /\ *)
  (*     s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\ *)
  (*     s R_R12 = Ⓓ(m Ⓑ[strloc+n]) /\ *)
  (*     s R_LR = Ⓓ(strloc+n) *)
  match a with
  | 16 =>
    Some (s R_R0 = Ⓓstrloc /\ s R_R1 = Ⓓacceptloc /\ s V_MEM32 = Ⓜm /\
          s R_R12 = Ⓓm Ⓑ[strloc])
  | 28 =>
    Some
      (exists strind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓacceptloc /\
          s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\
          s R_R12 = Ⓓ(m Ⓑ[strloc+strind]) /\
          s R_LR = Ⓓ(strloc+strind) /\
          cstring m acceptloc accept /\
          forall i, i < strind -> In (m Ⓑ[strloc+i]) accept)
  | 60 =>
    Some
      (exists strind acceptind,
          s R_R0 = Ⓓstrind /\
          s R_R1 = Ⓓacceptloc /\
          s R_R2 = Ⓓacceptind /\
          s R_R2 = Ⓓ(m Ⓑ[acceptloc+acceptind]) /\
          s R_R4 = Ⓓ(m Ⓑ[acceptloc]) /\
          s R_R12 = Ⓓ(m Ⓑ[strloc+strind]) /\
          s R_LR = Ⓓ(strloc+strind) /\
          cstring m acceptloc accept /\
          (forall i, i < strind -> In (m Ⓑ[strloc+i]) accept) /\
          (forall i, i < acceptind ->
                     m Ⓑ[strloc+strind] <> m Ⓑ[acceptloc+i]))
  | _ => None
  end.

Definition strspn_invset strloc acceptloc accept m :=
  invs (strspn_invs strloc acceptloc accept m)
       (strspn_post strloc acceptloc accept m).

Theorem strspn_partial_correctness_loop:
  forall s strloc acceptloc accept sp m n s' x
         (MDL0: models armtypctx s)
         (MEM0: s V_MEM32 = Ⓜm) (SP0: s R_SP = Ⓓsp)
         (ARGSTRING: s R_R0 = Ⓓstrloc) (ARGACCEPT: s R_R1 = Ⓓacceptloc)
         (INITCHAR: s R_R12 = Ⓓm Ⓑ[strloc])
         (ACCEPT: cstring m acceptloc accept)
         (RET: strspn_arm s (m Ⓓ[ sp ⊕ 4 ]) = None)
         (XP0: exec_prog fh strspn_arm 16 s n s' x),
    trueif_inv (strspn_invset strloc acceptloc accept m strspn_arm x s').
  intros.
  eapply prove_invs; [exact XP0|repeat split;assumption|].
  intros.
  assert (MDL: models armtypctx s1)
    by (eapply preservation_exec_prog; eauto; apply strspn_welltyped).
  assert (MEM: s1 V_MEM32 = Ⓜm) by shelve.
  assert (LR: s1 R_SP = Ⓓsp) by shelve.

  assert (WTM := arm_wtm MDL MEM).
  simpl in WTM.
  rewrite (strspn_nwc s1) in RET.
  apply (arm_regsize MDL0) in ARGSTRING.
  apply (arm_regsize MDL0) in ARGACCEPT.
  simpl in ARGSTRING,ARGACCEPT.

  destruct_inv 32 PRE.

  Local Ltac step := time arm_step.

  {
    repeat step.
    intuition.
    rewrite Hsv,Hsv0 in *.
    inversion H; subst.
    inversion H1; subst.
    rewrite H3.
    exists 0.
    rewrite N.add_0_r.
    intuition.
  }
  {
    repeat step.
    {
      unfold strspn_post.
      destruct PRE as [answer HPRE].
      intuition.
      rewrite Hsv in *.
      inversion H0; subst.
      exists answer.
      intuition; subst; intuition.
      unfold cstring in H4.
      apply Neqb_ok in BC.
      destruct getmem_little eqn:R in BC; [|discriminate].
      intuition.
      unfold cstring in ACCEPT.
      (* accept is empty *)
      admit.
    }
    all: admit.
  }
  {
    repeat step.
    all: admit.
  }
Abort.
