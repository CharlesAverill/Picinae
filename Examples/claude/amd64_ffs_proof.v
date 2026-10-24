(* ffs -- find first bit set in an int

   SEMANTICS
   ---------
   ffs returns the 1-based position of the least significant set bit of its
   32-bit argument, or 0 if no bit is set.  glibc uses BSF, which finds the
   0-based index of the lowest set bit.  When the argument is 0 it substitutes
   -1 (CMOVZ), and then it adds 1.

   Ghidra models BSF as a p-code loop inside the instruction.  pcode2coq lifts
   that loop to a bounded Picinae Rep (see find_scan_loop in pcode2coq_lib.py),
   which this proof analyzes with rep_move_iter and bsf_iter from
   amd64_common.v.  For a zero source, Ghidra's BSF writes 0 to the
   destination, whereas the hardware leaves it undefined.  CMOVZ overwrites
   the destination in that case, so the result does not depend on this
   difference.

   SPECIFICATION (man 3 ffs, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <strings.h>
            int ffs(int i);

     DESCRIPTION
            The ffs() function returns the position of the  first  (least  signifi-
            cant)  bit  set in the word i.  The least significant bit is position 1
            and the most significant position is, for example, 32 or 64.

     RETURN VALUE
            These functions return the position of the first bit set, or  0  if  no
            bits are set in i.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol ffs at 0x1a9910 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see ffs_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI (low 32 bits of RDI) holds i.  Let x = i as an unsigned 32-bit value.
   Output:  On return:
              if x = 0:  RAX = 0;
              if x <> 0: RAX = p with 1 <= p <= 32, bit p-1 of x is set, and
                         bits 0 .. p-2 of x are clear.
            RAX < 2^32, so EAX is the int result and the upper half is zero.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import ffs_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem ffs_nwc: forall s2 s1, ffs_amd64 s1 = ffs_amd64 s2.
Proof. reflexivity. Qed.

Theorem ffs_welltyped: welltyped_prog x64typctx ffs_amd64.
Proof. Picinae_typecheck. Qed.

Theorem ffs_preserves_memory:
  forall_endstates ffs_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ffs_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates ffs_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 18; BSF is at offset 9. *)
Definition ffs_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 18 => true
  | _ => false
  end | _ => false end.

Definition ffs_spec (x r:N) :=
  (x = 0 -> r = 0) /\
  (x <> 0 -> 1 <= r <= 32 /\ N.testbit x (r - 1) = true /\
             forall j, j < r - 1 -> N.testbit x j = false).

Definition postcondition (x rsp:N) (s:store) :=
  ffs_spec x (s R_RAX) /\ s R_RSP = rsp.

Definition ffs_invs (x rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI mod 2^32 = x /\ s R_RSP = rsp)
  | 9 => Some (s R_RDI mod 2^32 = x /\ s R_RSP = rsp /\ s R_RDX = 4294967295)
  | 18 => Some (postcondition x rsp s)
  | _ => None
  end | _ => None end.

(* One BSF loop iteration, as an eval_exp obligation for rep_move_iter. *)
Ltac bsf_ev X F :=
  let t' := fresh "t" in intro t'; eapply eval_exp_eq;
  [ eval_exp_build | idtac ];
  subst F; cbv beta;
  rewrite !update_updated, !update_frame by discriminate; simpl;
  change (N.pos (2^32)) with (2^32); change (N.pos (2^1)) with (2^1);
  unfold xbits; rewrite N.shiftr_0_r, N.sub_0_r, X, shiftr_land1;
  destruct (N.testbit _ t'); reflexivity.

Theorem ffs_correct:
  forall s t s' x' x rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (X: s R_RDI mod 2^32 = x) (RSP: s R_RSP = rsp),
  satisfies_all ffs_amd64 (ffs_invs x rsp) ffs_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ffs_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  - destruct PRE as [X RSP]. repeat x64_step. repeat split; assumption.

  - destruct PRE as [X [RSP RDX]].
    assert (XL: x < 2^32) by (rewrite <- X; apply mp2_mod_lt).
    set (F := fun t => if N.testbit x t then t else (t+1) mod 2^32).
    eapply NIStep; [reflexivity|reflexivity|].
    intros c s x0 XS.
    step_stmt XS. destruct XS as [XS _].
    rewrite N.shiftr_0_r, X in XS.
    destruct (N.eqb_spec x 0) as [X0|X0].
    + (* x = 0: no loop *)
      subst x. simpl in XS. step_stmt XS. destruct XS as [[RT ->] _].
      rewrite RT. simpl (9 + 3). rewrite exitof_none.
      repeat x64_step.
        split; [|assumption]. split; intro H. reflexivity. contradiction.
        exfalso. simpl in BC. discriminate.
    + (* x <> 0: the scan loop *)
      try rewrite (proj2 (N.eqb_neq _ _) X0) in XS. simpl in XS.
      apply exec_seq_none in XS.
      2: { intros c1 s0 x1 XR. eapply (rep_move_iter _ _ _ _ _ _ _ F) in XR.
           exact (proj1 XR). reflexivity. simpl; tauto. bsf_ev X F. }
      destruct XS as [c2 [s2 [XR XS]]].
      eapply (rep_move_iter _ _ _ _ _ _ _ F) in XR; [| reflexivity | simpl; tauto | bsf_ev X F].
      destruct XR as [_ [-> ->]].
      rewrite !update_frame, update_updated in XS by discriminate.
      destruct (bsf_iter 32 x ltac:(reflexivity) XL X0) as [KL [KB KJ]].
      fold F in KL, KB, KJ.
      change (N.succ 32) with 33 in KL, KB, KJ.
      remember (N.iter 33 F 0) as k eqn:K. clear K.
      step_stmt XS. destruct XS as [[RT ->] _].
      rewrite RT. simpl (9 + 3). rewrite exitof_none.
      repeat x64_step.
        exfalso. simpl in BC. discriminate.
        split; [|assumption]. split; intro H. contradiction.
        replace (1 + k - 1) with k by lia. split; [lia|]. split; assumption.
Qed.
