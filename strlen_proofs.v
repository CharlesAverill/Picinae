(* Example proofs using CoqBAP for Intel x86 Architecture
 *
 * Copyright (c) 2018 Kevin W. Hamlen
 * Computer Science Department
 * The University of Texas at Dallas
 *
 * Any use, commercial or otherwise, requires the express permission of
 * the author.
 *
 * To run this module, first load the BapSyntax, BapInterp, BapStatics,
 * Bap_i386, and strlen_i386 modules, and compile each (in that order)
 * using menu option Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Bap_i386.
Require Import strlen_i386.

Import BAPx86.
Import X86Notations.
Open Scope N.


(* Example #1: Type safety
   We first prove that the program is well-typed (automated by the BAP_typecheck tactic).
   This is useful for later inferring that all CPU registers and memory contents have
   values of appropriate bitwidth throughout the program's execution. *)
Theorem strlen_welltyped: welltyped_prog x86typctx strlen_i386.
Proof.
  BAP_typecheck.
Qed.

(* Example #2: Memory safety
   Strlen contains no memory-writes, and is therefore trivially memory-safe. *)
Theorem strlen_preserves_memory:
  forall RW s m n s' x,
  exec_prog RW strlen_i386 0 s m n s' x -> s' V_MEM32 = s V_MEM32.
Proof.
  intros. eapply prog_noassign_inv; [|exact H].
  intro a. destruct a as [|a]. discriminate 1.
  repeat first [ exact I | destruct a as [a|a|] | simpl; (repeat split); discriminate 1 ].
Qed.



(* Injections on certain data types occur frequently in proofs.  Some versions of Coq check
   injection-heavy proofs very slowly (at Qed).  This slow-down can be avoided by sequestering
   the most prevalent injections into lemmas, which we do here. *)
Lemma inj_prog_stmt: forall (sz1 sz2: N) (q1 q2: stmt),
                     Some (sz1,q1) = Some (sz2,q2) -> sz1=sz2 /\ q1=q2.
Proof. injection 1 as. split; assumption. Qed.

Lemma inj_exit: forall a1 a2, Exit a1 = Exit a2 -> a1 = a2.
Proof. intros. injection H. trivial. Qed.

Lemma inj_optval: forall (u1 u2:value), Some u1 = Some u2 -> u1=u2.
Proof. intros. injection H. trivial. Qed.

(* Create a case distinction between unfinished and not-unfinished program states.
   "Unfinished" programs are those whose starting states were not provided a sufficiently
   high recursion limit to fully evaluate one or more IL blocks.  A real CPU has no such
   recursion limit, so we don't usually care about such states.  Proof goals therefore
   tend to have the form "if not unfinished, then <some correctness property>". *)
Lemma fin_dec: forall x, {x = Some Unfinished} + {x <> Some Unfinished}.
Proof.
  intro. destruct x; [destruct e|]; first [ left;reflexivity | right;discriminate 1].
Qed.


(* Example #3: Architectural calling convention compliance
   Strlen does not write to callee-save registers (e.g., EBX)
   and it restores ESP on exit. *)

Theorem strlen_preserves_ebx:
  forall RW s m n s' x,
  exec_prog RW strlen_i386 0 s m n s' x -> s' R_EBX = s R_EBX.
Proof.
  intros. eapply prog_noassign_inv; [|exact H].
  intro a. destruct a as [|a]. discriminate 1.
  repeat first [ exact I | destruct a as [a|a|] | simpl; (repeat split); discriminate 1 ].
Qed.

Definition strlen_esp_inv (esp:N) (mem:addr->N) (x:exit) (s':store) :=
  match x with Exit a =>
    if N.eq_dec a (getmem LittleE 32 mem esp) then True
    else s' R_ESP = Some (VaN (esp,32))
  | _ => True
  end.

Lemma strlen_stmt_esp:
  forall y u s' mem x a' (PRE: y = Some (VaN (u,32))) (XS: s' R_ESP = y),
  strlen_esp_inv u mem (match x with Some e => e | None => Exit a' end) s'.
Proof.
  intros. rewrite <- XS in PRE. unfold strlen_esp_inv.
  destruct x; [ destruct e; try exact I | ].
  all: destruct (N.eq_dec _ _); first [ exact I | exact PRE ].
Qed.

Theorem strlen_preserves_esp:
  forall RW s esp mem m n s' x
         (ESP0: s R_ESP = Some (VaN (esp,32))) (MEM0: s V_MEM32 = Some (VaM mem 32))
         (RET: strlen_i386 (getmem LittleE 32 mem esp) = None)
         (XP: exec_prog RW strlen_i386 0 s m n s' x),
  strlen_esp_inv esp mem x s'.
Proof.
  intros.
  eapply prog_inv_reachable. exact XP.
  unfold strlen_esp_inv. destruct (N.eq_dec _ _). exact I. assumption.

  intros.
  unfold strlen_esp_inv in PRE. destruct (N.eq_dec a1 _) as [EQ|NE] in PRE.
    rewrite <- EQ, PA in RET. discriminate RET.
  apply strlen_preserves_memory in XP0. rewrite <- XP0 in MEM0.
  clear s n s' x ESP0 RET XP NE LE XP0.
  destruct a1 as [|a]; repeat first [ discriminate PA | destruct a as [a|a|] ].
  all: apply inj_prog_stmt in PA; destruct PA; subst sz q; simpl.

  all: try (
    apply (noassign_inv R_ESP) in XS;
    [ apply (strlen_stmt_esp (s1 R_ESP)); assumption
    | simpl; repeat split; discriminate 1 ]
  ).

  destruct (fin_dec x1) as [FIN|FIN]. subst x1. exact I.
  stock_store in XS. simpl_stmt in XS. destruct XS. subst x1.
  unfold strlen_esp_inv. destruct (N.eq_dec _ _).
    exact I.
    contradict n. reflexivity.
Qed.



(* Example #4: Partial correctness
   At termination, strlen returns (in EAX) a value k that satisfies the following:
   (1) p <= k,
   (2) no memory byte at addresses in the interval [p, p+k) is nil, and
   (3) the byte at address p+k is nil,
   where p is the address stored at [ESP+4] on entry. *)

Definition ones (b n:N) := N.iter n (fun x => x * 2^b + 1) 0.

Definition nilfree (m:addr->N) (p:addr) (k:N) :=
  p <= k /\ forall i, p <= i -> i < k -> m i > 0.

Definition strlen_regs_inv (m:addr->N) (a:addr) (s:store) (p eax:addr) :=
  match a with
  | 4 => nilfree m p eax
  | 9 => nilfree m p eax /\ s R_EDX = Some (VaN (3, 32))
  | 11 => nilfree m p eax /\ exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4 /\
                                         s R_ZF = Some (tobit (N.eqb edx 0))
  | 13 => nilfree m p eax /\ exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4
  | 15 | 24 | 33 => nilfree m p eax /\ exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4
  | 17 | 26 => nilfree m p eax /\ eax+1 < 2^32 /\
     (exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4) /\
     s R_ZF = Some (VaN (match m eax with N0 => 1 | _ => 0 end, 1))
  | 23 | 32 => nilfree m p (eax+1) /\ eax+1 < 2^32 /\
     exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4
  | 36 => nilfree m p eax /\ exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4 /\
                                       s R_ZF = Some (tobit (N.eqb edx 0))
  | 38 => nilfree m p eax /\ exists edx, s R_EDX = Some (VaN (edx, 32)) /\ edx < 4
  | 40 => nilfree m p eax /\ eax+1 < 2^32 /\
     s R_ZF = Some (VaN (match m eax with N0 => 1 | _ => 0 end, 1))
  | 46 => nilfree m p (eax+1) /\ eax+1 < 2^32
  | 47 => nilfree m p eax
  | 49 | 75 | 101 | 127 => nilfree m p eax /\ s R_EDX = Some (VaN (0, 32))
  | 51 | 77 | 103 | 129 => nilfree m p eax /\ eax+4 < 2^32 /\ s R_EDX = Some (VaN (0, 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m eax, 32))
  | 54 | 80 | 106 | 132 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN (0, 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-4), 32))
  | 56 | 82 | 108 | 134 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN ((2^32 - getmem LittleE 32 m (eax-4)) mod 2^32, 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-4), 32))
  | 62 | 88 | 114 | 140 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN ((2^32 - getmem LittleE 32 m (eax-4)) mod 2^32, 32)) /\
     s R_ECX = Some (towidth 32 (2^32 + getmem LittleE 32 m (eax-4) - ones 8 4)) /\
     s R_CF = Some (tobit (N.leb (ones 8 4) (getmem LittleE 32 m (eax-4))))
  | 63 | 89 | 115 | 141 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN (N.lnot (getmem LittleE 32 m (eax-4)) 32, 32)) /\
     s R_ECX = Some (towidth 32 (2^32 + getmem LittleE 32 m (eax-4) - ones 8 4)) /\
     s R_CF = Some (tobit (N.leb (ones 8 4) (getmem LittleE 32 m (eax-4))))
  | 65 | 91 | 117 | 143 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN (N.lnot (getmem LittleE 32 m (eax-4)) 32, 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-4) - ones 8 4, 32)) /\
     ones 8 4 <= getmem LittleE 32 m (eax-4)
  | 67 | 93 | 119 | 145 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_EDX = Some (VaN (N.lxor (N.lnot (getmem LittleE 32 m (eax-4)) 32)
                                 (getmem LittleE 32 m (eax-4) - ones 8 4), 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-4) - ones 8 4, 32)) /\
     ones 8 4 <= getmem LittleE 32 m (eax-4)
  | 73 | 99 | 125 | 151 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     let edx := N.land (N.lxor (N.lnot (getmem LittleE 32 m (eax-4)) 32)
                               (getmem LittleE 32 m (eax-4) - ones 8 4))
                         (ones 8 4 - 1) in
     s R_EDX = Some (VaN (edx, 32)) /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-4) - ones 8 4, 32)) /\
     s R_ZF = Some (tobit (N.eqb 0 edx)) /\
     ones 8 4 <= getmem LittleE 32 m (eax-4)
  | 153 => nilfree m p (eax-4) /\ 4 <= eax /\ eax < 2^32 /\
     s R_ECX = Some (towidth 32 (2^32 + getmem LittleE 32 m (eax-4) - ones 8 4)) /\
     exists i, p <= i < eax /\ m i = 0
  | 156 => nilfree m p eax /\ eax+3 < 2^32 /\
     s R_ECX = Some (towidth 32 (2^32 + getmem LittleE 32 m eax - ones 8 4)) /\
     exists i, p <= i <= eax+3 /\ m i = 0
  | 162 => nilfree m p eax /\ eax+3 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m eax, 32)) /\
     exists i, p <= i <= eax+3 /\ m i = 0
  | 165 => nilfree m p eax /\ eax+3 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m eax, 32)) /\
     s R_ZF = Some (VaN (match m eax with N0 => 1 | _ => 0 end, 1)) /\
     exists i, p <= i <= eax+3 /\ m i = 0
  | 167 => nilfree m p (eax+1) /\ eax+3 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m eax, 32)) /\
     exists i, p <= i <= eax+3 /\ m i = 0
  | 168 => nilfree m p eax /\ 1 <= eax /\ eax+2 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-1), 32)) /\
     exists i, p <= i <= eax+2 /\ m i = 0
  | 170 => nilfree m p eax /\ 1 <= eax /\ eax+2 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-1), 32)) /\
     s R_ZF = Some (VaN (match m eax with N0 => 1 | _ => 0 end, 1)) /\
     exists i, p <= i <= eax+2 /\ m i = 0
  | 172 => nilfree m p (eax+1) /\ 1 <= eax /\ eax+2 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 32 m (eax-1), 32)) /\
     exists i, p <= i <= eax+2 /\ m i = 0
  | 175 => nilfree m p (eax+1) /\ eax+2 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 16 m (eax+1), 32)) /\
     exists i, p <= i <= eax+2 /\ m i = 0
  | 176 => nilfree m p eax /\ eax+1 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 16 m eax, 32)) /\
     exists i, p <= i <= eax+1 /\ m i = 0
  | 179 => nilfree m p eax /\ eax+1 < 2^32 /\
     s R_ECX = Some (VaN (getmem LittleE 16 m eax, 32)) /\
     s R_ZF = Some (VaN (match m eax with N0 => 1 | _ => 0 end, 1)) /\
     exists i, p <= i <= eax+1 /\ m i = 0
  | 181 => nilfree m p (eax+1) /\ eax+1 < 2^32 /\ m (eax+1) = 0
  | 182 => nilfree m p eax /\ m eax = 0
  | 186 => nilfree m p (p+eax) /\ m (p+eax) = 0
  | _ => False
  end.

Definition strlen_postcond (mem:addr->N) (s:store) (esp:N) :=
  s R_ESP = Some (VaN (esp+4, 32)) /\
  let p := getmem LittleE 32 mem (esp+4) in
  exists eax, s R_EAX = Some (VaN (eax, 32)) /\
              mem (p + eax) = 0 /\
              forall i, i < eax -> mem (p+i) > 0.

Definition strlen_main_inv (esp:N) (mem:addr->N) (x:exit) (s:store) :=
  match x with
  | Exit a => if N.eq_dec a (getmem LittleE 32 mem esp) then strlen_postcond mem s esp else
     match a with 0 => True | N.pos _ =>
       exists eax, s R_EAX = Some (VaN (eax, 32)) /\
       strlen_regs_inv mem a s (getmem LittleE 32 mem (esp+4)) eax
     end
  | _ => True
  end.




Lemma shiftr_low_pow2: forall a n, a < 2^n -> N.shiftr a n = 0.
Proof.
  intros. destruct a. apply N.shiftr_0_l.
  apply N.shiftr_eq_0. apply N.log2_lt_pow2. reflexivity. assumption.
Qed.

Lemma lor_plus:
  forall a b (A0: N.land a b = 0), N.lor a b = a + b.
Proof.
  destruct a as [|a]; destruct b as [|b]; intros; try reflexivity.
  simpl in *. apply f_equal. revert b A0.
  induction a; destruct b; simpl; intros; try solve [ reflexivity | discriminate A0 ].
    destruct (Pos.land a b); discriminate A0.
    all: rewrite IHa; [ reflexivity | destruct (Pos.land a b); [ reflexivity | discriminate A0 ]].
Qed.

Lemma land_lohi_0:
  forall x y n, x < 2^n -> N.land x (N.shiftl y n) = 0.
Proof.
  intros. apply N.bits_inj_0. intro m. rewrite N.land_spec. destruct (N.lt_ge_cases m n).
    rewrite N.shiftl_spec_low. apply Bool.andb_false_r. assumption.
    erewrite bound_hibits_zero. reflexivity. exact H. assumption.
Qed.

Remark N_neq0_gt0: forall n, n<>0 <-> n>0.
Proof.
  split; intro.
    destruct n. contradict H. reflexivity. reflexivity.
    destruct n. discriminate H. discriminate 1.
Qed.

Remark le_div:
  forall a b c, a<=b -> a/c <= b/c.
Proof.
  intros.
  destruct c. destruct a; destruct b; reflexivity.
  intro H2. apply H, N.lt_gt. eapply N.lt_le_trans.
  rewrite (N.div_mod' b (N.pos p)) at 1.
  apply N.add_lt_mono_l. eapply (N.lt_lt_add_r _ _ (a mod N.pos p)). apply N.mod_lt. discriminate 1.
  rewrite N.add_assoc, <- N.mul_succ_r. rewrite (N.div_mod' a (N.pos p)) at 2.
  apply N.add_le_mono_r, N.mul_le_mono_l, N.le_succ_l, N.gt_lt, H2.
Qed.

(* User-level memory-reads that are successful must not have targeted the very top of
   the process address space, since those pages are reserved by the kernel. *)
Lemma read_bound_op:
  forall {RW mem mw a x s dstv op memv srcv en w e q m s'}
         (MEM: s memv = Some (VaM mem mw))
         (SRC: s srcv = Some (VaN (a,mw)))
         (HI: ~RW false mem mw (2^mw - 1))
         (ABND: a < 2^mw)
         (FIN: x <> Some Unfinished)
         (XS: exec_stmt RW s (Seq (Move dstv (BinOp op
                (Load (Var (Va memv (MemT mw))) (Cast CAST_UNSIGNED mw (Cast CAST_LOW mw (Var (Va srcv (NumT mw))))) en w)
                e)) q) m s' x),
  a + w/Mb < 2^mw.
Proof.
  intros.
  inversion XS; clear XS; subst. contradict FIN. reflexivity.
  inversion XS0; subst. contradict FIN. reflexivity.
  inversion XS1; clear XS0 XS1; subst. inversion E; clear E E2; subst.
  inversion E1; clear E1; subst.
  inversion E0; clear E0; subst. rewrite MEM in SV. injection SV as; subst.
  inversion E2; clear E2; subst. inversion E1; clear E1; subst.
  inversion E0; clear E0; subst. rewrite SRC in SV. injection SV as; subst.
  destruct (N.lt_ge_cases (n + w0/Mb) (2^w1)) as [?|H1]. assumption.
  exfalso. apply HI.
  rewrite N.mod_small in R by assumption.
  apply N.lt_le_pred in ABND. rewrite <- N.sub_1_r in ABND.
  rewrite <- (N.add_sub (2^w1 - 1) n). rewrite N.add_sub_swap by assumption. rewrite N.add_comm. apply R.
  apply (N.le_lt_add_lt n n). reflexivity.
  rewrite N.sub_add by assumption. rewrite N.add_comm. rewrite N.sub_1_r.
  eapply N.lt_le_trans. apply N.lt_pred_l. apply N.pow_nonzero. discriminate 1. assumption.
Qed.

Lemma read_bound_mov:
  forall {RW mem mw a x s dstv memv srcv en w m s'}
         (MEM: s memv = Some (VaM mem mw))
         (SRC: s srcv = Some (VaN (a,mw)))
         (HI: ~RW false mem mw (2^mw - 1))
         (ABND: a < 2^mw)
         (FIN: x <> Some Unfinished)
         (XS: exec_stmt RW s (Move dstv (Load (Var (Va memv (MemT mw))) (Var (Va srcv (NumT mw))) en w))
                        m s' x),
  a + w/Mb < 2^mw.
Proof.
  intros.
  inversion XS; clear XS; subst. contradict FIN. reflexivity.
  inversion E; clear E; subst.
  inversion E1; clear E1; subst. rewrite MEM in SV. injection SV as; subst.
  inversion E2; clear E2; subst. rewrite SRC in SV. injection SV as; subst.
  destruct (N.lt_ge_cases (a0 + w/Mb) (2^mw0)) as [?|H1]. assumption.
  exfalso. apply HI.
  apply N.lt_le_pred in ABND. rewrite <- N.sub_1_r in ABND.
  rewrite <- (N.add_sub (2^mw0 - 1) a0). rewrite N.add_sub_swap by assumption. rewrite N.add_comm. apply R.
  apply (N.le_lt_add_lt a0 a0). reflexivity.
  rewrite N.sub_add by assumption. rewrite N.add_comm. rewrite N.sub_1_r.
  eapply N.lt_le_trans. apply N.lt_pred_l. apply N.pow_nonzero. discriminate 1. assumption.
Qed.




Lemma unroll_Niter:
  forall {A:Type} f n (x:A), N.iter (N.succ n) f x = f (N.iter n f x).
Proof.
  intros. do 2 rewrite N2Nat.inj_iter. rewrite N2Nat.inj_succ. reflexivity.
Qed.

Lemma ones_succ:
  forall n w, ones n (N.succ w) = (ones n w) * 2^n + 1.
Proof.
  intros. unfold ones at 1. rewrite unroll_Niter. reflexivity.
Qed.

Lemma ones_succ_top:
  forall w n, ones w (N.succ n) = ones w n + 2^(w*n).
Proof.
  intros. induction n using N.peano_ind.
    rewrite N.mul_0_r. reflexivity.
    rewrite ones_succ, ones_succ, N.mul_succ_r, N.pow_add_r, <- N.add_assoc,
            (N.add_comm 1), N.add_assoc, <- N.mul_add_distr_r, <- IHn, ones_succ.
    reflexivity.
Qed.

Lemma ones_split:
  forall w i j, ones w (i+j) = (ones w i) + (ones w j) * 2^(w*i).
Proof.
  intros. revert i. induction j using N.peano_ind; intro.
    rewrite N.mul_0_l, N.add_0_r, N.add_0_r. reflexivity.
    rewrite ones_succ, <- N.add_succ_comm, N.mul_add_distr_r, <- N.mul_assoc,
            <- N.pow_add_r, (N.add_comm w), <- N.mul_succ_r, (N.add_comm _ (1*_)), N.add_assoc,
            N.mul_1_l, <- ones_succ_top.
    apply IHj.
Qed.

Lemma split_digit: forall m n p, 0 < m -> m*n <= p -> p - n = p - m*n + (m-1)*n.
Proof.
  intros. rewrite N.mul_sub_distr_r. rewrite N.add_sub_assoc.
    rewrite N.sub_add by assumption. rewrite N.mul_1_l. reflexivity.
    apply N.mul_le_mono_nonneg_r. apply N.le_0_l. apply N.lt_pred_le. assumption.
Qed.

Lemma ones_bound:
  forall p x, ones (N.pos p) x < 2^(N.pos p * x).
Proof.
  intros. rewrite <- (N2Nat.id x). generalize (N.to_nat x) as n. clear x. induction n.
    apply N_lt_0_pow2.
    rewrite Nat2N.inj_succ, ones_succ_top, N.mul_succ_r, N.pow_add_r. eapply N.lt_le_trans.
      eapply N.add_lt_le_mono. exact IHn. reflexivity.
      rewrite <- (N.mul_1_l (2^_)) at -3. rewrite <- N.mul_add_distr_r, N.mul_comm. apply N.mul_le_mono_nonneg_l.
        apply N.le_0_l.
        change (1+1) with (2^1). apply N.pow_le_mono_r. discriminate 1. destruct p; discriminate 1.
Qed.

Lemma bytes_pos_lobound:
  forall mem i a (WTM: welltyped_memory mem)
         (H: forall j, j < i -> mem (a + j) > 0),
  ones Mb i <= getmem LittleE (Mb*i) mem a.
Proof.
  intros mem i a WTM. revert a. induction i using N.peano_ind; intros.
    reflexivity.
    rewrite ones_succ, getmem_succ_r, lor_plus.
      rewrite N.add_comm. apply N.add_le_mono.
        apply N.lt_pred_le, N.gt_lt. rewrite <- (N.add_0_r a). apply H. apply N.lt_0_succ.
        rewrite N.shiftl_mul_pow2. apply N.mul_le_mono_nonneg_r.
          apply N.le_0_l.
          apply IHi. intros. rewrite N.add_succ_comm. apply H. apply -> N.succ_lt_mono. assumption.
      apply land_lohi_0, WTM.
Qed.

Lemma below_ones:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: getmem LittleE (Mb*w) mem a < ones Mb w),
  exists i, i < w /\ mem (a+i) = 0.
Proof.
  intros mem w a WTM. revert a. induction w using N.peano_ind; intros.
    contradict GM. apply N.nlt_0_r.
    rewrite ones_succ, getmem_succ_r in GM. destruct (mem a) eqn:M0.
      exists 0. split. apply N.lt_0_succ. rewrite N.add_0_r. exact M0.
      destruct (IHw (N.succ a)) as [i [LOI MI]].

        apply (N.mul_lt_mono_pos_r (2^Mb)). reflexivity.
        rewrite <- N.shiftl_mul_pow2.
        apply (N.le_lt_add_lt 1 (N.pos p)). destruct p; discriminate 1.
        rewrite N.add_comm, <- lor_plus. exact GM.
        apply N.bits_inj_0. intro n. rewrite N.land_spec. destruct (N.lt_ge_cases n Mb) as [LO|HI].
          rewrite N.shiftl_spec_low. apply Bool.andb_false_r. exact LO.
          rewrite bound_hibits_zero with (w:=Mb). reflexivity. rewrite <- M0. apply WTM. exact HI.

        exists (N.succ i). split.
          revert LOI. apply N.succ_lt_mono.
          rewrite <- N.add_succ_comm. exact MI.
Qed.

Lemma sub1parity:
  forall b x, x > 0 ->
  (x mod 2^b =? 0) = xorb (N.testbit x b) (N.testbit (x-1) b).
Proof.
  intros b x.
  do 2 rewrite N.testbit_odd, N.shiftr_div_pow2.
  rewrite (N.div_mod' x (2^b)) at -2.
  assert (XLO: x mod 2^b < 2^b). apply N.mod_lt, N.pow_nonzero. discriminate 1.
  destruct (x mod 2^b).

  rewrite N.add_0_r, N.mul_comm.
  intro H. apply N.gt_lt in H.
  rewrite N.div_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite <- (N.sub_add (2^b) (_*_)).
  rewrite <- N.add_sub_assoc by apply N.lt_pred_le, N_lt_0_pow2.
  rewrite <- (N.mul_1_l (2^b)) at 4. rewrite <- N.mul_sub_distr_r.
  rewrite N.div_add_l by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (_-_)) by (apply N.sub_lt; [ apply N.lt_pred_le, N_lt_0_pow2 | reflexivity ]).
  rewrite N.add_0_r.
  rewrite N.odd_sub by (eapply N.lt_pred_le, N.mul_lt_mono_pos_r; [ apply N_lt_0_pow2 | exact H ]).
  rewrite N.odd_1. destruct (N.odd (_/_)); reflexivity.

    rewrite <- (N.mul_1_l (2^b)) at 1. apply N.mul_le_mono_pos_r. apply N_lt_0_pow2.
    apply N.lt_pred_le, (N.mul_lt_mono_pos_r (2^b)). apply N_lt_0_pow2. exact H.

  intro.
  rewrite <- N.add_sub_assoc by (destruct p; discriminate 1).
  rewrite N.mul_comm. do 2 rewrite N.div_add_l by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (N.pos _)) by exact XLO.
  rewrite (N.div_small (_-_)) by (eapply N.le_lt_trans; [ apply N.le_sub_l | exact XLO ]).
  rewrite Bool.xorb_nilpotent. reflexivity.
Qed.

Lemma sub11parity:
  forall b x y, y*2^b < x ->
  (x mod 2^b =? 0) = xorb (N.odd y) (xorb (N.testbit x b) (N.testbit (x-(y*2^b + 1)) b)).
Proof.
  intros. rewrite N.sub_add_distr.
  rewrite <- (N.sub_add (y*2^b) x) at -3 by apply N.lt_le_incl, H.
  rewrite N.testbit_odd, N.shiftr_div_pow2.
  rewrite N.mod_add, N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.add_comm _ y), N.odd_add, Bool.xorb_assoc_reverse, <- N.shiftr_div_pow2, <- N.testbit_odd.
  rewrite <- sub1parity by apply N.lt_gt, N.lt_add_lt_sub_r, H.
  rewrite <- Bool.xorb_assoc_reverse, Bool.xorb_nilpotent.
  symmetry. apply Bool.xorb_false_l.
Qed.

Lemma sub_parity:
  forall b w x y z, y*2^b < x/2^w ->
                    z <= x mod 2^w ->
  (x/2^w mod 2^b =? 0) = xorb (N.odd y) (xorb (N.testbit x (b+w)) (N.testbit (x-(z + (y*2^b + 1)*2^w)) (b+w))).
Proof.
  intros.
  do 2 rewrite <- N.div_pow2_bits.
  rewrite (N.div_mod' x (2^w)) at 3.
  rewrite N.sub_add_distr.
  rewrite <- N.add_sub_assoc by assumption.
  rewrite N.mul_comm, N.add_comm.
  rewrite <- N.add_sub_assoc.
  rewrite <- N.mul_sub_distr_r.
  rewrite N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite (N.div_small (_-_)) by (eapply N.le_lt_trans; [apply N.le_sub_l | apply N.mod_lt, N.pow_nonzero; discriminate 1]).
  rewrite N.add_0_l.
  apply sub11parity. assumption.

  apply N.mul_le_mono_pos_r. apply N_lt_0_pow2.
  rewrite N.add_1_r. apply N.le_succ_l. assumption.
Qed.

Lemma extract_bit:
  forall b w xw x y z, y*2^b < x/2^w ->
                       z <= x mod 2^w ->
                       b+w < xw ->
                       N.odd y = true ->
  (x/2^w mod 2^b =? 0) =
  N.testbit (N.lxor (N.lnot x xw) (x - (z + (y*2^b + 1)*2^w))) (b+w).
Proof.
  intros.
  rewrite (sub_parity b w x y z); try assumption.
  rewrite N.lxor_spec, <- Bool.xorb_assoc.
  rewrite N.lnot_spec_low by assumption.
  rewrite H2. reflexivity.
Qed.

Lemma testbit_ones_true:
  forall w n b, b<>0 -> n < w -> N.testbit (ones b w) (b*n) = true.
Proof.
  intros w n b H0 H.

  destruct b as [|b']. contradict H0. reflexivity. clear H0.

  rewrite <- (N.sub_add n w) by apply N.lt_le_incl, H.
  destruct (w-n) eqn:H1. contradict H. apply N.nlt_ge, N.sub_0_le. assumption.
  rewrite <- (N.succ_pred (N.pos p)) by discriminate 1.
  rewrite N.add_comm, ones_split, ones_succ.
  rewrite <- lor_plus by (rewrite <- N.shiftl_mul_pow2; apply land_lohi_0, ones_bound).
  rewrite N.lor_spec.
  erewrite bound_hibits_zero; [| apply ones_bound | reflexivity].
  rewrite N.mul_pow2_bits_high by reflexivity.
  rewrite N.sub_diag.
  rewrite <- lor_plus by (rewrite N.land_comm, <- N.shiftl_mul_pow2; change 1 with (2^0); apply land_lohi_0, N.pow_lt_mono_r; reflexivity).
  rewrite N.lor_spec.
  rewrite N.mul_pow2_bits_low by reflexivity.
  reflexivity.
Qed.

Lemma testbit_onesm1_true:
  forall w n b, b<>0 -> n<>0 -> n<w -> N.testbit (ones b w - 1) (b*n) = true.
Proof.
  intros.
  destruct w. contradict H1. apply N.nlt_0_r.
  rewrite <- (N.succ_pred (N.pos p)) by discriminate 1.
  rewrite ones_succ, N.add_sub. rewrite <- (N.mul_1_r b) at 2.
  destruct n. contradict H0. reflexivity.
  rewrite N.mul_pow2_bits_high by (apply N.mul_le_mono_nonneg_l; [ apply N.le_0_l | destruct p0; discriminate 1]).
  rewrite <- N.mul_sub_distr_l, N.sub_1_r. apply testbit_ones_true. assumption.
  apply -> N.pred_lt_mono. assumption. discriminate 1.
Qed.

Theorem noborrow_nonil:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: ones Mb w <= getmem LittleE (Mb*w) mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE (Mb*w) mem a) (Mb*w))
                              (getmem LittleE (Mb*w) mem a - ones Mb w))
                      (ones Mb w - 1) = 0)
         i (IW: i < w),
  mem (a + i) > 0.
Proof.
  intros until i. intro IW.
  assert (JW:=N.le_refl w). revert JW i IW. generalize w at -2 as i. induction i using N.peano_ind; intros IW j JI.
  contradict JI. apply N.nlt_0_r.
  specialize (IHi (N.le_trans _ _ _ (N.le_succ_diag_r i) IW)).
  apply N.lt_succ_r, N.lt_eq_cases in JI. destruct JI as [JI|JI].
  apply (IHi _ JI). subst j.
  apply N.le_lteq in IW. destruct IW as [IW|IW].

  assert (H:=N.add_sub w i). rewrite N.add_comm in H. revert H.
  rewrite <- N.add_sub_assoc by (apply N.lt_le_incl, N.lt_succ_l; exact IW).
  generalize (w-i) as j. intros. subst w.
  destruct j as [|j]. contradict IW. rewrite N.add_0_r. apply N.nlt_succ_diag_l.
  rewrite <- (N.succ_pos_pred j) in *. destruct (Pos.pred_N j) as [|j'].
  contradict IW. rewrite N.add_1_r. apply N.lt_irrefl.
  clear j IW. rename j' into j.

  apply N_neq0_gt0, N.eqb_neq.
  rewrite ones_split in TST at 1. rewrite ones_succ in TST.
  apply (f_equal (fun x => N.testbit x (Mb + Mb*i))) in TST.
  rewrite N.bits_0, N.land_spec in TST.
  rewrite <- extract_bit in TST.
  rewrite <- TST.
  rewrite getmem_split, <- N.shiftr_div_pow2, N.shiftr_lor.
  rewrite N.shiftr_shiftl_l by reflexivity.
  rewrite N.sub_diag, N.shiftl_0_r, N.shiftr_div_pow2.
  rewrite N.div_small by apply getmem_bound, WTM.
  rewrite N.lor_0_l, getmem_succ_r, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.lor_0_r.
  rewrite N.mod_small by apply WTM.
  rewrite <- (N.mul_1_r Mb) at 2. rewrite <- N.mul_add_distr_l. rewrite testbit_onesm1_true.
    rewrite Bool.andb_true_r. reflexivity.
    discriminate 1.
    rewrite N.add_1_l. apply N.succ_0_discr.
    rewrite N.add_comm, <- (N.add_0_r (_+_)), <- N.add_1_l, N.add_assoc. apply N.add_lt_mono_l. reflexivity.

  rewrite ones_split, getmem_split in GM.
  rewrite lor_plus in GM by apply land_lohi_0, getmem_bound, WTM.
  rewrite N.shiftl_mul_pow2 in GM.
  apply (N.div_le_mono _ _ (2^(Mb*i))) in GM; [|apply N.pow_nonzero; discriminate 1].
  do 2 rewrite N.div_add in GM by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in GM by apply ones_bound.
  rewrite N.div_small in GM by apply getmem_bound, WTM.
  apply N.le_succ_l. rewrite <- N.add_1_r, <- ones_succ, getmem_split.
  rewrite lor_plus by apply land_lohi_0, getmem_bound, WTM.
  rewrite N.shiftl_mul_pow2.
  rewrite N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small by apply getmem_bound, WTM.
  exact GM.

  rewrite getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones, N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.mod_small by apply getmem_bound, WTM.
  rewrite N.lor_0_r. apply bytes_pos_lobound. exact WTM. exact IHi.

  rewrite N.add_comm, N.mul_add_distr_l. apply N.add_lt_mono_l.
  rewrite N.mul_succ_r. rewrite <- (N.add_0_l Mb) at 1. apply N.add_lt_mono_r.
  apply N.mul_pos_pos; reflexivity.

  rewrite <- N.bit0_odd, <- (N.mul_0_r Mb). apply testbit_ones_true.
    discriminate 1.
    reflexivity.

  subst w. clear TST IHi. revert a GM. induction i using N.peano_ind; intros.
    apply N.lt_gt. eapply N.lt_le_trans. apply N.lt_0_1. rewrite N.add_0_r. etransitivity.
      exact GM.
      rewrite getmem_succ_r, N.lor_0_r. reflexivity.

    rewrite <- N.add_succ_comm. apply IHi.
    rewrite getmem_succ_r, ones_succ in GM.
    apply (N.div_le_mono _ _ (2^Mb)) in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_add_l in GM; [|apply N.pow_nonzero; discriminate 1].
    rewrite N.div_small, N.add_0_r in GM; [|reflexivity].
    etransitivity. exact GM.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor, N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r, shiftr_low_pow2, N.lor_0_l.
      reflexivity. apply WTM. reflexivity.
Qed.

Lemma lsd_pos:
  forall b x, b<>0 -> x > 0 -> exists n, x/2^(b*n) mod 2^b > 0.
Proof.
  intros b x B0 X0. exists (N.log2 x / b).
  apply N.lt_gt. apply N.gt_lt in X0. destruct (N.log2_spec x X0) as [LO HI].
  rewrite N.mod_small.
    eapply N.lt_le_trans.
      apply N.lt_0_1.
      erewrite <- N.div_same.
        apply le_div. etransitivity.
          apply N.pow_le_mono_r. discriminate 1. apply N.mul_div_le; assumption.
          assumption.
        apply N.pow_nonzero. discriminate 1.
    eapply N.mul_lt_mono_pos_l. apply N_lt_0_pow2. eapply N.le_lt_trans.
      apply N.mul_div_le, N.pow_nonzero. discriminate 1.
      rewrite <- N.pow_add_r, <- N.mul_succ_r. eapply N.lt_le_trans.
        exact HI.
        apply N.pow_le_mono_r. discriminate 1. apply N.le_succ_l, N.mul_succ_div_gt. exact B0.
Qed.

Theorem borrow_nil:
  forall mem w a (WTM: welltyped_memory mem)
         (GM: ones Mb w <= getmem LittleE (Mb*w) mem a)
         (TST: N.land (N.lxor (N.lnot (getmem LittleE (Mb*w) mem a) (Mb*w))
                              (getmem LittleE (Mb*w) mem a - ones Mb w))
                      (ones Mb w - 1) > 0),
  exists i, i < w /\ mem (a + i) = 0.
Proof.
  intros.
  destruct w as [|w]. contradict TST. rewrite N.land_0_r. discriminate 1.
  rewrite <- (N.succ_pos_pred w) in *.
  apply (lsd_pos Mb) in TST; [|discriminate 1]. destruct TST as [j TST].

  rewrite <- N.shiftr_div_pow2, N.shiftr_land, <- N.land_ones, <- N.land_assoc in TST.

  destruct j as [|j].
  rewrite N.mul_0_r, (N.shiftr_0_r (_-_)), ones_succ, N.add_sub, <- N.shiftl_mul_pow2, (N.land_comm _ (N.ones _)) in TST.
  rewrite land_lohi_0 in TST by reflexivity.
  rewrite N.land_0_r in TST. discriminate TST.

  rewrite ones_succ in TST at 2.
  rewrite N.add_sub, <- N.shiftl_mul_pow2 in TST.
  rewrite N.shiftr_shiftl_r in TST by (rewrite <- (N.mul_1_r Mb) at 1; apply N.mul_le_mono_l; destruct j; discriminate 1).
  rewrite <- N.mul_pred_r in TST.
  destruct (N.le_gt_cases (N.pos j) (Pos.pred_N w)) as [JW|JW]; [|
    rewrite (shiftr_low_pow2 (ones _ _)) in TST by (eapply N.lt_le_trans; [ apply ones_bound | apply N.pow_le_mono_r ; [ discriminate 1 | apply N.mul_le_mono_l, N.lt_le_pred, JW] ]);
    rewrite N.land_0_l, N.land_0_r in TST; discriminate TST ].
  rewrite <- (N.sub_add (N.pos j) (Pos.pred_N w)) in TST at 5 by exact JW.
  rewrite N.add_comm, ones_split, (N.shiftr_div_pow2 (_+_)) in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 2 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb), N.pow_add_r, N.mul_assoc in TST.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite (ones_succ_top _ (N.pred _)) in TST.
  rewrite <- (N.mul_1_l (2^(_*N.pred _))) in TST at 1.
  rewrite N.div_add in TST by (apply N.pow_nonzero; discriminate 1).
  rewrite N.div_small in TST by apply ones_bound.
  rewrite N.land_ones in TST.
  rewrite N.mod_add in TST by (apply N.pow_nonzero; discriminate 1).
  change (_ mod _) with (N.ones 1) in TST.
  rewrite N.land_ones, <- (N.div_1_r (N.shiftr _ _)) in TST.
  change 1 with (2^0) in TST at 1.
  rewrite <- N.testbit_spec', N.shiftr_spec', N.add_0_l in TST.
  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST at 4 by (
    etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
  rewrite N.add_comm, ones_split in TST.
  rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
  rewrite ones_succ in TST.
  rewrite <- (N.succ_pred (N.pos j)) in TST at 4 by discriminate 1.
  rewrite (N.mul_succ_r _ (N.pred _)), (N.add_comm _ Mb) in TST.

  destruct (N.le_gt_cases (ones Mb (N.pred (N.pos j))) (getmem LittleE (Mb * N.pred (N.pos j)) mem a)) as [LOJ|LOJ].

  rewrite <- extract_bit in TST.

  exists (N.pred (N.pos j)). split.

    apply N.lt_succ_r, N.le_le_pred. exact JW.

    rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) in TST by (
      etransitivity; [ apply N.le_pred_l | etransitivity; [ exact JW | apply N.le_succ_diag_r ] ]).
    rewrite N.add_comm in TST.
    rewrite getmem_split in TST.
    rewrite <- N.shiftr_div_pow2, N.shiftr_lor in TST.
    rewrite shiftr_low_pow2 in TST by apply getmem_bound, WTM.
    rewrite N.shiftr_shiftl_l in TST by reflexivity.
    rewrite N.lor_0_l, N.sub_diag, N.shiftl_0_r in TST.
    rewrite N.sub_succ_l in TST by (etransitivity; [ apply N.le_pred_l | exact JW ]).
    rewrite getmem_succ_r in TST.
    rewrite lor_plus in TST by apply land_lohi_0, WTM.
    rewrite N.shiftl_mul_pow2 in TST.
    rewrite N.mod_add in TST by (apply N.pow_nonzero; discriminate 1).
    rewrite N.mod_small in TST by apply WTM.
    destruct (mem _). reflexivity. discriminate TST.

  apply N.le_succ_l. rewrite <- N.add_1_r, <- ones_succ.
  rewrite <- N.sub_succ_l by apply N.le_le_pred, JW.
  rewrite <- (N.add_0_l (ones _ _)).
  rewrite <- (N.div_small (ones Mb (N.pred (N.pos j))) (2^(Mb * N.pred (N.pos j)))) by apply ones_bound.
  rewrite <- N.div_add by (apply N.pow_nonzero; discriminate 1).
  rewrite <- ones_split.
  rewrite N.add_sub_assoc by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, N.add_sub.
  apply le_div. exact GM.

  rewrite <- (N.sub_add (N.pred (N.pos j)) (N.succ (Pos.pred_N w))) by apply N.le_le_pred, N.le_le_succ_r, JW.
  rewrite N.add_comm, getmem_split, <- N.land_ones, N.land_lor_distr_l, N.land_ones.
  rewrite N.mod_small by apply getmem_bound, WTM.
  rewrite N.land_ones, N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate 1).
  rewrite N.lor_0_r. exact LOJ.

  rewrite N.mul_succ_r, N.add_comm.
  apply N.add_lt_mono_r, N.mul_lt_mono_pos_l. reflexivity.
  eapply N.lt_le_trans. apply N.lt_pred_l. discriminate 1. exact JW.

  rewrite <- (N.succ_pred (_-_)), ones_succ.
  change (2^Mb) with (2*2^N.pred Mb).
  rewrite N.mul_comm, <- N.mul_assoc, N.add_comm. apply N.odd_add_mul_2.
  intro H. apply JW, N.lt_gt. eapply N.le_lt_trans. apply N.sub_0_le. exact H. apply N.lt_pred_l. discriminate 1.

  destruct (below_ones _ _ _ WTM LOJ) as [k [KW MK]].
  exists k. split.
    eapply N.lt_le_trans.
      exact KW.
      apply N.le_le_pred, N.le_le_succ_r, JW.
    exact MK.
Qed.


(* Tactic: destN n until T hyp:H
   Keep destructing n:N until either n is a completed numeric constant (provided as an
   equality in hypothesis H) or tactic T solves the goal.  This yields a set of subgoals
   in which n equals the various constants admitted by T.  Typical usage:
     destN a until (discriminate PA) hyp:ADDR.
   where PA is an instruction fetch of the form (PA: program a = Some _). *)
Tactic Notation "destN" constr(n) "until" tactic(T) "hyp:" ident(H) :=
  let p := fresh n in
  destruct n as [|p] eqn:H;
  [ try solve [T]
  | repeat first [ solve[T] | destruct p as [p|p|] ] ].

(* Tactic: focus_addr H n
   Shelve all goals except the goal in which hypothesis H has the form (H: _ = n).
   This retrieves the subgoal for address n from a sea of arbitrarily ordered goals.
   Use vernacular command "Unshelve" to pull back all the shelved goals afterward. *)
Tactic Notation "focus_addr" hyp(H) constr(n) :=
  match type of H with _ = n => idtac | _ => shelve end.

Theorem strlen_partial_correctness:
  forall RW s esp mem m n s' x
         (HI: ~ RW false mem 32 (2^32 - 1)%N)
         (MDL0: models x86typctx s)
         (ESPLO: esp + 8 <= 2^32)
         (ESP0: s R_ESP = Some (VaN (esp,32))) (MEM0: s V_MEM32 = Some (VaM mem 32))
         (RET: strlen_i386 (getmem LittleE 32 mem esp) = None)
         (XP0: exec_prog RW strlen_i386 0 s m n s' x),
  strlen_main_inv esp mem x s'.
Proof.
  intros. eapply prog_inv_reachable. exact XP0.
  unfold strlen_main_inv. destruct (getmem _ _ _ _). discriminate RET. exact I.
  intros. destruct (match x1 with Some x0 => x0 | None => _ end) eqn:EX; try exact I.
  assert (MEM: s1 V_MEM32 = Some (VaM mem 32)).
    rewrite <- MEM0. eapply strlen_preserves_memory. exact XP.
  assert (ESP: strlen_esp_inv esp mem (Exit a1) s1).
    eapply strlen_preserves_esp. exact ESP0. exact MEM0. exact RET. exact XP.
  assert (MDL: models x86typctx s1).
    eapply preservation_exec_prog. exact MDL0. apply strlen_welltyped. exact XP.
  destruct (fin_dec x1) as [FIN|FIN]. subst x1. discriminate EX.
  unfold strlen_esp_inv in ESP. unfold strlen_main_inv in PRE. destruct (N.eq_dec a1 _) as [EQ|NE].
    rewrite <- EQ, PA in RET. discriminate RET.
  clear s n s' x MDL0 MEM0 ESP0 XP NE LE XP0.

  destN a1 until (discriminate PA) hyp:ADDR.

  all: apply inj_prog_stmt in PA; destruct PA; subst sz q; simpl in EX.

  all: focus_addr ADDR 0 (* movl 0x4(%esp), %eax *).
  bsimpl in XS. destruct XS; subst s1' x1. apply inj_exit in EX. subst a.
  unfold strlen_main_inv. destruct (N.eq_dec _ _). rewrite <- e in RET. discriminate RET.
  simpl_stores. eexists. split. reflexivity. split.
    rewrite N.mod_small. reflexivity. eapply N.lt_le_trans; [|exact ESPLO]. apply N.add_le_lt_mono; reflexivity.
    intro. rewrite N.mod_small.
      intros IBOT ITOP. exfalso. eapply N.lt_irrefl. eapply N.le_lt_trans. exact IBOT. exact ITOP.
      eapply N.lt_le_trans; [|exact ESPLO]. apply N.add_le_lt_mono; reflexivity.

  Unshelve.
  all: destruct PRE as [eax [EAX PRE]]; unfold strlen_regs_inv in PRE.

  Local Ltac namepre H :=
    match type of H with
    | nilfree _ _ _ => let NF:=fresh "NF" in rename H into NF
    | _ R_EDX = _ => let EDX:=fresh "EDX" in rename H into EDX
    | _ R_ECX = _ => let ECX:=fresh "ECX" in rename H into ECX
    | _ R_CF = _ => let ECX:=fresh "CF" in rename H into ECX
    | _ R_ZF = _ => let ECX:=fresh "ZF" in rename H into ECX
    | _ => idtac
    end.
  Local Ltac destpre H :=
    match type of H with
    | _ /\ _ => let H1:=fresh "PRE" in let H2:=fresh "PRE" in destruct H as [H1 H2]; destpre H1; destpre H2
    | exists V, _ => let X:=fresh V in let H2:=fresh "PRE" in destruct H as [X H2]; destpre H2
    | _ => namepre H
    end.
  all: destpre PRE.

  all: match type of ADDR with _=15 => idtac | _=24 => idtac | _=38 => idtac | _ => shelve end.
  (* 15,24,38: cmpb %dh, (%eax) *)
  all: assert (LM: eax + 1 < 2^32) by (
    change 1 with (8/Mb); refine (read_bound_op MEM EAX HI _ FIN XS);
    destruct (MDL R_EAX (NumT 32) (eq_refl _)) as [u [EAX2 BND]];
    rewrite EAX2 in EAX; apply inj_optval in EAX; subst u;
    inversion BND; assumption).
  Unshelve.

  all: match type of ADDR with _=49 => idtac | _=75 => idtac | _=101 => idtac | _=127 => idtac | _ => shelve end.
  all: assert (LM: eax + 4 < 2 ^ 32) by (
    change 4 with (32/Mb); refine (read_bound_mov MEM EAX HI _ FIN XS);
    destruct (MDL R_EAX (NumT 32) (eq_refl _)) as [u [EAX2 BND]];
    rewrite EAX2 in EAX; apply inj_optval in EAX; subst u;
    inversion BND; assumption).
  Unshelve.

  Ltac reduce_main_inv XS EX RET :=
    match type of XS with ?S1' = _ /\ ?X1 = _ =>
      destruct XS; subst S1' X1; apply inj_exit in EX; rewrite <- EX in *; unfold strlen_main_inv;
      let e:=fresh "e" in let n:=fresh "n" in destruct (N.eq_dec _ _) as [e|n];
      [ rewrite <- e in RET; discriminate RET
      | clear n; unfold strlen_regs_inv; simpl_stores;
        eexists; try (split; [ solve [ reflexivity | eassumption ] | ]) ]
    end.

  all: bsimpl in XS; try reduce_main_inv XS EX RET.
  (* all: stock_store in XS; try (simpl_stmt in XS; reduce_main_inv XS EX RET). *)

  all: focus_addr ADDR 4 (* movl $0x3, %edx *).
  split. assumption. reflexivity.

  Unshelve. all: focus_addr ADDR 9 (* andl %eax, %edx *).
  split. assumption. eexists. split. reflexivity. change (3 mod 2^32) with (N.ones 2). split.
    rewrite N.land_comm, N.land_ones. apply N.mod_lt. discriminate 1.
    rewrite N.eqb_sym, <- N.land_ones, N.land_comm, N.land_assoc. reflexivity.

  Unshelve. all: focus_addr ADDR 11 (* je 49 *).
  destruct (edx =? 0) eqn:EDX0; bsimpl in XS; reduce_main_inv XS EX RET;
  (split; try assumption).
    apply Neqb_ok in EDX0. rewrite EDX,EDX0. reflexivity.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 13 (* jp 38 *).
  match type of XS with (exec_stmt _ _ match ?E with _ => _ end _ _ _) => destruct E end.
  destruct n; bsimpl in XS; reduce_main_inv XS EX RET;
  (split; [ assumption | eexists; split; [exact EDX | assumption] ]).

  Unshelve. all: focus_addr ADDR 15 (* cmpb %dh, (%eax) *).
  repeat (split; try assumption).
    eexists. split. reflexivity. assumption.

    rewrite (N.mod_small edx), (N.mod_small edx) by (transitivity 4; [assumption|reflexivity]).
    rewrite N.shiftr_eq_0, N.sub_0_r, N.add_comm.
    change (2^8) with (1*2^8) at 1. rewrite N.mod_add by discriminate 1.
    rewrite N.mod_small by apply getmem_bound, (x86_wtm MDL MEM).
    rewrite getmem_Mb, N.mod_small. destruct (mem _); reflexivity.
    eapply N.le_lt_trans. eapply N.le_add_r. exact LM.
    destruct edx. reflexivity. apply N.log2_lt_pow2. reflexivity. transitivity 4. assumption. reflexivity.

  Unshelve. all: focus_addr ADDR 17 (* je 182 *).
  destruct (mem eax) eqn:BYT; bsimpl in XS; reduce_main_inv XS EX RET;
      (repeat first [ assumption | split ]).
    etransitivity. apply (proj1 NF). apply N.le_add_r.
    intros i H1 H2. rewrite N.add_1_r in H2. apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2.
      apply NF; assumption.
      subst i. rewrite BYT. reflexivity.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 23 (* incl %eax *).
  split.
    rewrite (N.mod_small eax).
      rewrite N.mod_small by assumption. exact NF.
      eapply N.le_lt_trans. eapply N.le_add_r. eassumption.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 24 (* cmpb %dh, (%eax) *).
  repeat first [ assumption | split ].
    eexists. split. reflexivity. assumption.

    rewrite (N.mod_small edx), (N.mod_small edx) by (transitivity 4; [assumption|reflexivity]).
    rewrite N.shiftr_eq_0, N.sub_0_r, N.add_comm.
    change (2^8) with (1*2^8) at 1. rewrite N.mod_add by discriminate 1.
    rewrite N.mod_small by apply getmem_bound, (x86_wtm MDL MEM).
    rewrite getmem_Mb, N.mod_small. destruct (mem _); reflexivity.
    eapply N.le_lt_trans. eapply N.le_add_r. exact LM.
    destruct edx. reflexivity. apply N.log2_lt_pow2. reflexivity. transitivity 4. assumption. reflexivity.

  Unshelve. all: focus_addr ADDR 26 (* je 182 *).
  destruct (mem eax) eqn:BYT; bsimpl in XS; reduce_main_inv XS EX RET;
      (repeat first [ assumption | split ]).
    etransitivity. apply (proj1 NF). apply N.le_add_r.
    intros i H1 H2. rewrite N.add_1_r in H2. apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2.
      apply NF; assumption.
      subst i. rewrite BYT. reflexivity.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 32 (* incl %eax *).
  split.
    rewrite (N.mod_small eax).
      rewrite N.mod_small by assumption. exact NF.
      eapply N.le_lt_trans. eapply N.le_add_r. eassumption.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 33 (* xorl $0x2, %edx *).
  split. assumption. eexists.
  assert (XORLO: N.lxor (edx mod 2^32) 2 < 4).
    change 4 with (2^2). apply logic_op_bound.
      intros. rewrite N.lxor_spec,Z1,Z2. reflexivity.
      rewrite <- (N.mod_small edx 4) by assumption. rewrite N.mod_small.
        apply N.mod_lt. discriminate 1.
        transitivity 4. apply N.mod_lt. discriminate 1. reflexivity.
      reflexivity.
  repeat split.
    apply XORLO.
    rewrite N.mod_small.
      rewrite N.eqb_sym. reflexivity.
      transitivity 4. apply XORLO. reflexivity.

  Unshelve. all: focus_addr ADDR 36 (* je 49 *).
  destruct (edx =? 0) eqn:EDX0; bsimpl in XS; reduce_main_inv XS EX RET;
  (split; try assumption).
    apply Neqb_ok in EDX0. rewrite EDX,EDX0. reflexivity.
    eexists. split. exact EDX. assumption.

  Unshelve. all: focus_addr ADDR 38 (* cmpb %dh, (%eax) *).
  repeat first [ assumption | split ].
    rewrite (N.mod_small edx), (N.mod_small edx) by (transitivity 4; [assumption|reflexivity]).
    rewrite N.shiftr_eq_0, N.sub_0_r, N.add_comm.
    change (2^8) with (1*2^8) at 1. rewrite N.mod_add by discriminate 1.
    rewrite N.mod_small by apply getmem_bound, (x86_wtm MDL MEM).
    rewrite getmem_Mb, N.mod_small. destruct (mem _); reflexivity.
    eapply N.le_lt_trans. eapply N.le_add_r. exact LM.
    destruct edx. reflexivity. apply N.log2_lt_pow2. reflexivity. transitivity 4. assumption. reflexivity.

  Unshelve. all: focus_addr ADDR 40 (* je 182 *).
  destruct (mem eax) eqn:BYT; bsimpl in XS; reduce_main_inv XS EX RET;
      (repeat first [ assumption | split ]).
    etransitivity. apply (proj1 NF). apply N.le_add_r.
    intros i H1 H2. rewrite N.add_1_r in H2. apply N.lt_succ_r, N.lt_eq_cases in H2. destruct H2.
      apply NF; assumption.
      subst i. rewrite BYT. reflexivity.

  Unshelve. all: focus_addr ADDR 46 (* 46: incl %eax *).
  rewrite (N.mod_small eax).
    rewrite N.mod_small by assumption. exact NF.
    eapply N.le_lt_trans. eapply N.le_add_r. eassumption.

  Unshelve. all: focus_addr ADDR 47 (* xorl %edx, %edx *).
  split. assumption. reflexivity.

  (* movl (%eax), %ecx *)
  Unshelve. all: match type of ADDR with _=49 => idtac | _=75 => idtac | _=101 => idtac | _=127 => idtac | _ => shelve end.
  all: repeat first [ assumption | split ].

  (* 51: addl $0x4, %eax *)
  Unshelve. all: match type of ADDR with _=51 => idtac | _=77 => idtac | _=103 => idtac | _=129 => idtac | _ => shelve end.
  all: rewrite (N.mod_small eax) by (eapply N.le_lt_trans; [ apply N.le_add_r | exact PRE ]);
  rewrite N.mod_small by assumption;
  rewrite N.add_sub;
  repeat first [ assumption | split ]; rewrite N.add_comm; apply N.le_add_r.

  (* subl %ecx, %edx *)
  Unshelve. all: match type of ADDR with _=54 => idtac | _=80 => idtac | _=106 => idtac | _=132 => idtac | _ => shelve end.
  all: repeat first [ assumption | split ];
  change (0 mod _) with 0; rewrite N.add_0_r;
  rewrite (N.mod_small (getmem _ _ _ _)) by apply getmem_bound, (x86_wtm MDL MEM);
  reflexivity.

  (* addl $0xfefefeff, %ecx *)
  Unshelve. all: match type of ADDR with _=56 => idtac | _=82 => idtac | _=108 => idtac | _=134 => idtac | _ => shelve end.
  all: unfold towidth;
  rewrite (N.mod_small (getmem _ _ _ _)) by (change 32 with (Mb * N.of_nat 4); apply getmem_bound, (x86_wtm MDL MEM));
  repeat first [ assumption | split ];
  [ rewrite (N.add_comm (2^32)); rewrite <- (N.add_sub_assoc _ (2^32)) by discriminate 1; reflexivity
  | rewrite N.mod_mod by discriminate 1; change 4278124287 with (2^32 - ones 8 4); destruct (ones 8 4 <=? _) eqn:CMP;
    [ apply N.leb_le in CMP; rewrite N.add_sub_assoc by discriminate 1; rewrite N.add_comm; rewrite <- N.add_sub_assoc by exact CMP;
      rewrite N.add_mod by discriminate 1; rewrite N.add_0_l; rewrite N.mod_mod by discriminate 1;
      rewrite N.mod_small;
      [ apply N.sub_lt, N.ltb_lt in CMP; [ rewrite CMP; reflexivity | reflexivity ]
      | eapply N.le_lt_trans;
        [ apply N.le_sub_l
        | change 32 with (Mb * N.of_nat 4); apply getmem_bound, (x86_wtm MDL MEM) ] ]
    | apply N.leb_gt in CMP; rewrite N.mod_small;
      [ replace (_ <? _) with false;
        [ reflexivity
        | symmetry; apply N.ltb_ge; apply N.le_add_r ]
      | apply (N.le_lt_add_lt (ones 8 4) (ones 8 4));
        [ reflexivity
        | rewrite (N.add_comm (2^32)); rewrite <- N.add_assoc; apply N.add_lt_le_mono;
          [ exact CMP
          | rewrite N.sub_add by discriminate 1; reflexivity ] ] ] ] ].

  (* decl %edx *)
  Unshelve. all: match type of ADDR with _=62 => idtac | _=88 => idtac | _=114 => idtac | _=140 => idtac | _ => shelve end.
  all: repeat first [ assumption | split ];
  rewrite N.mod_mod by discriminate 1; destruct (getmem _ _ _ (eax-4)) eqn:GM;
  [ reflexivity
  | assert (BND: N.pos p < 2^(Mb * N.of_nat 4)) by (rewrite <- GM; apply getmem_bound, (x86_wtm MDL MEM));
    rewrite (N.mod_small (2^32-_)) by (apply N.sub_lt; [ apply N.lt_le_incl; exact BND | reflexivity ]);
    rewrite <- N.add_sub_assoc by (apply N.le_add_le_sub_l, N.lt_pred_le; rewrite N.add_1_r, N.pred_succ; exact BND);
    rewrite N.add_comm; rewrite <- (N.mul_1_l (2^32)) at 2; rewrite N.mod_add by discriminate 1;
    rewrite N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply N.sub_lt; [ apply N.lt_le_incl; exact BND | reflexivity ] ]);
    rewrite <- N.sub_add_distr, N.add_comm, N.sub_add_distr, <- N.pred_sub;
    rewrite N.lnot_sub_low by (apply N.log2_lt_pow2; [ reflexivity | exact BND ]);
    reflexivity ].

  (* jae 153 *)
  Unshelve. all: match type of ADDR with _=63 => idtac | _=89 => idtac | _=115 => idtac | _=141 => idtac | _ => shelve end.
  all: destruct (ones 8 4 <=? getmem _ _ _ _) eqn:UF; [ apply N.leb_le in UF | apply N.leb_gt in UF ];
  bsimpl in XS; reduce_main_inv XS EX RET;
  repeat first [ assumption | split ];
  [ rewrite ECX; unfold towidth; rewrite <- N.add_sub_assoc by exact UF;
    rewrite N.add_mod, N.mod_same by discriminate 1; rewrite N.add_0_l;
    rewrite N.mod_mod by discriminate 1;
    rewrite N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply getmem_bound, (x86_wtm MDL MEM) ]);
    reflexivity
  | change 32 with (Mb*4) in UF; destruct (below_ones _ _ _ (x86_wtm MDL MEM) UF) as [i [I4 ZB]]; exists (eax-4+i); repeat split;
    [ rewrite <- (N.add_0_r (getmem _ _ _ _)); apply N.add_le_mono; [ apply (proj1 NF) | apply N.le_0_l ]
    | rewrite <- (N.sub_add 4 eax) at 2 by assumption; apply N.add_lt_mono_l; assumption
    | assumption ] ].

  (* 65: xorl %ecx, %edx *)
  Unshelve. all: match type of ADDR with _=65 => idtac | _=91 => idtac | _=117 => idtac | _=143 => idtac | _ => shelve end.
  all: repeat first [ assumption | split ];
  rewrite N.mod_small;
  [ rewrite N.mod_small;
    [ reflexivity
    | eapply N.le_lt_trans;
      [ apply N.le_sub_l
      | apply getmem_bound; apply (x86_wtm MDL MEM) ] ]
  | unfold N.lnot; apply logic_op_bound;
    [ intros; rewrite N.lxor_spec,Z1,Z2; reflexivity
    | apply getmem_bound; apply (x86_wtm MDL MEM)
    | apply N.lt_pred_l; discriminate 1 ] ].

  (* andl $0x1010100, %edx *)
  Unshelve. all: match type of ADDR with _=67 => idtac | _=93 => idtac | _=119 => idtac | _=145 => idtac | _ => shelve end.
  all: rewrite N.mod_small;
  [ rewrite N.mod_small;
    [ repeat first [ assumption | split ]
    | apply logic_op_bound;
      [ intros; rewrite N.land_spec,Z1,Z2; reflexivity
      | apply logic_op_bound;
        [ intros; rewrite N.lxor_spec,Z1,Z2; reflexivity
        | unfold N.lnot; apply logic_op_bound;
          [ intros; rewrite N.lxor_spec,Z1,Z2; reflexivity
          | apply getmem_bound, (x86_wtm MDL MEM)
          | reflexivity ]
        | eapply N.le_lt_trans; [ apply N.le_sub_l | apply getmem_bound, (x86_wtm MDL MEM) ] ]
      | reflexivity ] ]
  | apply logic_op_bound;
    [ intros; rewrite N.lxor_spec,Z1,Z2; reflexivity
    | unfold N.lnot; apply logic_op_bound;
      [ intros; rewrite N.lxor_spec,Z1,Z2; reflexivity
      | apply getmem_bound, (x86_wtm MDL MEM)
      | reflexivity ]
    | eapply N.le_lt_trans; [ apply N.le_sub_l | apply getmem_bound; apply (x86_wtm MDL MEM) ] ] ].

  (* jne 153 *)
  Unshelve. all: match type of ADDR with _=73 => idtac | _=99 => idtac | _=125 => idtac | _=151 => idtac | _ => shelve end.
  all: destruct (N.land _ _) eqn:TST; bsimpl in XS; reduce_main_inv XS EX RET;
  repeat first [ assumption | split ];
  [ etransitivity; [ apply (proj1 NF) | apply N.le_sub_l ]
  | intros i IBOT ITOP; destruct (N.lt_ge_cases i (eax-4));
    [ apply (proj2 NF); assumption
    | rewrite <- (N.sub_add _ _ H), N.add_comm; apply noborrow_nonil with (w:=4);
      [ apply (x86_wtm MDL MEM)
      | exact PRE3
      | exact TST
      | apply (N.add_lt_mono_r _ _ (eax-4)); rewrite (N.sub_add _ _ H), (N.add_sub_assoc _ _ _ PRE), N.add_comm, N.add_sub; exact ITOP ] ]
  | unfold towidth; rewrite <- N.add_sub_assoc by assumption;
        rewrite N.add_mod,N.mod_same by discriminate 1; rewrite N.add_0_l;
        rewrite N.mod_mod by discriminate 1; rewrite N.mod_small;
        [ exact ECX
        | eapply N.le_lt_trans; [ apply N.le_sub_l | apply getmem_bound, (x86_wtm MDL MEM) ] ]
  | assert (TST': N.pos p > 0) by reflexivity; rewrite <- TST in TST'; change 32 with (Mb*4) in TST'; apply borrow_nil in TST';
    [ destruct TST' as [n [N4 MN]]; exists (eax - 4 + n); split;
      [ split;
        [ etransitivity; [ apply (proj1 NF) | apply N.le_add_r ]
        | rewrite <- (N.sub_add 4 eax) at 2 by exact PRE; apply N.add_lt_mono_l; exact N4 ]
      | exact MN ]
    | apply (x86_wtm MDL MEM)
    | exact PRE3 ] ].

  Unshelve. all: focus_addr ADDR 153 (* subl $0x4, %eax *).
  rewrite (N.mod_small eax) by assumption.
  rewrite <- N.add_sub_assoc by assumption.
  rewrite N.add_mod, N.mod_same, N.add_0_l, N.mod_mod by discriminate 1.
  rewrite N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | assumption ]).
  change 3 with (4-1). rewrite N.add_sub_assoc by discriminate 1. rewrite N.sub_add by assumption.
  repeat first [ assumption | split ].
    eapply N.le_lt_trans. apply N.le_sub_l. assumption.
    exists i. repeat first [ assumption | split ]. rewrite N.sub_1_r. apply N.lt_le_pred. assumption.

  Unshelve. all: focus_addr ADDR 156 (* subl $0xfefefeff, %ecx *).
  unfold towidth. repeat first [ assumption | split ].

    rewrite N.mod_mod by discriminate 1.
    rewrite N.add_comm. rewrite <- N.add_sub_assoc by discriminate 1. rewrite <- (N.mod_small (2^32-_) (2^32)) by reflexivity. rewrite <- N.add_mod by discriminate 1.
    rewrite (N.add_comm (2^32) _). rewrite <- N.add_sub_assoc by discriminate 1. rewrite <- N.add_assoc. rewrite N.add_mod by discriminate 1.
    rewrite N.add_0_r. rewrite N.mod_mod by discriminate 1. rewrite N.mod_small. reflexivity.
    apply getmem_bound. apply (x86_wtm MDL MEM).

    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 162 (* cmpb $0x0, $cl *).
  repeat first [ assumption | split ].

    rewrite N.sub_0_r, N.add_mod, N.add_0_l, N.mod_mod, N.mod_mod by discriminate 1.
    do 2 rewrite <- N.land_ones. rewrite <- N.land_assoc. change (N.land (N.ones _) _) with (N.ones 8).
    change 32 with (Mb*4). rewrite getmem_mul, N.land_lor_distr_l. do 2 rewrite N.land_ones.
    rewrite N.shiftl_mul_pow2, N.mod_mul, N.lor_0_r by discriminate 1. rewrite N.mod_small by apply (x86_wtm MDL MEM).
    destruct (mem eax); reflexivity.

    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 165 (* je 182 *).
  destruct (mem eax) eqn:MA; bsimpl in XS; reduce_main_inv XS EX RET;
      repeat first [ assumption | split ].
    transitivity eax. apply (proj1 NF). apply N.le_add_r.
    rewrite N.add_1_r. intros j JBOT JTOP. apply N.lt_succ_r,N.lt_eq_cases in JTOP. destruct JTOP.
      apply (proj2 NF); assumption.
      subst j. rewrite MA. reflexivity.
    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 167 (* incl %eax *).
  rewrite (N.mod_small eax) by (eapply N.le_lt_trans; [ apply N.le_add_r | eassumption ]).
  rewrite N.mod_small by (eapply N.le_lt_trans; [|eassumption]; apply N.add_le_mono_l; discriminate 1).
  rewrite N.add_sub. rewrite <- N.add_assoc.
  repeat first [ assumption | split ].
    rewrite N.add_comm. apply N.le_add_r.
    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 168 (* testb %ch, %ch *).
  repeat first [ assumption | split ].

    rewrite N.land_diag. unfold cast. rewrite (N.mod_small (getmem _ _ _ _)) by apply getmem_bound, (x86_wtm MDL MEM).
    change 32 with (Mb*4). rewrite getmem_mul. change (N.pred 4) with 3. rewrite getmem_mul.
    rewrite N.shiftl_lor, N.shiftl_shiftl, N.lor_assoc, <- N.land_ones, N.land_lor_distr_l.
    do 2 rewrite N.land_ones.
    rewrite (N.shiftl_mul_pow2 _ (_+_)). rewrite N.mod_mul by discriminate 1.
    rewrite N.lor_0_r, <- N.land_ones, N.shiftr_land, N.shiftr_lor.
    rewrite N.shiftr_shiftl_r by discriminate 1. rewrite N.shiftr_0_r.
    rewrite shiftr_low_pow2 by apply (x86_wtm MDL MEM). rewrite N.lor_0_l.
    change (N.shiftr _ _) with (N.ones 8). rewrite N.land_ones. rewrite N.mod_small by apply (x86_wtm MDL MEM).
    rewrite <- N.pred_sub. erewrite N.lt_succ_pred by (eapply N.lt_le_trans; [ apply N.lt_0_1 | assumption ]).
    destruct (mem eax); reflexivity.

    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 170 (* 170: je 182 *).
  destruct (mem eax) eqn:MA; bsimpl in XS; reduce_main_inv XS EX RET;
      repeat first [ assumption | split ].
    transitivity eax. apply (proj1 NF). apply N.le_add_r.
    rewrite N.add_1_r. intros j JBOT JTOP. apply N.lt_succ_r,N.lt_eq_cases in JTOP. destruct JTOP.
      apply (proj2 NF); assumption.
      subst j. rewrite MA. reflexivity.
    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 172 (* shrl $0x10, %ecx *).
  repeat first [ assumption | split ].
    simpl (N.land _ _). rewrite N.mod_small by apply getmem_bound, (x86_wtm MDL MEM).
    change 32 with (Mb*4). rewrite getmem_mul. change (N.pred 4) with 3. rewrite getmem_mul.
    do 2 (rewrite N.shiftr_lor; rewrite N.shiftr_shiftl_r by discriminate 1).
    rewrite shiftr_low_pow2 by (etransitivity; [ apply (x86_wtm MDL MEM) | reflexivity ]).
    rewrite shiftr_low_pow2 by apply (x86_wtm MDL MEM).
    do 2 rewrite N.lor_0_l. rewrite N.shiftr_0_r by reflexivity.
    do 2 rewrite <- N.add_1_r. rewrite N.sub_add by assumption. reflexivity.

    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 175 (* incl %eax *).
  rewrite (N.mod_small eax) by (eapply N.le_lt_trans; [ apply N.le_add_r | eassumption ]).
  rewrite N.mod_small by (eapply N.le_lt_trans; [ apply (N.le_add_r _ 1) | rewrite <- N.add_assoc; assumption ]).
  rewrite <- N.add_assoc.
  repeat first [ assumption | split ].
    exists i. repeat first [assumption | split ].

  Unshelve. all: focus_addr ADDR 176 (* cmpb $0x0, %cl *).
  repeat first [ assumption | split ].

    rewrite N.sub_0_r, N.add_mod, N.add_0_l, N.mod_mod, N.mod_mod by discriminate 1.
    do 2 rewrite <- N.land_ones. rewrite <- N.land_assoc. change (N.land (N.ones _) _) with (N.ones 8).
    change 16 with (Mb*2). rewrite getmem_mul, N.land_lor_distr_l. do 2 rewrite N.land_ones.
    rewrite N.shiftl_mul_pow2, N.mod_mul, N.lor_0_r by discriminate 1. rewrite N.mod_small by apply (x86_wtm MDL MEM).
    destruct (mem eax); reflexivity.

    exists i. repeat first [ assumption | split ].

  Unshelve. all: focus_addr ADDR 179 (* je 182 *).
  destruct (mem eax) eqn:MA; bsimpl in XS; reduce_main_inv XS EX RET;
      repeat first [ assumption | split ].
    transitivity eax. apply (proj1 NF). apply N.le_add_r.
    rewrite N.add_1_r. intros j JBOT JTOP. apply N.lt_succ_r,N.lt_eq_cases in JTOP. destruct JTOP.
      apply (proj2 NF); assumption.
      subst j. rewrite MA. reflexivity.
    apply N.le_lteq in PRE3. destruct PRE3 as [H|H].
      rewrite N.add_1_r in H. apply N.lt_succ_r, N.le_lteq in H. destruct H as [H|H].
        apply (proj2 NF) in H; [|assumption]. rewrite PRE2 in H. discriminate H.
        subst i. rewrite PRE2 in MA. discriminate MA.
      subst i. assumption.

  Unshelve. all: focus_addr ADDR 181 (* incl %eax *).
  rewrite (N.mod_small eax) by (eapply N.le_lt_trans; [ apply N.le_add_r | eassumption ]).
  rewrite N.mod_small by assumption.
  split; assumption.

  Unshelve. all: focus_addr ADDR 182 (* subl 0x4(%esp), %eax *).
  rewrite (N.mod_small esp) by (eapply N.lt_le_trans; [|exact ESPLO]; apply N.lt_add_pos_r; reflexivity).
  rewrite (N.mod_small (esp+4)) by (eapply N.lt_le_trans; [|exact ESPLO]; apply N.add_lt_mono_l; reflexivity).
  rewrite (N.mod_small eax) by apply (x86_regsize MDL EAX).
  rewrite <- N.add_sub_assoc by apply (proj1 NF).
  rewrite N.add_mod, N.mod_same, N.add_0_l, N.mod_mod by discriminate 1.
  rewrite N.mod_small by (eapply N.le_lt_trans; [ apply N.le_sub_l | apply (x86_regsize MDL EAX) ]).
  rewrite (N.add_comm _ (_-_)). rewrite N.sub_add by apply (proj1 NF).
  split; assumption.

  Unshelve. all: focus_addr ADDR 186 (* retl *).
  destruct XS. subst s1' x1. apply inj_exit in EX. subst a.
  unfold strlen_main_inv, strlen_postcond. simpl_stores.
  destruct (N.eq_dec _ _); [| contradict n; reflexivity ].
  rewrite N.mod_small by (eapply N.lt_le_trans; [|exact ESPLO]; apply N.add_lt_mono_l; reflexivity).
  split.
    reflexivity.
    exists eax. repeat first [ assumption | split ]. intros i ITOP. apply (proj2 NF).
      apply N.le_add_r.
      apply N.add_lt_mono_l. assumption.
Qed.
