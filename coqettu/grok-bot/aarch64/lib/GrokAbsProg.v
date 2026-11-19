(* Grok Bot (agent coqettu): reasoning about a caller inside an abstract
   program.  When a function calls through a pointer (bsearch, lfind, lsearch
   call a comparator with blr), its proof must quantify over the whole program
   prog containing both the caller's code and the unknown callee.  Picinae's
   step and destruct_inv tactics compute (prog s a), which is stuck for an
   abstract prog.  These lemmas
   - replace prog by the caller's code p1 (p1 ⊆2 prog) when stepping at an
     address of p1 (effinv_sub), and
   - replace prog by the total program ptot in pre/postconditions at a point
     known to be code, so destruct_inv can enumerate the invariant points
     (getpre_tot, getpost_tot). *)
From Stdlib Require Import Utf8 NArith.
Require Import Picinae_armv8.
Open Scope N.

Definition ptot : program := fun _ _ => Some (4, Nop).

Lemma effinv_sub: ∀ p1 p (PS: p1 ⊆2 p) n f b a s t insn, p1 s a = Some insn ->
  effinv b p (make_invs n p f) (make_exits n p f) ((Addr a,s)::t) =
  effinv b p1 (make_invs n p1 f) (make_exits n p1 f) ((Addr a,s)::t).
Proof.
  intros p1 p PS n f b a s t insn IL. unfold effinv, effexit, make_invs, make_exits. cbv beta iota.
  rewrite IL, (PS _ _ _ IL). reflexivity.
Qed.

Lemma getpre_tot: ∀ p n f a s t,
  true_inv (get_precondition p (make_invs n p f) (make_exits n p f) a s t) ->
  true_inv (get_precondition ptot (make_invs n ptot f) (make_exits n ptot f) a s t).
Proof.
  intros p n f a s t H. unfold get_precondition, make_invs, make_exits, ptot in *. cbv beta iota in *.
  destruct (p s a); [exact H | destruct (match f _ _ _ _ _ _ with Some (true,m) => _ | _ => false end); contradiction].
Qed.

Lemma getpost_tot: ∀ p n f a s t,
  true_inv (get_postcondition p (make_invs n p f) (make_exits n p f) a s t) ->
  true_inv (get_postcondition ptot (make_invs n ptot f) (make_exits n ptot f) a s t).
Proof.
  intros p n f a s t H. unfold get_postcondition, make_invs, make_exits, ptot in *. cbv beta iota in *.
  destruct (p s a); [exact H | contradiction].
Qed.

(* one step (or arrival at an invariant) at an address of p1 inside prog *)
Ltac sub_here P :=
  match goal with |- context[Addr ?a] =>
    eapply nextinv_here; [ erewrite (effinv_sub _ _ P) by reflexivity; reflexivity | hnf; psimpl_goal ];
    idtac "Goal at <" a ">"
  end.
Ltac sub_step P :=
  repeat match goal with [ H: MemAcc _ _ _ _ _ |- _ ] => clear H end;
  first [ eapply NIStep; [ erewrite (effinv_sub _ _ P) by reflexivity; reflexivity
                         | apply P; reflexivity | ISA_symbolic_interp ]
        | sub_here P ].
