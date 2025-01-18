Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import nops_o_rec_nop_armv8.

Require Import Lia.
Require Import Bool.

(* Only used for bookkeeping *)
Require Import String.

Import ARM8Notations.
Open Scope N.

Definition valeqb (l r:value) : bool :=
  match l with
  | VaN nl wl => match r with VaN nr wr => andb (nl =? nr) (wl =? wr) | _ => false end
  | _ => false
  end.
  
Definition recnop_exit sp (t:trace) :=
  match t with (Addr a,ts)::_ => match a with
  | 0x00100064 => valeqb (Ⓠsp) (ts R_SP)
  | _ => false
  end | _ => false end.
  
Definition recnop_invs (x0:N) (ret_ptr sp:addr) (t:trace) :=
  match t with (Addr a, s)::_ => match a with
  | 0x00100044 => Some (s R_X0 = Ⓠx0 /\ s R_X30 =  Ⓠret_ptr /\ s R_SP = Ⓠsp)
  | 0x00100064 => Some (s R_X0 = Ⓠ0 /\ s R_X30 =  Ⓠret_ptr /\ s R_SP = Ⓠsp)
  | _ => None end | _ => None end.
  
Theorem recnop_partial_correctness:
  ∀ s x0 ret_ptr sp m t s' x'
         (ENTRY: startof t (x',s') = (Addr 0x00100044,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = Ⓜm)
         (X0: s R_X0 = Ⓠx0)
         (X30:  s R_X30 = Ⓠret_ptr)
         (SP: s R_SP = Ⓠsp)
,
  satisfies_all rec_nop (recnop_invs x0 ret_ptr sp) (recnop_exit sp) ((x',s')::t).
Proof.
Local Ltac step := time arm8_step.
intros. generalize dependent x0.
  induction x0 using N.peano_ind; intros. 
  (* 0; base *)
  apply prove_invs. simpl. rewrite ENTRY. step. repeat (split || assumption).
  (* 0; inductive *)
    intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply recnop_welltyped).
  clear - PRE MDL. rename t1 into t. rename s1 into s.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 64 PRE.
  destruct PRE as [X0 [X30 SP]].
  step. step. step. step. step. step. repeat first [ split | reflexivity ].
  
  unfold recnop_exit, get_precondition in *. destruct ( valeqb (Ⓠsp) (s R_SP) ) eqn:SP;
    [ contradiction| unfold recnop_invs in PRE].
    destruct PRE as [X0 [X30 SP']]. unfold valeqb in SP. unfold models in MDL.
    specialize (MDL R_SP (NumT 64)). unfold arm8typctx in MDL.
    assert (HELP: Some (NumT 64) = Some (NumT 64)) by reflexivity; apply MDL in HELP.
    inversion HELP; subst. destruct (s R_SP); try discriminate. clear MDL X30 X0 HELP.
    Search (_ && _ = false). apply andb_false_elim in SP.
    inversion SP'; subst. destruct SP; now rewrite N.eqb_neq in e.
  
  (* N.succ *)