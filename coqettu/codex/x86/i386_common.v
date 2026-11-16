(* Shared ABI definitions for Codex's musl i386 proofs. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith.
Import X86Notations.
Open Scope N.

(* getmem wraps addresses modulo 2^32, including the stack argument slot. *)
Definition cdecl_arg (s : store) : N :=
  getmem 32 LittleE 4 (s V_MEM32) (4 + s R_ESP).

(* Frame at the RET instruction, before the return address is popped. *)
Definition cdecl_leaf_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_ESP = s0 R_ESP /\
  s R_EBX = s0 R_EBX /\ s R_ESI = s0 R_ESI /\
  s R_EDI = s0 R_EDI /\ s R_EBP = s0 R_EBP /\
  s A_READ = s0 A_READ /\ s A_WRITE = s0 A_WRITE.

Definition cdecl_leaf_post (s0 : store) (value : N) (s : store) : Prop :=
  s R_EAX = value /\ cdecl_leaf_frame s0 s.

Definition at_address (a : N) (t : trace) : bool :=
  match t with (Addr pc, _) :: _ => pc =? a | _ => false end.

(* Proposition generators: the entry accepts every store; the return-site
   assertion specifies both the result and the ABI frame. *)
Definition leaf_invs (entry ret : N) (s0 : store) (value : N)
    (t : trace) : option Prop :=
  match t with
  | (Addr pc, s) :: _ =>
      if pc =? entry then Some (s = s0)
      else if pc =? ret then Some (cdecl_leaf_post s0 value s)
      else None
  | _ => None
  end.

Lemma leaf_correct_extend : forall p prog entry ret s0 value t xs,
  p ⊆2 prog ->
  (forall s, p s entry <> None) ->
  (forall s, p s ret <> None) ->
  (forall xs' t', startof t' xs' = (Addr entry, s0) ->
    satisfies_all p (leaf_invs entry ret s0 value) (at_address ret) (xs'::t')) ->
  startof t xs = (Addr entry, s0) ->
  satisfies_all prog (leaf_invs entry ret s0 value) (at_address ret) (xs::t).
Proof.
  intros p prog entry ret s0 value t xs EXT EN RT LOCAL ENTRY.
  eapply satisfies_all_pmono; [exact EXT | |].
  - intros a s tl EX NO. unfold leaf_invs.
    destruct (a =? entry) eqn:E.
    + apply N.eqb_eq in E. subst a. exfalso. exact (EN s NO).
    + destruct (a =? ret) eqn:R; [|reflexivity].
      apply N.eqb_eq in R. subst a. exfalso. exact (RT s NO).
  - intros xs' t' START. apply LOCAL. rewrite START. exact ENTRY.
Qed.

Definition i386_ret : stmt :=
  Move R_EIP (Load (Var V_MEM32) (Var R_ESP) LittleE 4) $;
  Move R_ESP (BinOp OP_PLUS (Var R_ESP) (Word 4 32)) $;
  Jmp (Var R_EIP).

(* Unlike the pre-RET frame, this frame includes the popped return address. *)
Definition cdecl_returned (s0 : store) (value : N) (x : exit) (s : store) :=
  x = Addr (getmem 32 LittleE 4 (s0 V_MEM32) (s0 R_ESP)) /\
  s R_EAX = value /\ s R_ESP = (s0 R_ESP + 4) mod 2^32 /\
  s V_MEM32 = s0 V_MEM32 /\
  s R_EBX = s0 R_EBX /\ s R_ESI = s0 R_ESI /\
  s R_EDI = s0 R_EDI /\ s R_EBP = s0 R_EBP /\
  s A_READ = s0 A_READ /\ s A_WRITE = s0 A_WRITE.

Lemma cdecl_ret_step : forall p ret s0 value s x s',
  p s ret = Some (1, i386_ret) ->
  cdecl_leaf_post s0 value s ->
  can_step p ((x,s'), (Addr ret,s)) ->
  cdecl_returned s0 value x s'.
Proof.
  intros p ret s0 value s x s' LOOK POST STEP.
  inversion STEP; subst.
  rewrite LOOK in LU. injection LU as SZ CODE. subst sz q.
  unfold i386_ret in XS. step_stmt XS. psimpl in XS.
  destruct XS as [[STORE JUMP] ACC]. rewrite STORE, JUMP.
  unfold cdecl_returned. psimpl.
  unfold cdecl_leaf_post, cdecl_leaf_frame in POST.
  destruct POST as (AX & MEM & SP & BX & SI & DI & BP & RD & WR).
  rewrite AX, MEM, SP, BX, SI, DI, BP, RD, WR.
  repeat split; reflexivity.
Qed.

Lemma leaf_return : forall p entry ret s0 value t s x s',
  entry <> ret ->
  p s ret = Some (1, i386_ret) ->
  satisfies_all p (leaf_invs entry ret s0 value) (at_address ret)
    ((Addr ret,s)::t) ->
  exec_prog p ((x,s')::(Addr ret,s)::t) ->
  unterminated (at_address ret) t ->
  cdecl_returned s0 value x s'.
Proof.
  intros p entry ret s0 value t s x s' DIFF LOOK SA XP UT.
  assert (POST : cdecl_leaf_post s0 value s).
  { pose proof (satall_trueif_inv p _ _ _ SA (exec_prog_tail _ _ _ XP) UT) as H.
    unfold leaf_invs in H.
    rewrite (proj2 (N.eqb_neq ret entry) (not_eq_sym DIFF)), N.eqb_refl in H.
    exact H. }
  eapply cdecl_ret_step; [exact LOOK | exact POST |].
  exact (exec_prog_final _ _ _ _ XP).
Qed.

Definition cdecl_saved : list x86var :=
  R_EBX :: R_ESI :: R_EDI :: R_EBP :: nil.

Ltac prove_cdecl_saved :=
  intros v IN; cbn in IN;
  repeat destruct IN as [IN | IN]; try contradiction;
  subst v; apply noassign_prog_same; prove_noassign.
