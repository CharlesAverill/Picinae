(* Transport checked local VCs to a larger program without regenerating IL. *)
Require Import Picinae_amd64.
From Stdlib Require Import NArith.
Import X64Notations.
Open Scope N.

Definition program_extends (p q : program) :=
  forall s a code, p s a=Some code -> q s a=Some code.
Definition inv_supported (p : program) (I : trace -> option Prop) :=
  forall t, match t with
  | (Addr a,s)::_ => p s a=None -> I t=None
  | _ => I t=None
  end.
Definition invariants_agree_on (p : program) (I J : trace -> option Prop)
  (xp xq : trace -> bool) :=
  forall a s t code, p s a=Some code ->
    I ((Addr a,s)::t)=J ((Addr a,s)::t) /\ xp ((Addr a,s)::t)=xq ((Addr a,s)::t).

Lemma effinv_has_code : forall p I xp b t,
  inv_supported p I -> true_inv (effinv b p I xp t) ->
  exists a s tl code, t=(Addr a,s)::tl /\ p s a=Some code.
Proof.
  intros p I xp b t SUP H. specialize (SUP t).
  destruct t as [|[[a|i] s] tl];
    try (unfold effinv,effinv' in H; rewrite SUP in H; destruct (xp _); contradiction).
  destruct (p s a) as [code|] eqn:LOOK.
  - exists a,s,tl,code. split; [reflexivity | exact LOOK].
  - specialize (SUP eq_refl). unfold effinv,effinv' in H.
    rewrite SUP,LOOK in H. destruct (xp _); contradiction.
Qed.

Lemma effinv_program_agree : forall p q I J xp xq b a s t code,
  program_extends p q -> invariants_agree_on p I J xp xq ->
  p s a=Some code ->
  effinv b p I xp ((Addr a,s)::t)=effinv b q J xq ((Addr a,s)::t).
Proof.
  intros p q I J xp xq b a s t code EXT AGR LOOK.
  destruct (AGR a s t code LOOK) as [INV EXIT].
  unfold effinv,effinv'. rewrite INV,EXIT,LOOK,(EXT _ _ _ LOOK).
  reflexivity.
Qed.

Theorem nextinv_program_transport_core : forall p q I J xp xq b t,
  program_extends p q -> inv_supported p I -> invariants_agree_on p I J xp xq ->
  nextinv' p I xp b t -> nextinv' q J xq b t.
Proof.
  cofix IH. intros p q I J xp xq b t EXT SUP AGR NI.
  inversion NI; subst.
  - destruct (effinv_has_code p I xp b t SUP TRU) as [a [s [tl [code [EQ LOOK]]]]].
    subst t. apply NIHere'.
    rewrite <-(effinv_program_agree p q I J xp xq b a s tl code EXT AGR LOOK).
    exact TRU.
  - eapply NIStep'.
    + rewrite <-(effinv_program_agree p q I J xp xq b a s t0 (sz,q0) EXT AGR IL).
      exact NOI.
    + exact (EXT _ _ _ IL).
    + intros. eapply IH; [exact EXT | exact SUP | exact AGR | eapply STEP; eassumption].
Qed.

Definition head_invariant (I : trace -> option Prop) :=
  forall xs t1 t2, I (xs::t1)=I (xs::t2).
Definition head_exit (xp : trace -> bool) :=
  forall xs t1 t2, xp (xs::t1)=xp (xs::t2).

Theorem nextinv_program_transport : forall p q I J xp xq b a s t,
  program_extends p q -> inv_supported p I -> invariants_agree_on p I J xp xq ->
  head_invariant J -> head_exit xq ->
  nextinv p I xp b ((Addr a,s)::nil) -> nextinv q J xq b ((Addr a,s)::t).
Proof.
  intros p q I J xp xq b a s t EXT SUP AGR HEAD EXIT NI XP.
  eapply nextinv_apptrace with (t1:=t) (t2:=nil).
  - intros. apply EXIT.
  - eapply nextinv_program_transport_core; [exact EXT | exact SUP | | ].
    + intros a0 s0 tl code LOOK.
      destruct (AGR a0 s0 tl code LOOK) as [INV EX].
      split; [rewrite INV; apply HEAD | exact EX].
    + apply NI. constructor.
Qed.
