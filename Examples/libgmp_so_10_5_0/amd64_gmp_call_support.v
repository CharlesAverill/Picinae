(* Shared invariant composition and leaf preservation contracts. *)
Require Import Picinae_amd64.
From Stdlib Require Import NArith Lia.
Import X64Notations.
Open Scope N.

Definition inv_present (i : option Prop) := match i with Some _ => true | None => false end.
Definition same_inv_support (I J : trace -> option Prop) :=
  forall t, inv_present (I t)=inv_present (J t).
Definition inv_conj (I J : trace -> option Prop) t :=
  match I t,J t with Some P,Some Q => Some (P /\ Q) | _,_ => None end.

Lemma effinv_none_same : forall p I J xp b t,
  same_inv_support I J ->
  (effinv b p I xp t=None <-> effinv b p J xp t=None).
Proof.
  intros p I J xp b t S. specialize (S t).
  unfold effinv,inv_present in *.
  destruct (I t), (J t); try discriminate; destruct b;
    unfold effinv'; destruct (xp t); destruct t as [|[[a|i] s] t];
    try (destruct (p s a)); intuition discriminate.
Qed.

Lemma effinv_conj_none : forall p I J xp b t,
  same_inv_support I J ->
  (effinv b p (inv_conj I J) xp t=None <-> effinv b p I xp t=None).
Proof.
  intros p I J xp b t S. specialize (S t).
  unfold effinv,inv_conj,inv_present in *.
  destruct (I t), (J t); try discriminate; destruct b;
    unfold effinv'; destruct (xp t); destruct t as [|[[a|i] s] t];
    try (destruct (p s a)); intuition discriminate.
Qed.

Lemma effinv_conj_true : forall p I J xp b t,
  same_inv_support I J ->
  (true_inv (effinv b p (inv_conj I J) xp t) <->
    true_inv (effinv b p I xp t) /\ true_inv (effinv b p J xp t)).
Proof.
  intros p I J xp b t S. specialize (S t).
  unfold effinv,inv_conj,inv_present in *.
  destruct (I t), (J t); try discriminate; destruct b;
    unfold effinv'; destruct (xp t); destruct t as [|[[a|i] s] t];
    try (destruct (p s a)); cbn [true_inv]; tauto.
Qed.

Lemma nextinv_conj_core : forall p I J xp b t,
  same_inv_support I J ->
  nextinv' p I xp b t -> nextinv' p J xp b t ->
  nextinv' p (inv_conj I J) xp b t.
Proof.
  cofix IH. intros p I J xp b t SUP A B.
  inversion A; subst.
  - inversion B; subst.
    + apply NIHere'. apply effinv_conj_true; [exact SUP | split; assumption].
    + apply (proj2 (effinv_none_same p I J xp b _ SUP)) in NOI.
      rewrite NOI in TRU. contradiction.
  - inversion B; subst.
    + apply (proj1 (effinv_none_same p I J xp b _ SUP)) in NOI.
      rewrite NOI in TRU. contradiction.
    + rewrite IL in IL0. injection IL0; intros; subst.
      eapply NIStep'.
      * apply effinv_conj_none; [exact SUP | exact NOI].
      * exact IL.
      * intros. eapply IH; [exact SUP | eapply STEP | eapply STEP0]; eassumption.
Qed.

Theorem nextinv_conj : forall p I J xp b t,
  same_inv_support I J ->
  nextinv p I xp b t -> nextinv p J xp b t ->
  nextinv p (inv_conj I J) xp b t.
Proof.
  unfold nextinv. intros. eapply nextinv_conj_core; eauto.
Qed.

(* The equality is for every protected read region, including a return cell. *)
Definition outside_output m0 m d bytes :=
  forall p len, ~overlap 64 p len d bytes ->
    getmem 64 LittleE len m p=getmem 64 LittleE len m0 p.
Definition leaf_abi (initial s : store) :=
  s R_RSP=initial R_RSP /\ s R_RBX=initial R_RBX /\ s R_RBP=initial R_RBP /\
  s R_R12=initial R_R12 /\ s R_R13=initial R_R13 /\
  s R_R14=initial R_R14 /\ s R_R15=initial R_R15.
Definition leaf_frame initial m0 d n (s : store) :=
  leaf_abi initial s /\ outside_output m0 (s V_MEM64) d (8*n).

Lemma outside_output_refl : forall m d bytes, outside_output m m d bytes.
Proof. unfold outside_output; intros; reflexivity. Qed.
Lemma outside_output_store : forall m0 m d bytes offset size out,
  offset+size<=bytes -> outside_output m0 m d bytes ->
  outside_output m0 (setmem 64 LittleE size m (d+offset) out) d bytes.
Proof.
  unfold outside_output. intros m0 m d bytes offset size out B F p len NO.
  rewrite getmem_noverlap.
  - apply F, NO.
  - eapply noverlap_index_r; [exact NO | exact B].
Qed.

Definition frame_invset (I : trace -> option Prop) initial m0 d n t :=
  match I t with
  | Some _ => Some (match t with (_,s)::_ => leaf_frame initial m0 d n s | _ => False end)
  | None => None
  end.
Lemma frame_invset_support : forall I initial m0 d n,
  same_inv_support I (frame_invset I initial m0 d n).
Proof.
  intros I initial m0 d n t. unfold frame_invset,inv_present.
  destruct (I t); reflexivity.
Qed.

Lemma leaf_frame_return_cell : forall initial m0 d n s,
  leaf_frame initial m0 d n s ->
  ~overlap 64 (initial R_RSP) 8 d (8*n) ->
  s R_RSP=initial R_RSP /\ (s V_MEM64) Ⓠ[s R_RSP]=m0 Ⓠ[initial R_RSP].
Proof.
  intros initial m0 d n s [[SP ABI] OUT] SEP.
  split; [exact SP | rewrite SP; apply OUT, SEP].
Qed.
