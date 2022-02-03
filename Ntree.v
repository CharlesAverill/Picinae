Require Import Picinae_theory.
Require Import NArith.
Require Import List.

Open Scope list.

Definition iseqb {X} {_ : EqDec X} (x1 x2 : X) :=
  if x1 == x2 then true else false.

Section assoc.
  Variables K V : Type.
  Variables EQD : EqDec K.
  Definition alist := list (K * V).

  Fixpoint assoc k (l : alist) :=
    match l with
    | nil => None
    | kv::kvs => if k == fst kv then Some (snd kv) else assoc k kvs
    end.

  Definition assoc_def k l d :=
    match assoc k l with
    | None => d
    | Some v => v
    end.

  Fixpoint assoc_remove k l : alist :=
    match l with
    | nil => nil
    | kv :: kvs => (if k == fst kv then nil else kv::nil) ++ assoc_remove k kvs
    end.

  (* Definition assoc_remove k (l : alist) := *)
  (*   filter (fun '(k',v) => negb (iseqb k' k)) l. *)

  Definition assoc_cons_raw k v l : alist := (k,v)::l.
  Definition assoc_cons k v l : alist := (k,v)::assoc_remove k l.

  Theorem assoc_app k l1 l2 :
    assoc k (l1 ++ l2) =
      match assoc k l1 with
      | None => assoc k l2
      | Some v => Some v
      end.
  Proof.
    induction l1 as [|[? ?]]; simpl; [reflexivity|].
    destruct iseq; [reflexivity|assumption].
  Qed.

  Theorem assoc_nomap {A} k f l (HF : forall x : A, k <> fst (f x)) :
    assoc k (map f l) = None.
  Proof.
    induction l as [|a ?]; [reflexivity|].
    simpl.
    destruct iseq; subst; [|assumption].
    edestruct HF.
    reflexivity.
  Qed.

  Theorem assoc_find k l :
    assoc k l = option_map snd (find (fun '(k',v) => iseqb k k') l).
  Proof.
    induction l as [|[? ?] ?]; simpl; [reflexivity|].
    unfold iseqb.
    destruct iseq; [reflexivity|assumption].
  Qed.

  (* Theorem assoc_in' k l : *)
  (*   match assoc k l with *)
  (*   | Some v => In (k,v) l *)
  (*   | None => forall v, ~In (k,v) l *)
  (*   end. *)
  (* Proof. *)
  (*   induction l as [|[? ?] ?]; simpl; [tauto|]. *)
  (*   destruct iseq; subst; [tauto|]. *)
  (*   destruct assoc; [tauto|]. *)
  (*   intros v' HX. *)
  (*   destruct HX as [HX|HX]; [|eapply IHl,HX]. *)
  (*   inversion HX; subst. *)
  (*   tauto. *)
  (* Qed. *)

  Theorem assoc_in k l v (HA : assoc k l = Some v) : In (k,v) l.
  Proof.
    induction l as [|[? ?] ?]; [discriminate|]; simpl in *.
    destruct iseq; subst; [inversion HA; subst|]; tauto.
  Qed.

  Theorem assoc_remove_lookup kr l k :
    assoc k (assoc_remove kr l) = if k == kr then None else assoc k l.
  Proof.
    induction l as [|[? ?] ?]; [destruct iseq; reflexivity|].
    simpl.
    rewrite assoc_app,IHl.
    repeat (destruct iseq; try tauto; subst; simpl).
  Qed.

  Theorem assoc_cons_lookup k v l k' :
    assoc k' (assoc_cons k v l) = assoc k' ((k,v)::l).
  Proof.
    simpl.
    destruct iseq; [reflexivity|].
    rewrite assoc_remove_lookup.
    destruct iseq; tauto.
  Qed.
End assoc.

Arguments assoc {_ _ _}.
Arguments assoc_def {_ _ _}.
Arguments assoc_remove {_ _ _}.
Arguments assoc_cons {_ _ _}.
Arguments assoc_cons_raw {_ _ _}.

Theorem assoc_map {K1 K2 V} {_ : EqDec K1} {_ : EqDec K2} (f : K1 -> K2) k l
        (HF : forall x1 x2 (HEq : f x1 = f x2), x1 = x2) :
  assoc (f k) (map (fun kv : K1 * V => (f (fst kv),snd kv)) l) = assoc k l.
Proof.
  induction l; [reflexivity|].
  simpl.
  destruct (iseq k) as [HX|HX]; destruct iseq; subst; try tauto.
  destruct HX.
  apply HF.
  assumption.
Qed.

Instance eqdec_positive : EqDec positive := {iseq := Pos.eq_dec}.

Section treePN.
  Variable V : Type.

  Inductive treeP := | TPNil | TPBranch (ov : option V) (tx ty : treeP).

  Fixpoint treeP_lookup t p :=
    match t with
    | TPNil => None
    | TPBranch ov tx ty =>
        match p with
        | xH => ov
        | xO p' => treeP_lookup tx p'
        | xI p' => treeP_lookup ty p'
        end
    end.

  Definition treeP_dest t :=
    match t with
    | TPNil => (None,TPNil,TPNil)
    | TPBranch ov tx ty => (ov,tx,ty)
    end.

  Fixpoint treeP_update t p ov :=
    match treeP_dest t with
    | (ov',tx,ty) =>
        match p with
        | xH => TPBranch ov tx ty
        | xO p' => TPBranch ov' (treeP_update tx p' ov) ty
        | xI p' => TPBranch ov' tx (treeP_update ty p' ov)
        end
    end.

  Fixpoint treeP_alist t :=
    match t with
    | TPNil => nil
    | TPBranch ov tx ty =>
        let restx := map (fun kv => (xO (fst kv),snd kv)) (treeP_alist tx) in
        let resty := map (fun kv => (xI (fst kv),snd kv)) (treeP_alist ty) in
        let px := (match ov with None => nil | Some v => (xH,v)::nil end) in
        px ++ restx ++ resty
    end.

  Theorem treeP_lookup_update t p1 p2 ov :
    treeP_lookup (treeP_update t p1 ov) p2 =
      if Pos.eqb p1 p2 then ov else treeP_lookup t p2.
  Proof.
    revert t p2.
    induction p1; intros; destruct t,p2; simpl; apply IHp1 + reflexivity.
  Qed.

  Theorem treeP_update_updated t p ov :
    treeP_lookup (treeP_update t p ov) p = ov.
  Proof.
    rewrite treeP_lookup_update,Pos.eqb_refl.
    reflexivity.
  Qed.

  Theorem treeP_update_frame t p1 p2 ov (HNEq : p1 <> p2) :
    treeP_lookup (treeP_update t p1 ov) p2 = treeP_lookup t p2.
  Proof.
    apply Pos.eqb_neq in HNEq.
    rewrite treeP_lookup_update,HNEq.
    reflexivity.
  Qed.

  Theorem treeP_alist_assoc t p :
    assoc p (treeP_alist t) = treeP_lookup t p.
  Proof.
    revert p.
    induction t; intros; simpl; [reflexivity|].
    repeat rewrite assoc_app.
    destruct p; simpl;
      repeat ((rewrite assoc_nomap by discriminate)
              + rewrite assoc_map by
               (intros ? ? HX; inversion HX; subst; reflexivity)).
    all: destruct ov; try apply IHt2; try rewrite IHt1; simpl; try tauto.
    all: destruct treeP_lookup; reflexivity.
  Qed.

  Definition treeN : Type := option V * treeP.

  Definition treeN_nil : treeN := (None,TPNil).

  Definition treeN_lookup t n :=
    match n with
    | N0 => fst t
    | Npos p => treeP_lookup (snd t) p
    end.

  Definition treeN_update t n ov :=
    match n with
    | N0 => (ov,snd t)
    | Npos p => (fst t,treeP_update (snd t) p ov)
    end.

  Definition treeN_alist t :=
    match fst t with None => nil | Some v => (0,v)::nil end
      ++ map (fun kv => (Npos (fst kv),snd kv)) (treeP_alist (snd t)).

  Theorem treeN_lookup_update t n1 n2 ov :
    treeN_lookup (treeN_update t n1 ov) n2 =
      if N.eqb n1 n2 then ov else treeN_lookup t n2.
  Proof.
    destruct n1,n2; simpl; apply treeP_lookup_update + reflexivity.
  Qed.

  Theorem treeN_update_updated t p ov :
    treeN_lookup (treeN_update t p ov) p = ov.
  Proof.
    rewrite treeN_lookup_update,N.eqb_refl.
    reflexivity.
  Qed.

  Theorem treeN_update_frame t n1 n2 ov (HNEq : n1 <> n2) :
    treeN_lookup (treeN_update t n1 ov) n2 = treeN_lookup t n2.
  Proof.
    apply N.eqb_neq in HNEq.
    rewrite treeN_lookup_update,HNEq.
    reflexivity.
  Qed.

  Theorem treeN_alist_assoc t p :
    assoc p (treeN_alist t) = treeN_lookup t p.
  Proof.
    unfold treeN_alist,treeN_lookup.
    rewrite assoc_app.
    destruct p,t as [o ?]; simpl.
    {
      rewrite assoc_nomap by discriminate.
      destruct o; reflexivity.
    }
    {
      rewrite assoc_map by (intros ? ? HX; inversion HX; reflexivity).
      rewrite treeP_alist_assoc.
      destruct o; reflexivity.
    }
  Qed.
End treePN.

Arguments TPNil {_}.
Arguments TPBranch {_}.
Arguments treeP_lookup {_}.
Arguments treeP_update {_}.
Arguments treeN_nil {_}.
Arguments treeN_lookup {_}.
Arguments treeN_update {_}.

Definition nset := treeN unit.
Definition nset_cons x xs := treeN_update xs x (Some tt).
Definition nset_remove x xs : nset := treeN_update xs x None.
Definition nset_contains x xs :=
  match treeN_lookup xs x with None => false | Some tt => true end.
