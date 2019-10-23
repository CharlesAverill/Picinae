Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Wf.

Set Nested Proofs Allowed.

Inductive ListHas {A : Type} (P : A -> Prop) : list A -> nat -> Prop :=
| ListHasNil : ListHas P nil 0
| ListHasNext x xs n : P x -> ListHas P xs n -> ListHas P (cons x xs) (S n)
| ListHasSkip x xs n : not (P x) -> ListHas P xs n -> ListHas P (cons x xs) n.

(* Inductive ListMember {A : Type} : A -> list A -> Prop := *)
(* | ListMemFirst e l' : ListMember e (cons e l') *)
(* | ListMemRest e e' l' : ListMember e l' -> ListMember e (cons e' l'). *)

(* Theorem nilempty {A : Type} (x : A) : not (ListMember x nil). *)
(*   unfold not. *)
(*   intros. *)
(*   inversion H. *)
(* Qed. *)

Record IndexImpl {K : Type} {A : Type -> Type} : Type :=
  make_indeximpl {
      indeximplkeys {V} : A V -> list K;
      indeximplsetopt {V} : A V -> K -> option V -> A V;
      indeximplget {V} : A V -> K -> option V;
      indeximplempty {V} : A V;
      (* indeximplfoldhas a k v : *)
      (*   ListMember (pair k v) (indeximplkeys a) -> *)
      (*   indeximplget a k = v; *)
      indeximplemptyspec {V} k :
        indeximplget (indeximplempty : A V) k = None;
      indeximplsetoptget {V} (a : A V) k v :
        indeximplget (indeximplsetopt a k v) k = v;
      indeximplsetoptirrel {V} (a : A V) k1 k2 v :
        k1 <> k2 -> indeximplget (indeximplsetopt a k2 v) k1 = indeximplget a k1;
      indeximplkeysspec {V} (a : A V) k :
        match indeximplget a k with
        | None => ListHas (eq k) (indeximplkeys a) 0
        | Some v => ListHas (eq k) (indeximplkeys a) 1
        end
    }.

Arguments IndexImpl : clear implicits.

Theorem indeximplkeysspechas {K A V} (I : IndexImpl K A) (a : A V) (k : K) v :
  indeximplget I a k = Some v -> ListHas (eq k) (indeximplkeys I a) 1.
  intros.
  eassert (HK := indeximplkeysspec _ _ _).
  rewrite H in HK.
  assumption.
Qed.

Theorem indeximplkeysspecnone {K A V} (I : IndexImpl K A) (a : A V) (k : K) :
  indeximplget I a k = None -> ListHas (eq k) (indeximplkeys I a) 0.
  intros.
  eassert (HK := indeximplkeysspec _ _ _).
  rewrite H in HK.
  assumption.
Qed.

(* Definition indeximplalist {K V A} (I : IndexImpl K A) a : list (K*V) := *)
(*   map (fun k => pair k (indeximplget I a k)) (indeximplkeys I a). *)
(*   ListHas (k,v) *)

(* Theorem indeximplalistspec {K V A} (I : IndexImpl K A) a k (v : V) : *)
(*   ListHas (eq (k,v)) (indeximplkeys I a) 1 <-> indeximplget I a k = Some v. *)

Class EqDec (A : Type) := { iseq (x y : A) : {x=y}+{x<>y} }.

Fixpoint listmem {A} (f : A -> bool) (l : list A) : option A :=
  match l with
  | nil => None
  | cons x xs => if f x then Some x else listmem f xs
  end.

Definition iseqb {A : Type} {_ : EqDec A} x y :=
  if iseq x y then true else false.

(* Theorem listmemberdest {A} (e x : A) xs : *)
(*   ListMember e (cons x xs) <-> e = x \/ ListMember e xs. *)
(*   split; intros; [inversion H; auto|]. *)
(*   destruct H as [[]|]; constructor. *)
(*   assumption. *)
(* Qed. *)

(* Theorem listnonmemdest {A} (e x : A) xs : *)
(*   not (ListMember e (cons x xs)) <-> e <> x /\ not (ListMember e xs). *)
(*   rewrite listmemberdest. *)
(*   tauto. *)
(* Qed. *)

Definition alistremove {K V} {eqd : EqDec K} k (l : list (K*V)) :=
  filter (fun kv => negb (iseqb k (fst kv))) l.

Fixpoint alistsimplify {K V} {eqd : EqDec K} (l : list (K*V)) :=
  match l with
  | cons x xs => cons x (alistremove (fst x) (alistsimplify xs))
  | nil => nil
  end.

Fixpoint listuniq {A} {eqd : EqDec A} (l : list A) :=
  match l with
  | cons x xs => cons x (filter (fun x' => negb (iseqb x x')) (listuniq xs))
  | nil => nil
  end.

(* Theorem filtermem {A} f l (a : A) : *)
(*   ListMember a (filter f l) <-> f a = true /\ ListMember a l. *)
(*   induction l; simpl; [split;[intro H; inversion H|tauto]|]. *)
(*   destruct (f a0) eqn:FA; repeat rewrite listmemberdest; rewrite IHl; *)
(*     intuition; subst; auto. *)
(*   rewrite FA in *. *)
(*   discriminate. *)
(* Qed. *)

(* Theorem alistremmem {K V} {_ : EqDec K} (a : list (K*V)) k v : *)
(*   not (ListMember (pair k v) (alistremove k a)). *)
(*   unfold alistremove,iseqb. *)
(*   rewrite filtermem. *)
(*   intuition. *)
(*   destruct iseq; auto. *)
(*   discriminate. *)
(* Qed. *)

Theorem listhasnone {A} P n :
  not (ListHas (A := A) P nil (S n)).
  unfold not.
  intros.
  inversion H.
Qed.

Theorem listhasdest {A} P x xs n :
  ListHas (A := A) P (cons x xs) n <->
  match n with
  | S n' => P x /\ ListHas P xs n' \/ ~P x /\ ListHas P xs (S n')
  | 0 => ~P x /\ ListHas P xs 0
  end.
  destruct n; (split; intro H; [inversion H; auto|]).
  {
    destruct H.
    apply ListHasSkip; assumption.
  }
  {
    destruct H as [[H1 H2]|[H1 H2]];
      [apply ListHasNext|apply ListHasSkip]; assumption.
  }
Qed.

Theorem listhasdests {A} P x xs n :
  ListHas (A := A) P (cons x xs) (S n) <->
  (P x /\ ListHas P xs n) \/ (~P x /\ ListHas P xs (S n)).
  rewrite listhasdest.
  reflexivity.
Qed.

Theorem listhasdest0 {A} P x xs :
  ListHas (A := A) P (cons x xs) 0 <->
  (~P x /\ ListHas P xs 0).
  rewrite listhasdest.
  reflexivity.
Qed.

Theorem listhasfilterrem {A} (P : A -> Prop) f (l : list A) :
  (forall x, P x -> f x = false) -> ListHas P (filter f l) 0.
  induction l; [constructor|].
  simpl.
  intros H.
  destruct f eqn:HF; auto.
  constructor; auto.
  intro.
  rewrite H in HF by assumption.
  discriminate.
Qed.

Theorem listhasfilterkeep {A} (P : A -> Prop) f (l : list A) n :
  (forall x, P x -> f x = true) ->
  ListHas P (filter f l) n <-> ListHas P l n.
  generalize dependent n.
  induction l; [reflexivity|].
  intros n H.
  simpl.
  destruct f eqn:FA; repeat rewrite listhasdest;
    [destruct n; repeat rewrite IHl by assumption; reflexivity|].
  rewrite IHl by assumption.
  assert (~P a).
  {
    unfold not.
    intros.
    rewrite H in FA by assumption.
    discriminate.
  }
  destruct n; tauto.
Qed.

Theorem listhasuniq {A} P l n1 n2:
  n1 <> n2 -> ListHas (A := A) P l n1 -> ListHas P l n2 -> False.
  generalize dependent n2.
  generalize dependent n1.
  induction l; intros n1 n2 H1 H2 H3;
    [inversion H2;inversion H3;subst;auto|].
  inversion H2; inversion H3; subst; eauto.
Qed.

Theorem listhasapp {A} (P : A -> Prop) l1 l2 n1 n2 :
  ListHas P l1 n1 /\ ListHas P l2 n2 -> ListHas P (l1 ++ l2) (n1 + n2).
  intro H.
  destruct H as [H1 H2].
  generalize dependent n1.
  induction l1; intros; [inversion H1|]; auto.
  simpl.
  inversion H1; subst; [apply ListHasNext|apply ListHasSkip]; auto.
Qed.

Theorem listhasmap {A B} (P : B -> Prop) (f : A -> B) l n :
  ListHas P (map f l) n <-> ListHas (fun x => P (f x)) l n.
  generalize dependent n.
  induction l; simpl; intro n;
    [split; intro H; inversion H; subst; constructor|].
  repeat rewrite listhasdest.
  destruct n; repeat rewrite IHl; reflexivity.
Qed.

Theorem listhasnever {A} (P : A -> Prop) l :
  (forall x, ~ P x) -> ListHas P l 0.
  induction l; constructor; auto.
Qed.

Theorem listhasiff {A} (P Q : A -> Prop) l n :
  (forall x, P x <-> Q x) -> ListHas P l n <-> ListHas Q l n.
  intro H.
  generalize dependent n.
  induction l; intro n;
    [split; intro LH; inversion LH; subst; constructor|].
  repeat rewrite listhasdest.
  destruct n; repeat rewrite H; repeat rewrite IHl; reflexivity.
Qed.

Program Definition IndexAlistOptImpl (K : Type) {_ : EqDec K} :
  IndexImpl K (fun V => list (K*V)) :=
  make_indeximpl
    K (fun V => list (K*V))
    (fun V a => listuniq (map fst a))
    (fun V a k v =>
       let rm := filter (fun kv => negb (iseqb k (fst kv))) a in
       match v with
       | None => rm
       | Some x => cons (pair k x) rm
       end)
    (fun V a k =>
       option_map snd (listmem (fun kv => iseqb k (fst kv)) a))
    (fun V => nil)
    _ _ _ _.
Next Obligation.
  unfold iseqb.
  destruct v; simpl; [destruct iseq;[reflexivity|tauto]|].
  induction a; auto.
  simpl.
  destruct a,iseq; auto; simpl in *.
  destruct iseq; auto.
  tauto.
Qed.
Next Obligation.
  unfold iseqb.
  destruct v; simpl.
  {
    destruct iseq; [tauto|].
    simpl.
    induction a; auto.
    destruct a.
    simpl in *.
    destruct iseq; subst; simpl in *; destruct iseq; subst; simpl in *; auto.
    tauto.
  }
  {
    induction a; auto.
    destruct a.
    simpl.
    destruct iseq; subst; simpl; destruct iseq; subst; simpl; auto.
    tauto.
  }
Qed.
Next Obligation.
  induction a; [constructor|].
  simpl.
  unfold iseqb.
  destruct iseq; simpl in *; subst.
  {
    rewrite listhasdest.
    left.
    split; [reflexivity|].
    apply listhasfilterrem.
    intros; subst.
    destruct iseq; tauto.
  }
  {
    destruct option_map; rewrite listhasdest; [right|]; split;
      auto; rewrite listhasfilterkeep; auto; intros; subst;
        destruct iseq; auto.
  }
Qed.

Program Definition IndexKeyIsoImpl
        {K1 K2 : Type} {A}
        (k1tok2 : K1 -> K2)
        (k2tok1 : K2 -> K1)
        (I : IndexImpl K2 A)
        (H1 : forall k, (k2tok1 (k1tok2 k)) = k)
        (H2 : forall k, (k1tok2 (k2tok1 k)) = k)
  : IndexImpl K1 A :=
  make_indeximpl
    K1 A
    (fun V a => map k2tok1 (indeximplkeys I a))
    (fun V a k v => indeximplsetopt I a (k1tok2 k) v)
    (fun V a k => indeximplget I a (k1tok2 k))
    (fun V => indeximplempty I)
    _ _ _ _.
Next Obligation.
  destruct I; auto.
Qed.
Next Obligation.
  destruct I; auto.
Qed.
Next Obligation.
  apply indeximplsetoptirrel.
  unfold not in *.
  intro HK.
  apply H.
  rewrite <- H1.
  rewrite <- HK.
  auto.
Qed.
Next Obligation.
  assert (S := indeximplkeysspec I a (k1tok2 k)).
  induction indeximplkeys; simpl in *;
    [destruct indeximplget;[inversion S|constructor]|].
  destruct indeximplget; rewrite listhasdest in S; rewrite listhasdest.
  {
    destruct S as [[? S]|[? S]]; subst.
    {
      left.
      intuition.
      clear IHl.
      induction l; simpl; auto; [constructor|].
      rewrite listhasdest.
      rewrite listhasdest in S.
      intuition.
      subst.
      auto.
    }
    {
      right.
      intuition.
      subst.
      auto.
    }
  }
  {
    intuition.
    subst.
    auto.
  }
Qed.

Inductive PosTree {A} : Type :=
| PosTreeNil : PosTree
| PosTreeBranch : option A -> PosTree -> PosTree -> PosTree.

Arguments PosTree : clear implicits.

Fixpoint postreeempty {A} (t : PosTree A) :=
  match t with
  | PosTreeBranch (Some _) _ _ => false
  | PosTreeBranch None t1 t2 => andb (postreeempty t1) (postreeempty t2)
  | PosTreeNil => true
  end.

Fixpoint postreeminimal {A} (t : PosTree A) :=
  match t with
  | PosTreeBranch None PosTreeNil PosTreeNil => false
  | PosTreeBranch _ t1 t2 => andb (postreeminimal t1) (postreeminimal t2)
  | PosTreeNil => true
  end.

Fixpoint postreeminimize {A} (t : PosTree A) :=
  match t with
  | PosTreeBranch o t1 t2 =>
    let t1' := postreeminimize t1 in
    let t2' := postreeminimize t2 in
    match o,t1',t2' with
    | None,PosTreeNil,PosTreeNil => PosTreeNil
    | _,_,_ => PosTreeBranch o t1' t2'
    end
  | PosTreeNil => PosTreeNil
  end.

Theorem postreeminimizespec {A} (t : PosTree A) :
  postreeminimal (postreeminimize t) = true.
  induction t; [reflexivity|].
  simpl.
  destruct o; simpl; [rewrite IHt1;exact IHt2|].
  repeat destruct postreeminimize; auto; simpl in *; rewrite IHt1; auto.
Qed.

Require Import NArith.

Fixpoint postreeget {A} t k : option A :=
  match t with
  | PosTreeNil => None
  | PosTreeBranch tv t1 t2 =>
    match k with
    | xH => tv
    | xO p => postreeget t1 p
    | xI p => postreeget t2 p
    end
  end.

Theorem postreegetmini {A} (t : PosTree A) k :
  postreeget (postreeminimize t) k = postreeget t k.
  generalize dependent k.
  induction t; [reflexivity|]; intros.
  destruct o; [destruct k;simpl;auto|].
  simpl.
  destruct k; [rewrite <- IHt2|rewrite <- IHt1|];
    repeat destruct postreeminimize; reflexivity.
Qed.

Fixpoint postreesetopt {A} t k ov : PosTree A :=
  match t,ov with
  | PosTreeNil,None => PosTreeNil
  | _,_ =>
    match (match t with
           | PosTreeBranch tv t1 t2 => (tv,t1,t2)
           | PosTreeNil => (None,PosTreeNil,PosTreeNil)
           end) with
    | (tv,t1,t2) =>
      match k with
      | xH => PosTreeBranch ov t1 t2
      | xO p => PosTreeBranch tv (postreesetopt t1 p ov) t2
      | xI p => PosTreeBranch tv t1 (postreesetopt t2 p ov)
      end
    end
  end.

Fixpoint postreekeys {A} (t : PosTree A) :=
  match t with
  | PosTreeNil => nil
  | PosTreeBranch o t1 t2 =>
    let l := app (map xO (postreekeys t1)) (map xI (postreekeys t2)) in
    match o with
    | Some _ => cons xH l
    | None => l
    end
  end.

Program Definition IndexPosTreeImpl (* : IndexImpl positive PosTree *) :=
  make_indeximpl
    positive PosTree
    (fun V => postreekeys)
    (fun V t k ov => postreeminimize (postreesetopt t k ov))
    (fun V => postreeget)
    (fun V => PosTreeNil (A := V))
    _ _ _ _.
Next Obligation.
  rewrite postreegetmini.
  generalize dependent a.
  induction k; intro a; destruct a,v; simpl; auto.
Qed.
Next Obligation.
  rewrite postreegetmini.
  generalize dependent k2.
  generalize dependent a.
  induction k1; intros a k2 H; destruct a,k2,v; simpl; tauto + auto;
    apply IHk1; intuition; subst; tauto.
Qed.
Next Obligation.
  generalize dependent k.
  induction a; [constructor|].
  intro k; destruct k.
  3: {
    destruct o; [constructor; auto|]; fold (0+0);
    apply listhasapp; repeat rewrite listhasmap; split;
    apply listhasnever; discriminate.
  }
  all: simpl.
  1: assert (IH := IHa2 k); fold (0+1).
  2: assert (IH := IHa1 k); fold (1+0).
  all: fold (0+0).
  all: destruct postreeget.
  all: destruct o; [constructor;[discriminate|]|].
  all: apply listhasapp.
  all: repeat rewrite listhasmap.
  all: simpl.
  all: split; try (apply listhasnever;discriminate).
  all: rewrite (listhasiff _ (eq k)); auto.
  all: split; intro H; subst; auto.
  all: inversion H.
  all: reflexivity.
Qed.

(* Definition indeximplfold {K V : Type} {A R} (I : IndexImpl K A) kons (knil : R) a := *)
(*   fold_right (fun (kv : (K*V)) => let (k,v) := kv in kons k v) *)
(*              knil *)
(*              (indeximplalist I a (V := V)). *)

Definition indeximplupdate {K V A} (I : IndexImpl K A) f a k :=
  indeximplsetopt I a k (f (indeximplget I a k (V := V))).

Definition optdefault {A} def opt : A :=
  match opt with Some a => a | None => def end.

Theorem paireqdest {A B} a b c d :
  ((a,c) : A*B) = (b,d) <-> a = b /\ c = d.
  split; intro H; inversion H; subst; auto.
Qed.

(* Theorem indeximplemptymem {K V A} (I : IndexImpl K A) a k : *)
(*   indeximplalist I a (V := V) = nil -> indeximplget I a k = None. *)
(*   intro H. *)
(*   destruct indeximplget eqn:HG; auto. *)
(*   rewrite <- indeximplalistspec in HG. *)
(*   rewrite H in *. *)
(*   inversion HG. *)
(* Qed. *)

Inductive ListTail {A} : list A -> list A -> Prop :=
| ListTailSelf l : ListTail l l
| ListTailCdr t x xs : ListTail t xs -> ListTail t (cons x xs).

Program Definition IndexProdImpl
        {K1 K2 : Set} {_ : EqDec K1} {A1 A2}
        (I1 : IndexImpl K1 A1)
        (I2 : IndexImpl K2 A2)
        (EMPTY : forall {V} a,
            {indeximplkeys I2 a = nil}+{indeximplkeys I2 a <> nil})
  : IndexImpl (K1*K2) (fun V => A1 (A2 V)) :=
  make_indeximpl
    _ _
    (fun V a1 =>
       fold_right (app (A := K1*K2))
                  nil
                  (map (fun k =>
                          match indeximplget I1 a1 k with
                          | Some a2 => map (pair k) (indeximplkeys I2 a2)
                          | None => nil
                          end)
                       (indeximplkeys I1 a1)))
       (* fold_right (fun k1 a1 knil => app (map (pair k1) (indeximplfold I2  *)
       (* indeximplfold *)
       (*   I1 *)
       (*   (fun k1a1 knil => *)
       (*      (indeximplfold *)
       (*         I2 *)
       (*         (fun k2v => cons (pair (pair (fst k1a1) (fst k2v)) (snd k2v))) *)
       (*         knil *)
       (*         (snd k1a1))) *)
       (*   nil) *)
    (* (fun V => *)
    (*    indeximplfold *)
    (*      I1 *)
    (*      (fun k1a1 knil => *)
    (*         (indeximplfold *)
    (*            I2 *)
    (*            (fun k2v => cons (pair (pair (fst k1a1) (fst k2v)) (snd k2v))) *)
    (*            knil *)
    (*            (snd k1a1))) *)
    (*      nil) *)
    (fun V a k v =>
       indeximplupdate
         I1 (fun oa2 =>
               let a2 :=
                   indeximplupdate
                     I2
                     (fun _ => v)
                     (optdefault (indeximplempty I2) oa2)
                     (snd k) in
               if EMPTY a2 then None else Some a2)
         a
         (fst k))
    (fun V a k =>
       optdefault None
                  (option_map (fun a2 => indeximplget I2 a2 (snd k))
                              (indeximplget I1 a (fst k))))
    (fun V => indeximplempty I1)
    _ _ _ _.
Next Obligation.
  rewrite indeximplemptyspec.
  reflexivity.
Qed.
Next Obligation.
  unfold indeximplupdate.
  rewrite indeximplsetoptget.
  unfold optdefault.
  destruct EMPTY; simpl in *; [|rewrite indeximplsetoptget;reflexivity].
  destruct v; [|reflexivity].
  exfalso.
  epose (HK := indeximplkeysspec I2 (V := V) _ k0).
  rewrite e in HK.
  rewrite indeximplsetoptget in HK.
  inversion HK.
Qed.
Next Obligation.
  simpl.
  simpl.
  unfold indeximplupdate.
  simpl.
  destruct (iseq k1 k); subst;
    [|rewrite indeximplsetoptirrel by assumption; reflexivity].
  assert (k2 <> k0); [intro; subst; auto|].
  unfold optdefault.
  rewrite indeximplsetoptget.
  destruct (indeximplget I1) eqn:HG1; simpl; auto.
  {
    destruct EMPTY; simpl; [|apply indeximplsetoptirrel; assumption].
    symmetry.
    destruct (indeximplget I2 a0 k2) eqn:HG2; try reflexivity.
    erewrite <- indeximplsetoptirrel in HG2 by eassumption.
    apply indeximplkeysspechas in HG2.
    rewrite e in HG2.
    inversion HG2.
  }
  {
    destruct EMPTY; auto.
    simpl.
    rewrite indeximplsetoptirrel by assumption.
    rewrite indeximplemptyspec.
    reflexivity.
  }
Qed.
Next Obligation.
  destruct indeximplget eqn:HG1; simpl in *.
  {
    assert (HG1' := HG1).
    apply indeximplkeysspechas in HG1.
    destruct (indeximplget I2) eqn:HG2; simpl in *.
    {
      apply indeximplkeysspechas in HG2.
      induction indeximplkeys; [inversion HG1|]; simpl in *.
      inversion HG1; subst.
      2: {
        apply IHl in H4.
        eapply (listhasapp _ _ _ 0).
        split; auto.
        destruct (indeximplget I1 a a1); [|constructor].
        rewrite listhasmap.
        apply listhasnever.
        intros x F.
        inversion F; subst.
        auto.
      }
      {
        rewrite HG1'.
        eapply (listhasapp _ _ _ 1 0).
        clear IHl.
        rewrite listhasmap.
        split.
        {
          erewrite listhasiff; [apply HG2|].
          intros.
          split; intro HX; subst; auto.
          inversion HX.
          reflexivity.
        }
        {
          clear HG1 HG1'.
          induction l; [constructor|].
          simpl.
          eapply (listhasapp _ _ _ 0 0).
          rewrite listhasdest in H4.
          destruct H4.
          split; auto.
          destruct indeximplget; [|constructor].
          rewrite listhasmap.
          apply listhasnever.
          intros x HX.
          inversion HX; auto.
        }
      }
    }
    {
      induction indeximplkeys; [constructor|].
      simpl.
      rewrite listhasdest in HG1.
      eapply (listhasapp _ _ _ 0 0).
      destruct HG1 as [[HEQ HGK]|[HNE HGK]]; subst.
      {
        rewrite HG1'.
        split.
        {
          rewrite listhasmap.
          apply indeximplkeysspecnone in HG2.
          rewrite listhasiff; eauto.
          split; intro; subst; auto.
          inversion H0; auto.
        }
        {
          clear IHl.
          induction l; [constructor|].
          simpl.
          rewrite listhasdest in HGK.
          destruct HGK as [HGK1 HGK2].
          eapply (listhasapp _ _ _ 0 0).
          split; auto.
          destruct (indeximplget I1 a a2); [|constructor].
          apply listhasmap.
          apply listhasnever.
          intros x HX; inversion HX; subst; auto.
        }
      }
      {
        split; auto.
        destruct (indeximplget I1 a a1); [|constructor].
        apply listhasmap.
        apply listhasnever.
        intros x HX.
        inversion HX.
        auto.
      }
    }
  }
  {
    apply indeximplkeysspecnone in HG1.
    induction indeximplkeys; [constructor|].
    rewrite listhasdest in HG1.
    destruct HG1.
    simpl.
    eapply (listhasapp _ _ _ 0 0).
    split; auto.
    destruct (indeximplget I1 a a0); [|constructor].
    apply listhasmap.
    apply listhasnever.
    intros x HX.
    inversion HX.
    auto.
  }
Qed.

Record Index {K V} : Type :=
  make_index {
      indextype : Type -> Type;
      indeximpl : IndexImpl K indextype;
      indexobj : indextype V;
    }.

Arguments Index : clear implicits.

Definition indexkeys {K V} (s : Index K V) :=
  indeximplkeys (indeximpl s) (indexobj s).

Definition indexsetopt {K V} (s : Index K V) k v :=
  make_index K V
             (indextype s)
             (indeximpl s)
             (indeximplsetopt (indeximpl s) (indexobj s) k v).

Definition indexget {K V} (s : Index K V) :=
  indeximplget (indeximpl s) (indexobj s).

Definition indexempty {K V1} (s : Index K V1) {V2} :=
  make_index K V2
             (indextype s)
             (indeximpl s)
             (indeximplempty (indeximpl s)).

Theorem indexemptyspec {K V1 V2} (s : Index K V1) k :
  indexget (indexempty s : Index K V2) k = None.
  apply indeximplemptyspec.
Qed.
Theorem indexsetoptget {K V} (s : Index K V) k v :
  indexget (indexsetopt s k v) k = v.
  apply indeximplsetoptget.
Qed.
Theorem indexsetoptirrel {K V} (s : Index K V) k1 k2 v :
  k1 <> k2 ->
  indexget (indexsetopt s k2 v) k1 = indexget s k1.
  apply indeximplsetoptirrel.
Qed.
Theorem indexkeysspec {K V} (s : Index K V) k :
  match (indexget s k) with
  | Some v => ListHas (eq k) (indexkeys s) 1
  | None => ListHas (eq k) (indexkeys s) 0
  end.
  apply indeximplkeysspec.
Qed.


Theorem indexkeysspechas {K V} (i : Index K V) (k : K) v :
  indexget i k = Some v -> ListHas (eq k) (indexkeys i) 1.
  apply indeximplkeysspechas.
Qed.

Theorem indexkeysspecnone {K V} (i : Index K V) (k : K) :
  indexget i k = None <-> ListHas (eq k) (indexkeys i) 0.
  split; [apply indeximplkeysspecnone|].
  intros.
  destruct indexget eqn:HG; auto.
  apply indexkeysspechas in HG.
  exfalso.
  eapply (listhasuniq _ _ 0 1); eauto.
Qed.

Theorem indexkeysspechas' {K V} (i : Index K V) (k : K) :
  (exists v, indexget i k = Some v) <-> ListHas (eq k) (indexkeys i) 1.
  split; intro H; [destruct H; eapply indexkeysspechas; eauto|].
  destruct indexget eqn:HG; [econstructor; reflexivity|].
  exfalso.
  rewrite indexkeysspecnone in HG.
  eapply (listhasuniq _ _ 0 1); eauto.
Qed.

Definition indexsmallereq {K V} (i1 i2 : Index K V) : Prop :=
  forall k, ListHas (eq k) (indexkeys i1) 1 -> ListHas (eq k) (indexkeys i2) 1.

Definition indexsmaller {K V} (i1 i2 : Index K V) : Prop :=
  indexsmallereq i1 i2 /\
  exists k, ListHas (eq k) (indexkeys i1) 0 /\ ListHas (eq k) (indexkeys i2) 1.

Definition indexremovesmallereq {K V} (i : Index K V) k :
  indexsmallereq (indexsetopt i k None) i.
  unfold indexsmallereq.
  intros k2 H.
  rewrite <- indexkeysspechas' in H.
  destruct H.
  rewrite indexsetoptirrel in H by
      (intro; subst; rewrite indexsetoptget in H; discriminate).
  rewrite <- indexkeysspechas'.
  econstructor.
  eassumption.
Qed.

Theorem indexremovesmaller {K V} (i : Index K V) k v :
  indexget i k = Some v -> indexsmaller (indexsetopt i k None) i.
  unfold indexsmaller.
  split; [apply indexremovesmallereq|].
  exists k.
  rewrite <- indexkeysspechas',<- indexkeysspecnone,indexsetoptget,H.
  split; [|econstructor]; auto.
Qed.

Definition issome {A} (o : option A) :=
  if o then true else false.

Theorem filterleq {A} f (l : list A) :
  length (filter f l) <= length l.
  induction l; auto.
  simpl.
  destruct f; auto.
  simpl.
  apply le_n_S.
  assumption.
Qed.
(* Definition issome {A} (o : option A) := *)
(*   match o with Some _ => true | None => false end. *)

Definition ListAll {A} (P : A -> Prop) l : Prop :=
  ListHas P l (length l).

Theorem listhasmax {A} (P : A -> Prop) l n : ListHas P l n -> n <= length l.
  generalize dependent n.
  induction l; intros n H; [inversion H; auto|].
  simpl.
  inversion H; subst; auto using le_n_S.
Qed.

Require Import PeanoNat.

Theorem listalldest {A} (P : A -> Prop) x xs :
  ListAll P (cons x xs) <-> P x /\ ListAll P xs.
  unfold ListAll.
  rewrite listhasdest.
  simpl.
  split; auto.
  intro H.
  destruct H; auto.
  exfalso.
  destruct H as [_ H].
  apply listhasmax in H.
  generalize dependent (length xs).
  intros.
  eapply Nat.nle_succ_diag_l.
  eassumption.
Qed.

Definition ListUnique {A} l : Prop :=
  forall (a : A) n, ListHas (eq a) l n -> n = 0 \/ n = 1.

Fixpoint listhascount {A} (f : A -> bool) l : nat :=
  match l with
  | nil => 0
  | cons x xs =>
    if f x
    then S (listhascount f xs)
    else listhascount f xs
  end.

Theorem listhasdec {A P} (PDEC : forall (x : A), {P x} + {~P x}) l :
  ListHas P l (listhascount (fun x => if PDEC x then true else false) l).
  induction l; simpl; [constructor|].
  rewrite listhasdest.
  destruct PDEC; auto.
  destruct listhascount; auto.
Qed.

(* Program Fixpoint listhasdec' {A P} (PDEC : forall (x : A), {P x} + {~P x}) l : *)
(*   {n | ListHas P l n} := *)
(*   match l with *)
(*   | nil => exist _ 0 _ *)
(*   | cons x xs => *)
(*     match listhasdec' PDEC xs with *)
(*     | n => *)
(*       match PDEC x with *)
(*       | left HP => exist _ (S n) _ *)
(*       | right NHP => exist _ n _ *)
(*       end *)
(*     end *)
(*   end. *)
(* Next Obligation. *)
(*   constructor. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; auto. *)
(* Qed. *)

(* Program Fixpoint listhasdec' {A P} (PDEC : forall (x : A), {P x} + {~P x}) l : *)
(*   {n | ListHas P l n} := *)
(*   match l with *)
(*   | nil => exist _ 0 _ *)
(*   | cons x xs => *)
(*     match listhasdec' PDEC xs with *)
(*     | n => *)
(*       match PDEC x with *)
(*       | left HP => exist _ (S n) _ *)
(*       | right NHP => exist _ n _ *)
(*       end *)
(*     end *)
(*   end. *)
(* Next Obligation. *)
(*   constructor. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; auto. *)
(* Qed. *)

(* Theorem indexkeys *)

Theorem indexsetemptykey {K V1 V2} (i : Index K V1) k (v : V2) :
  indexkeys (indexsetopt (indexempty i) k (Some v)) = cons k nil.
  pose (ie := indexsetopt (indexempty i) k (Some v)).
  assert (HG : indexget ie k = Some v); [apply indexsetoptget|].
  apply indexkeysspechas in HG.
  assert (HG2 : forall k2, k <> k2 -> ListHas (eq k2) (indexkeys ie) 0);
    [intros; unfold ie; apply indexkeysspecnone;
     rewrite indexsetoptirrel by auto; apply indexemptyspec|].
  destruct indexkeys eqn:HK; [inversion HG|].
  rewrite listhasdest in HG.
  destruct HG as [[HE LH]|[HNE LH]].
  {
    subst.
    destruct l; auto.
    exfalso.
    repeat rewrite listhasdest in LH.
    specialize (HG2 k).
    repeat rewrite listhasdest in HG2.
    tauto.
  }
  {
    exfalso.
    specialize (HG2 k0 HNE).
    inversion HG2; auto.
  }
Qed.

Program Definition indexeq {K V} (i : Index K V) k1 k2 : {k1=k2}+{k1<>k2} :=
  let e := indexempty i in
  match indexget (indexsetopt e k1 (Some tt)) k2 with
  | Some tt => left _
  | None => right _
  end.
Next Obligation.
  apply eq_sym in Heq_anonymous.
  apply indexkeysspechas in Heq_anonymous.
  rewrite indexsetemptykey in Heq_anonymous.
  inversion Heq_anonymous; auto.
  subst.
  inversion H3.
Qed.
Next Obligation.
  apply eq_sym in Heq_anonymous.
  apply indexkeysspecnone in Heq_anonymous.
  rewrite indexsetemptykey in Heq_anonymous.
  inversion Heq_anonymous.
  auto.
Qed.

Instance indexeqd {K V} (i : Index K V) : EqDec K :=
  { iseq := indexeq i }.

Definition listuniquedest {A} {eqd : EqDec A} (x : A) xs :
  ListUnique (cons x xs) <-> ListHas (eq x) xs 0 /\ ListUnique xs.
  assert (LU : forall l, ListUnique (A := A) l <->
                         forall x, ListHas (eq x) l 0 \/ ListHas (eq x) l 1).
  {
    intro l.
    unfold ListUnique.
    split; intros.
    {
      assert (LH := listhasdec (iseq x0) l).
      specialize (H _ _ LH).
      destruct H; rewrite H in *; auto.
    }
    do 2 (destruct n; auto).
    specialize (H a).
    exfalso.
    destruct H; (eapply listhasuniq; [|apply H|apply H0]); auto.
  }
  repeat rewrite LU.
  split; intro H.
  {
    split.
    {
      specialize (H x).
      repeat rewrite listhasdest in H.
      tauto.
    }
    {
      intro x2.
      specialize (H x2).
      repeat rewrite listhasdest in H.
      tauto.
    }
  }
  {
    intros.
    repeat rewrite listhasdest.
    destruct (iseq x0 x); subst; [tauto|].
    destruct H as [H1 H2].
    specialize (H2 x0).
    tauto.
  }
Qed.

Theorem indexkeysuniq {K V} (i : Index K V) : ListUnique (indexkeys i).
  unfold ListUnique.
  intros.
  assert (KS := indexkeysspec i a).
  destruct n; auto.
  destruct n; auto.
  exfalso.
  destruct indexget; (eapply listhasuniq; [|apply H|apply KS]); auto.
Qed.

Definition Permutation {A} l1 l2 :=
  forall P n, ListHas (A := A) P l1 n <-> ListHas P l2 n.

(* Definition Permutation {A} l1 l2 := *)
(*   forall (x : A) n, ListHas (eq x) l1 n <-> ListHas (eq x) l2 n. *)

Theorem indexkeysspec' {K V} (i : Index K V) k n :
  ListHas (eq k) (indexkeys i) n <->
  match n with
  | 0 => indexget i k = None
  | 1 => exists v, indexget i k = Some v
  | _ => False
  end.
  destruct n; [rewrite indexkeysspecnone; reflexivity|].
  destruct n; [rewrite indexkeysspechas'; reflexivity|].
  split; [|tauto].
  intros.
  assert (HS := indexkeysspec i k).
  destruct indexget; (eapply listhasuniq; [|apply H|apply HS]); auto.
Qed.

Theorem listalldest' {A} (P : A -> Prop) l :
  ListAll P l <->
  match l with
  | cons x xs => P x /\ ListAll P xs
  | nil => True
  end.
  unfold ListAll.
  destruct l; [split; auto; constructor|].
  simpl.
  rewrite listhasdest.
  split; auto.
  intros.
  destruct H; auto.
  destruct H.
  exfalso.
  eapply Nat.nle_succ_diag_l, listhasmax.
  eassumption.
Qed.

Theorem listalltrivial {A} (P : A -> Prop) l :
  (forall x, P x) -> ListAll P l.
  intros.
  induction l; rewrite listalldest'; auto.
Qed.

(* Theorem listhastrivial {A} (P : A -> Prop) l : *)
(*   (forall x, P x) -> ListHas P l (length l). *)
(*   apply listalltrivial. *)
(* Qed. *)

Theorem permutelength {A} (l1 l2 : list A) :
  Permutation l1 l2 -> length l1 = length l2.
  unfold Permutation.
  intros.
  specialize (H (fun x => True) (length l1)).
  destruct H as [H1 H2].
  assert (H3 : ListAll (fun x => True) l1); [apply listalltrivial; auto|].
  specialize (H1 H3).
  clear H2 H3.
  generalize dependent (length l1).
  clear l1.
  induction l2; intros n H; inversion H; subst; auto; [|tauto].
  simpl.
  f_equal.
  auto.
Qed.

Definition IndexHas {K V} (P : K -> V -> Prop) (i : Index K V) n :=
  let P' :=
      fun x =>
        match (indexget i x)
        with
        | None => False
        | Some v => P x v
        end in
  ListHas P' (indexkeys i) n.

Theorem indexemptyspec' {K V} (i : Index K V) :
  indexkeys i = nil <-> forall k, indexget i k = None.
  assert (HS := indexkeysspec i).
  split.
  {
    intros.
    specialize (HS k).
    destruct indexget; auto.
    rewrite H in HS.
    inversion HS.
  }
  {
    intros.
    destruct indexkeys eqn:HK; auto.
    specialize (H k).
    specialize (HS k).
    destruct indexget; [discriminate|].
    rewrite listhasdest in HS.
    tauto.
  }
Qed.

Theorem indexsetemptykey' {K V} (i : Index K V) k v :
  indexkeys i = nil -> indexkeys (indexsetopt i k (Some v)) = k :: nil.
  intros.
  eassert (HS1 := indexkeysspechas _ k v).
  erewrite indexsetoptget in HS1.
  specialize (HS1 eq_refl).
  eassert (HS2 := indexkeysspecnone _).
  destruct indexkeys eqn:HK at 1; rewrite HK in *; [inversion HS1|].
  inversion HS1; subst.
  {
    destruct l as [|kn ?]; [reflexivity|].
    inversion H4; subst.
    specialize (HS2 kn).
    rewrite indexsetoptirrel in HS2 by auto.
    exfalso.
    eapply (listhasuniq (eq kn) _ 0 (S _)).
    {
      unfold not.
      intros.
      discriminate.
    }
    {
      rewrite <- HS2.
      apply indexemptyspec'.
      assumption.
    }
    {
      repeat rewrite listhasdest.
      right.
      split; auto.
      left.
      split; auto.
      apply listhasdec.
      Unshelve.
      apply (indexeq i).
    }
  }
  {
    specialize (HS2 k0).
    rewrite indexemptyspec' in H.
    rewrite indexsetoptirrel in HS2; auto.
    destruct HS2 as [HS2 _].
    specialize (HS2 (H _)).
    inversion HS2.
    tauto.
  }
Qed.

Require Import Arith Wf.

Theorem permnil {A} (l : list A) : Permutation nil l -> l = nil.
  destruct l; auto.
  unfold Permutation.
  intro H.
  exfalso.
  eapply (listhasuniq (fun x => True) _ 0 (S _));
    [discriminate|constructor|].
  rewrite H.
  constructor; auto.
  apply listalltrivial.
  auto.
Qed.

Require Import Coq.Relations.Relations.

Theorem permrefl {A} : reflexive (list A) Permutation.
  unfold reflexive,Permutation.
  reflexivity.
Qed.

Theorem permtrans {A} : transitive (list A) Permutation.
  unfold transitive,Permutation.
  intros ? ? ? H0 H1 ? ?.
  rewrite H0,H1.
  reflexivity.
Qed.

Theorem permsym {A} : symmetric (list A) Permutation.
  unfold symmetric,Permutation.
  intros ? ? H ? ?.
  rewrite H.
  reflexivity.
Qed.

Theorem permequiv {A} : equivalence (list A) Permutation.
  unfold Permutation.
  constructor; [apply permrefl|apply permtrans|apply permsym].
Qed.

Theorem listhasfun {A} f (l : list A) :
  ListHas (fun x => f x = true) l (listhascount f l).
  induction l; [constructor|].
  simpl.
  destruct f eqn:HF; constructor; auto.
  rewrite HF.
  discriminate.
Qed.

Theorem listhasfilterconj {A} P f (l : list A) n :
  ListHas P (filter f l) n
  <-> ListHas (fun x => P x /\ f x = true) l n.
  generalize dependent n.
  induction l.
  {
    split; intro H; inversion H; constructor.
  }
  {
    simpl.
    intro.
    rewrite listhasdest.
    destruct f eqn:HF.
    {
      rewrite listhasdest.
      destruct n; repeat rewrite IHl; intuition.
    }
    {
      rewrite IHl.
      destruct n; intuition; discriminate.
    }
  }
Qed.

Theorem listhasneg {A} P (l : list A) n :
  ListHas P l n -> ListHas (fun x => ~ P x) l (length l - n).
  intros.
  generalize dependent n.
  induction l; [constructor|].
  intros.
  assert (HM := (listhasmax _ _ _ H)).
  simpl in HM.
  inversion HM; subst.
  {
    specialize (IHl (length l)).
    rewrite Nat.sub_diag in *.
    inversion H; subst; [constructor;auto|].
    exfalso.
    eapply Nat.nle_succ_diag_l.
    eapply listhasmax.
    eassumption.
  }
  {
    unfold length; fold (length l).
    inversion H; subst; [constructor; simpl; auto|].
    rewrite Nat.sub_succ_l by assumption.
    constructor; auto.
  }
Qed.

Theorem permconssame {A} l1 l2 (x : A) :
  Permutation l1 l2 -> Permutation (cons x l1) (cons x l2).
  unfold Permutation.
  intros.
  repeat rewrite listhasdest.
  destruct n; repeat rewrite H; reflexivity.
Qed.

Theorem listhasapp' {A} P (l1 l2 : list A) n :
  ListHas P (l1 ++ l2) n -> exists m, ListHas P l1 m /\ ListHas P l2 (n-m).
  generalize dependent n.
  induction l1; intros.
  {
    exists 0.
    rewrite Nat.sub_0_r.
    split; [|assumption].
    constructor.
  }
  {
    inversion H; subst; (edestruct IHl1; [eassumption|]).
    {
      exists (S x).
      simpl.
      rewrite listhasdest.
      intuition.
    }
    {
      intuition.
      exists x.
      split; [|assumption].
      constructor; assumption.
    }
  }
Qed.

Theorem listhasapp'' {A} P (l1 l2 : list A) n :
  ListHas P (l1 ++ l2) n
  <-> exists m p, n = m+p /\ ListHas P l1 m /\ ListHas P l2 p.
  split.
  {
    generalize dependent n.
    induction l1; intros n H.
    {
      exists 0,n.
      repeat split; [constructor|assumption].
    }
    {
      inversion H; subst;
        (edestruct IHl1 as [m [p [? [? ?]]]]; [eassumption|]); subst.
      {
        exists (S m),p.
        repeat split; [constructor|]; assumption.
      }
      {
        exists m,p.
        repeat split; [constructor|]; assumption.
      }
    }
  }
  {
    intros.
    destruct H as [m [p [H1 [H2 H3]]]].
    subst.
    induction H2; auto; constructor; auto.
  }
Qed.

Theorem permappcomm {A} (l1 l2 : list A) :
  Permutation (l1 ++ l2) (l2 ++ l1).
  unfold Permutation.
  intros.
  repeat rewrite listhasapp''.
  split; intro H; destruct H as [m [p ?]];
    exists p,m; rewrite Nat.add_comm; tauto.
Qed.

Theorem permfilterapp {A} f (l : list A) :
  Permutation l (filter f l ++ filter (fun x => negb (f x)) l).
  unfold Permutation.
  intros.
  rewrite listhasapp''.
  split.
  {
    intro H.
    induction H; [exists 0,0; repeat constructor| |].
    {
      simpl.
      destruct IHListHas as [m [p [? [H1 H2]]]].
      subst.
      destruct f.
      {
        exists (S m),p.
        rewrite listhasdest.
        tauto.
      }
      {
        exists m,(S p).
        rewrite Nat.add_succ_r.
        simpl.
        rewrite listhasdest.
        tauto.
      }
    }
    {
      destruct IHListHas as [m [p ?]].
      exists m,p.
      simpl.
      destruct f; intuition; apply ListHasSkip; assumption.
    }
  }
  {
    intros.
    destruct H as [m [p [? [H1 H2]]]].
    subst.
    generalize dependent H2.
    generalize dependent H1.
    generalize dependent p.
    generalize dependent m.
    induction l.
    {
      simpl.
      intros.
      inversion H1; assumption.
    }
    {
      simpl.
      intros.
      destruct f; simpl in *; [inversion H1|inversion H2]; subst;
        try rewrite Nat.add_succ_r; constructor; auto.
    }
  }
Qed.

Theorem permfilter {A} f (l1 l2 : list A) :
  Permutation l1 l2 <->
  Permutation (filter (fun x => negb (f x)) l1) (filter (fun x => negb (f x)) l2)
  /\ Permutation (filter f l1) (filter f l2).
  split; intro H.
  {
    unfold Permutation.
    split; intros; repeat rewrite listhasfilterconj; auto.
  }
  {
    destruct H as [HN HP].
    eapply permtrans; [apply (permfilterapp f)|].
    eapply permtrans; [|apply permsym; apply (permfilterapp f)].
    unfold Permutation in *.
    intros.
    repeat rewrite listhasapp''.
    specialize (HN P).
    specialize (HP P).
    split; intro H; destruct H as [m [p H]];
      exists m,p; rewrite HN,HP in *; exact H.
  }
Qed.

(* Theorem permfilter {A} f (l1 l2 : list A) : *)
(*   Permutation l1 l2 <-> *)
(*   ListHas (fun x => f x = false) l2 (listhascount (fun x => negb (f x)) l1) *)
(*   /\ Permutation (filter f l1) (filter f l2). *)

(* Theorem listelmind {A} {_ : EqDec A} P : *)
(*   P nil *)
(*   -> (forall x *)

(* Theorem permeqd {A} {_ : EqDec A} (l1 l2 : list A) : *)
(*   (forall k n, ListHas (eq k) l1 n <-> ListHas (eq k) l2 n) *)
(*   -> Permutation l1 l2. *)
(*   destruct l1. *)
(*   { *)
(*     destruct l2. *)
(*     { *)
(*       unfold Permutation. *)
(*       split; intro HN; inversion HN; constructor. *)
(*     } *)
(*     { *)
(*       intros. *)
(*       specialize (H a 0). *)
(*       destruct H as [H _]. *)
(*       specialize (H (ListHasNil _)). *)
(*       inversion H. *)
(*       tauto. *)
(*     } *)
(*   } *)
(*   { *)
(*     rewrite (permfilter (iseqb a)). *)
(*     intros. *)
(*     split. *)
(*     { *)
(*       simpl. *)
(*       unfold iseqb. *)
(*       destruct iseq; [|tauto]. *)
(*       simpl. *)
(*       destruct H. *)
(*       inversion H. *)
(*   intros. *)
(*   rewrite (permfilter (iseqb . *)
(*   unfold Permutation. *)
(*   intros. *)
(*   rewrite permfilter. *)

(*                  Search sumbool bool. *)
(* Definition indexeqb {K V} (i : Index K V) k1 k2 := *)
(*   match indexeq i k1 k2 with *)
(*   | left _ => true *)
(*   | right _ => false *)
(*   end. *)

(* Theorem indexsetoptperm {K V} (i : Index K V) k v : *)
(*   Permutation (cons k (indexkeys (indexsetopt i k None))) *)
(*               (indexkeys (indexsetopt i k (Some v))). *)
(*   rewrite (permfilter (indexeqb i k)). *)
(*   unfold indexeqb. *)
(*   fold ((cons k nil) ++ (indexkeys (indexsetopt i k None))). *)
(*   split. *)
(*   { *)
(*     simpl. *)
(*     destruct indexeq; [|tauto]. *)
(*     simpl. *)
(*     unfold Permutation. *)
(*     intros. *)
(*     repeat rewrite listhasfilterconj. *)
(*     split. *)
(*     { *)
(*       intros. *)
      
(*   simpl. *)
(*   destruct indexeq; [|tauto]. *)
(*   simpl. *)
(*   rewrite permtrans. *)
(*   Search Permutation filter. *)
(*   repeat rewrite filterapp. *)

(* Theorem indexhasdestn {K V} (P : K -> V -> Prop) (i : Index K V) k v n : *)
(*   P k v -> *)
(*   IndexHas P (indexsetopt i k None) n *)
(*   <-> IndexHas P (indexsetopt i k (Some v)) (S n). *)
(*   unfold IndexHas. *)
(*   rewrite (permfilterapp (indexeqb i k) _ _ n). *)
(*   rewrite (permfilterapp (indexeqb i k) _ _ (S n)). *)
(*   Search ListHas app. *)
(*   Search ListHas filter. *)
(*   unfold indexeqb. *)
(*   repeat rewrite listhasapp''. *)
(*   intro HP. *)
(*   split; intro H; destruct H as [m [p H]]; *)
(*     repeat rewrite listhasfilterconj in H; destruct H as [H1 [H2 H3]]; subst. *)
(*   { *)
(*     exists (S m),p. *)
(*     repeat rewrite listhasfilterconj. *)
(*     split; [reflexivity|]. *)
(*     split. *)
(*     { *)
(*       rewrite (listhasiff _ (eq k)). *)
(*       2: { *)
(*         intros. *)
(*         destruct indexeq; subst; [rewrite indexsetoptget; tauto|]. *)
(*         intuition. *)
(*         discriminate. *)
(*       } *)
(*       replace m with 0. *)
(*       2: { *)
(*         destruct m; auto. *)
(*         exfalso. *)
(*         eapply listhasuniq; [|apply listhasnever|apply H2]; [discriminate|]. *)
(*         unfold not. *)
(*         intros x H. *)
(*         destruct H as [HG HE]. *)
(*         destruct indexeq; [|discriminate]. *)
(*         subst. *)
(*         rewrite indexsetoptget in HG. *)
(*         assumption. *)
(*       } *)
(*       eapply indexkeysspechas,indexsetoptget. *)
(*     } *)
(*     { *)
(*       rewrite (listhasiff _ (fun x => ~(eq k x))). *)
(*       2: { *)
(*         intros. *)
(*         destruct indexeq; intuition. *)
(*         rewrite indexsetoptirrel by auto. *)
(*       appl *)
(*       [|eapply indexkeysspechas]. *)
(*         split; intro H; subst. *)
(*     rewrite listhasnever in H2. *)
(*   repeat rewrite listhasfilterconj. *)
(*   split; intro H. *)
(*   split; intros HP. *)
(*   intros. *)
(*   split. *)
(*   generalize dependent v. *)
(*   generalize dependent k. *)
(*   generalize dependent n. *)
(*   unfold IndexHas. *)
(*   induction (indexkeys i) eqn:HK. *)
(*   { *)
(*     destruct n. *)
(*     { *)
(*       rewrite indexsetemptykey'. *)
(*       split. *)
(*     rewrite indexemptyspec' in HK. *)
(*     intros. *)
(*     split; intro HX. *)
(*     { *)
(*       destruct indexkeys eqn:HKN at 1. *)
(*       { *)
        
(*       { *)
(*       } *)
(*       destruct indexkeys as [|k2 k'] eqn:HK2; [inversion HX|]. *)
(*       rewrite listhasdest in HX. *)
(*       destruct (indexeq i k k2); subst. *)
(*       { *)
(*         rewrite indexsetoptget in HX. *)
(*         destruct HX as [[H1 H2]|[? ?]]; [|tauto]. *)
(*         replace k'  *)
(*         2: { *)
(*       rewrite indexsetoptget in HX. *)
(*       inversion HX; subst. *)
(*       { *)
(*         destruct (indexeq i k x); subst. *)
(*         { *)
(*           rewrite indexsetoptget in H2. *)
(*           rewrite <- H0 in HX. *)
(*           rewrite listhasdest in HX. *)
(*         destruct indexget eqn:HG; [|tauto]. *)
(*       destruct indexkeys eqn:HK2. *)
(*     { *)
(*       rewrite indexemptyspec' in HK2. *)
(*       split. *)
(*       intros. *)
(*     split. *)
(*     { *)
(*       intro HX. *)
(*       inversion *)
(*     destruct n. *)
(*     rewrite indexemptyspec' in HK. *)
(*     split *)
(*   intros *)
(*   2: { *)
(*   unfold IndexHas. *)
(*   intro H. *)
(*   split. *)
(*   { *)
(*     intros. *)
(*   inversion H; subst. *)
(*   { *)
(*     destruct (indexkeys i) eqn:HK. *)
(*     destruct indexkeys eqn:HK at 1. *)
(*     Search indexkeys. *)
    
(*     rewrite <- H2 in H0. *)
(*   destruct (indexget i k) eqn:HG. *)
(*   { *)
(*     intros. *)
(*   intros. *)

(* Theorem indexkeysaddpermute {K V} (i : Index K V) k v : *)
(*   ListHas (eq k) (indexkeys i) 0 -> *)
(*   Permutation (cons k (indexkeys i)) (indexkeys (indexsetopt i k (Some v))). *)
(*   unfold Permutation. *)
(*   intros H x n. *)
(*   generalize dependent k. *)
(*   induction indexkeys eqn:HK; intro k; repeat rewrite listhasdest. *)
(*   { *)
(*     intros. *)
(*     destruct n. *)
(*     { *)
(*       split. *)
(*       intros. *)
(*       Search indexkeys. *)
(*       rewrite indexkeysempty. *)
(*     split. *)
(*   rewrite listhasdest. *)
(*   destruct n. *)
(*   { *)
(*     split. *)
(*     intros. *)
(*     destruct H0. *)
(*     Search indexkeys. *)
(*     rewrite indexkeysspec' in H. *)
    
(*     destruct indexkeys. *)
(*     Search indexsetopt. *)
(*     Search indexkeys. *)
(*     apply listmap. *)
(*   rewrite indexkeysspec'. *)
(*   rewrite listhasdest. *)
(*   destruct (indexeq i x k); subst. *)
(*   { *)
(*     destruct n; rewrite indexkeysspec',indexsetoptget; *)
(*       [split; [tauto|discriminate]|]. *)
(*     rewrite indexkeysspec' in H. *)
(*     destruct n; [intuition; eauto|]. *)
(*     destruct n; intuition. *)
(*     rewrite H in *. *)
(*     destruct H2. *)
(*     discriminate. *)
(*   } *)
(*   { *)
(*     destruct n; repeat rewrite indexkeysspec'; *)
(*       repeat rewrite indexsetoptirrel by auto; tauto. *)
(*   } *)
(* Qed. *)

(* Theorem indexkeysrempermute {K V} (i : Index K V) k : *)
(*   ListHas (eq k) (indexkeys i) 1 -> *)
(*   Permutation (indexkeys i) (cons k (indexkeys (indexsetopt i k None))). *)
(*   unfold Permutation. *)
(*   intros H x n. *)
(*   rewrite listhasdest. *)
(*   rewrite indexkeysspec'. *)
(*   destruct (indexeq i x k). *)
(*   { *)
(*     subst. *)
(*     rewrite indexkeysspec' in H. *)
(*     destruct H. *)
(*     rewrite H. *)
(*     destruct n; rewrite indexkeysspec',indexsetoptget; *)
(*       [split;[discriminate|tauto]|]. *)
(*     destruct n; intuition; eauto; destruct n; auto. *)
(*     destruct H2. *)
(*     discriminate. *)
(*   } *)
(*   { *)
(*     destruct n; repeat rewrite indexkeysspec'; *)
(*       repeat rewrite indexsetoptirrel by assumption; [tauto|intuition]. *)
(*   } *)
(* Qed. *)

(* Theorem permutelength {A} {_ : EqDec A} (l1 l2 : list A) : *)
(*   Permutation l1 l2 -> length l1 = length l2. *)
(*   unfold Permutation. *)
(*   generalize dependent l2. *)
(*   induction l1; intros. *)
(*   { *)
(*     destruct l2; auto. *)
(*     exfalso. *)
(*     assert (H0 : ListHas (eq a) (a :: l2) 0); [rewrite <- H; constructor|]. *)
(*     rewrite listhasdest in H0. *)
(*     tauto. *)
(*   } *)
(*     specialize (H a). *)
(*     assert (H0 := H 0). *)
(*     destruct H0. *)
(*     exfalso. *)
(*     inversion H0. *)
(*     inversion H0; auto. *)
(*     eapply listhasuniq; [|apply H; constructor|constructor; auto]. *)
(*     simpl. *)
(*   intros. *)
(*   induction l1; simpl. *)
(*   2: { *)

(* Theorem indexkeysremsize {K V} (i1 : Index K V) k : *)
(*   ListHas (eq k) (indexkeys i1) 1 -> *)
(*   length (indexkeys i1) = S (length (indexkeys (indexsetopt i1 k None))). *)
(*   intros. *)
(*   assert (U1 := indexkeysuniq i1). *)
(*   assert (U2 := indexkeysuniq (indexsetopt i1 k None)). *)
(*   assert ( *)
(*   gener *)
(*   inversion H; subst; simpl; f_equal. *)
(*   assert ( *)
(*   induction (indexkeys i1) eqn:HX; [inversion H|]. *)
(*   simpl. *)
(*   induction (length (indexkeys i1)) eqn: *)

(* Theorem indexsmeqleq {K V} (i1 i2 : Index K V) : *)
(*   indexsmallereq i1 i2 -> length (indexkeys i1) <= length (indexkeys i2). *)
(*   intro H. *)
(*   destruct (indexkeys i1) eqn:HK; simpl; [apply PeanoNat.Nat.le_0_l|]. *)
(*   unfold indexsmallereq in *. *)
(*   generalize dependent i1. *)
(*   induction (indexkeys i2); intros. *)
(*   { *)
(*     destruct indexkeys eqn:HK; auto. *)
(*     exfalso. *)
(*     specialize (H k). *)
(*     assert (H2 : ListHas (eq k) (k :: l) 1); [|specialize (H H2); inversion H]. *)
(*     rewrite <- HK, <- indexkeysspechas'. *)
(*     destruct indexget eqn:HG; [econstructor; eauto|]. *)
(*     rewrite indexkeysspecnone in HG. *)
(*     rewrite HK in HG. *)
(*     exfalso. *)
(*     inversion HG; auto. *)
(*   } *)
(*   { *)
    
(*     constructor; auto. *)
(*     rewrite <- HK. *)
(*     destruct H. *)
(*     inversion H. *)
(*     exfalso. *)
(*     destruct *)
(*   einversion H. *)
(*   { *)
(*     induction indexkeys; auto. *)
(*   exfalso. *)
  
(*   [apply PeanoNat.Nat.le_0_l|]. *)
(*   simpl. *)
(*   intros. *)
(*   rewrite <- indexkeysspechas',<- indexkeysspecnone in H. *)
(*   induction (indexkeys i2) *)
(*   2: { *)
(*   induction (indexkeys) eqn:HK; [apply PeanoNat.Nat.le_0_l|]. *)
  
(*   simpl. *)
(*   Search (0 <= _). *)
(*   apply PeanoNat.Nat.le_0_l. *)
(*   assert (HK : forall k, indexget k *)
(*   induction (indexkeys i2) *)
(*   eapply PeanoNat.Nat.le_trans; [|apply filterleq]. *)
(*   apply indexkeysspechas in H. *)
(*   apply (PeanoNat.Nat.le_trans *)
(*            _ (length (filter (fun k => issome (indexget i1 k)) *)
(*                              (indexkeys i2))) _). *)
(*   induction index *)
(*   ind *)

(* Theorem indsmallwf {K V} : well_founded (indexsmaller (K:=K) (V:=V)). *)
(*   unfold well_founded. *)
(*   intros. *)
  
(*   induction (length (indexkeys a)) eqn:HK. *)
(*   2: { *)
(*   { *)
(*     constructor. *)
(*     intros. *)
(*     destruct H. *)
    
(*     unfold in *)
(*   intros. *)
(*   constructor. *)
(*   intros. *)
(*   destruct H. *)
(*   do 3 destruct H0. *)
(*   rewrite <- indexalistspec in H1. *)
(*   unfold indexsmallereq in H. *)
(*   specialize (H x x0). *)

(* Record Graph {Node Edge} : Type := *)
(*   make_graph { *)
(*       graphindextype : Type -> Type; *)
(*       graphindeximpl : IndexImpl Node graphindextype; *)
(*       graphobj : Index Node (graphindextype Edge); *)
(*     }. *)

(* Arguments Graph : clear implicits. *)

(* Definition emptygraph {Node Edge A} (I : IndexImpl Node A) : Graph Node Edge := *)
(*   make_graph _ _ _ I (make_index _ _ _ I (indeximplempty I)). *)

(* Definition graphedgesfrom {Node Edge : Type} g e: Index Node Edge := *)
(*   let I := graphindeximpl g in *)
(*   make_index *)
(*     _ _ *)
(*     (graphindextype g) *)
(*     I *)
(*     (optdefault (indeximplempty I) (indexget (graphobj g) e)). *)

(* Definition graphedge {Node Edge : Type} g (n1 n2 : Node) : option Edge := *)
(*   indexget (graphedgesfrom g n1) n2. *)

(* Definition graphremoveoutgoing {Node Edge : Type} g n := *)
(*   let I := graphindeximpl g in *)
(*   make_graph Node Edge _ I (indexsetopt (graphobj g) n None). *)

(* (* Definition graphedgealist {Node Edge : Type} g e : ((Node*Node)*Edge) := *) *)
(* (*   fold_right *) *)
(* (*     app *) *)
(* (*     (map (fun k1v =>  *) *)

(* Print well_founded. *)

(* Program Fixpoint reachable {Node Edge} (g : Graph Node Edge) (x y : Node) *)
(*         {eqd : EqDec Node} *)
(*         {measure *)
(*            (length (alistsimplify (indeximplalist (graphindeximpl g) (graphobj g))))} *)
(*   : bool := *)
(*   orb (iseqb x y) *)
(*       (let i := graphedgesfrom g x in *)
(*        let rm := graphremoveoutgoing g x in *)
(*        match indexalist (graphedgesfrom g x) with *)
(*        | nil => false *)
(*        | cons _ _ => *)
(*          fold_right (fun ne knil => orb knil (reachable rm (fst ne) y)) *)
(*                     false *)
(*                     (indexalist (graphedgesfrom g x)) *)
(*        end). *)
(* Next Obligation. *)
