(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2018 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Implementation of separation logic.                 MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
   To compile this module, first load and compile:       MMMMMMMMMMMMMM7..$MNDM+
   * Picinae_core                                         MMDMMMMMMMMMZ7..$DM$77
   * Picinae_theory                                        MMMMMMM+MMMZ7..7ZM~++
   Then compile this module with menu option                MMMMMMMMMMM7..ZNOOMZ
   Compile->Compile_buffer.                                  MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
                                                               $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)


Require Import Picinae_core.
Require Import Picinae_theory.
Require Import Program.Equality.
Require Import FunctionalExtensionality.
Require Import NArith.

(* This module implements separation logic for local reasoning about memory in
   Picinae.  Rather than define a separation operators as an Inductive datatype
   with associated inference rules (which would confine proof authors to using
   only those rules for local reasoning), we instead derive the soundness of
   separation logic's Frame Rule directly in Coq.  This allows proof authors to
   use Coq's entire proof logic for local reasoning by simply applying the
   Frame Rule as a theorem when desired. *)


(* Heaps are partial functions from addr to N.  The IL interpreter expresses
   memories m as total functions, so to make them act like heaps, we separately
   encode the heap's domain (h:hdomain), which we here express as a partial
   function from addr to unit.  For any addr 'a', if (h a = None) then address
   'a' is outside the heap; otherwise (h a = Some tt) and (m a) is its value.
   (This is more convenient than representing h as a total function from addr
   to bool, since it allows functions and theorems concerning partial functions
   to be applied to heaps and their domains.) *)
Definition hdom {A} (h: heap A) a := match h a with None => None | Some _ => Some tt end.
Definition hopp {A} (h: heap A) a := match h a with None => Some tt | Some _ => None end.

(* the restriction of heap h2 to the domain of h1: *)
Definition resth {A B} (h1: heap A) (h2: heap B) a :=
  match h1 a with None => None | Some _ => h2 a end.

(* disjointedness of heaps *)
Definition hdisj {A B} (h1: heap A) (h2: heap B) := forall a, h1 a = None \/ h2 a = None.

(* A "heapy value" is like a regular value, except that if it is a memory (VaM),
   then it holds a partial function instead of a total function. *)
Definition hval := avalue (option N).
Definition to_heap (m: addr -> N) a := Some (m a).
Definition to_hval (u:value) :=
  match u with VaN n w => VaN n w | VaM m w => VaM (to_heap m) w end.

Definition hstore (V:Type) := V -> option hval.
Definition to_hstore {V} s (v:V) := option_map to_hval (s v).

(* restriction of heapy values and heapy stores to a given domain: *)
Definition resthv {A} (h:heap A) (hu:hval) :=
  match hu with VaN n w => VaN n w | VaM h' w => VaM (resth h h') w end.
Definition resths {V A} (h:heap A) (hs:hstore V) v :=
  match hs v with None => None | Some hv => Some (resthv h hv) end.


(* Propositional operators from separation logic are here defined as Coq Props: *)

Definition hsprop (V:Type) := hstore V -> Prop.

(* Separating conjunction (sepconj _ P Q) is satisfied by heaps that can be
   partitioned into disjoint heaplets that satisfy P and Q respectively. *)
Definition sepconj V P Q : hsprop V :=
  fun hs => exists (h:hdomain), P (resths h hs) /\ Q (resths (hopp h) hs).

(* Separation logic for Picinae is complicated by the fact that Picinae stores
   can have many heaps (or none), not just one.  We therefore define heap
   propositions as properties satisfied by ALL heaps in the store. *)
Definition hprop V (P: heap N -> Prop): hsprop V :=
  fun hs => forall v m w (SV: hs v = Some (VaM m w)), P m.

Definition hfalse {A:Type} (_:A) := False.

Definition htrue {A:Type} (_:A) := True.

(* (pointsto a Q) is satisfied by heaps containing exactly one address a,
   which contains something satisfying Q. *)
Definition pointsto a Q (h: heap N) :=
  forall a0, match h a0 with None => a0<>a | Some n => a0=a /\ Q n end.

(* emp is satisfied by exactly and only the empty heap. *)
Definition emp (h: heap N) := forall a, h a = None.

(* Separating implication (sepimp P Q) is satisfied by heaps that, when joined
   with any disjoint, P-satisfying heap, become a heap that satisfies Q. *)
Definition sepimp (P Q: heap N -> Prop) (h: heap N) :=
  forall h' (DJ: hdisj h h'), P h' -> Q (updateall h h').


(* Meta-properties of heap-properties: *)

(* monotonic properties are preserved by domain expansion. *)
Definition monotonic {A B} (P: (A -> option B) -> Prop) :=
  forall h1 h2 (SS: h1 ⊆ h2), P h1 -> P h2.

(* monotonic' properties are preserved by domain contraction. *)
Definition monotonic' {A B} (P: (A -> option B) -> Prop) :=
  forall h1 h2 (SS: h2 ⊆ h1), P h1 -> P h2.

(* update-preserving heapy-store-properties are preserved by updating var v to
   heapy value hu. *)
Definition upd_pres {V} {_:EqDec V} (R: hsprop V) hs hu v :=
  R hs -> R (update hs v (Some hu)).


(* Helper lemmas concerning heaps and heap domains: *)

Lemma resth_hdom:
  forall {A B} (h1:heap A) (h2:heap B), resth (hdom h1) h2 = resth h1 h2.
Proof.
  intros. extensionality a. unfold hdom,resth. destruct (h1 a); reflexivity.
Qed.

Lemma hopp_hdom:
  forall {A} (h:heap A), hopp (hdom h) = hopp h.
Proof.
  intros. extensionality a. unfold hopp,hdom. destruct (h a); reflexivity.
Qed.

Lemma sub_htotal: forall h, h ⊆ htotal.
Proof. unfold pfsub. intros. destruct y. reflexivity. Qed.

Lemma hopp_mono:
  forall {A} (h1 h2: heap A) (SS: h1 ⊆ h2), hopp h2 ⊆ hopp h1.
Proof.
  unfold pfsub, hopp. intros. destruct y. specialize (SS x). destruct (h1 x).
    rewrite <- H, (SS a); reflexivity.
    reflexivity.
Qed.

Lemma updateall_comm:
  forall (h1 h2:hdomain), updateall h1 h2 = updateall h2 h1.
Proof.
  unfold updateall. intros. extensionality a.
  destruct (h1 a), (h2 a); try destruct u; try destruct u0; reflexivity.
Qed.

Lemma resth_subset:
  forall {A B} (h1: heap A) (h2: heap B), resth h1 h2 ⊆ h2.
Proof.
  unfold pfsub, resth. intros. destruct (h1 x). assumption. discriminate.
Qed.

Lemma resth_mono_l:
  forall {A B} (h1 h2: heap A) (h: heap B) (SS: h1 ⊆ h2), resth h1 h ⊆ resth h2 h.
Proof.
  unfold pfsub,resth. intros. specialize (SS x). destruct (h1 x).
    rewrite (SS a). assumption. reflexivity.
    discriminate.
Qed.

Lemma hopp_resth:
  forall {A B} (h1: heap A) (h2: heap B), hopp (resth h1 h2) = updateall (hopp h1) (hopp h2).
Proof.
  intros. extensionality a. unfold resth,hopp,updateall.
  destruct (h1 a), (h2 a); reflexivity.
Qed.

Lemma hopp_inv:
  forall h, hopp (hopp h) = h.
Proof.
  intro. extensionality a. unfold hopp. destruct (h a); try destruct u; reflexivity.
Qed.

Lemma resth_ident:
  forall (h1 h2:hdomain) (SS: h1 ⊆ h2), resth h1 h2 = h1.
Proof.
  unfold resth,pfsub. intros. extensionality a. specialize (SS a).
  destruct (h1 a), (h2 a); try destruct u; try destruct u0; try reflexivity.
  apply SS. reflexivity.
Qed.

Lemma resth_comm:
  forall (h1 h2: hdomain), resth h1 h2 = resth h2 h1.
Proof.
  intros. extensionality a. unfold resth.
  destruct (h1 a), (h2 a); try destruct u; try destruct u0; reflexivity.
Qed.

Lemma resthv_hdom:
  forall {A} (h:heap A) hv, resthv (hdom h) hv = resthv h hv.
Proof.
  intros. destruct hv. reflexivity. simpl. rewrite resth_hdom. reflexivity.
Qed.

Lemma resth_assoc:
  forall {A B C} (h1: heap A) (h2: heap B) (h3: heap C),
  resth h1 (resth h2 h3) = resth (resth h1 h2) h3.
Proof.
  intros. extensionality a. unfold resth.
  destruct (h1 a),(h2 a); reflexivity.
Qed.

Lemma resthv_assoc:
  forall {A B} (h1: heap A) (h2: heap B) hv, resthv h1 (resthv h2 hv) = resthv (resth h1 h2) hv.
Proof.
  intros. destruct hv. reflexivity. unfold resthv. rewrite resth_assoc. reflexivity.
Qed.

Lemma hdisj_mono:
  forall {A B} (h1 h2: heap A) (h3: heap B) (SS: h1 ⊆ h2) (DJ: hdisj h2 h3),
  hdisj h1 h3.
Proof.
  unfold hdisj. intros. specialize (SS a). destruct (h1 a).
    right. destruct (DJ a).
      rewrite (SS a0) in H. discriminate. reflexivity.
      assumption.
    left. reflexivity.
Qed.

Lemma resths_hdom:
  forall {V A} (h:heap A) (hs:hstore V), resths (hdom h) hs = resths h hs.
Proof.
  intros. extensionality a. unfold resths. destruct (hs a).
    rewrite resthv_hdom. reflexivity.
    reflexivity.
Qed.

Lemma resths_assoc:
  forall {V A B} (h1: heap A) (h2: heap B) (hs:hstore V),
  resths h1 (resths h2 hs) = resths (resth h1 h2) hs.
Proof.
  intros. extensionality v. unfold resths. destruct (hs v).
    rewrite resthv_assoc. reflexivity.
    reflexivity.
Qed.

Lemma resths_mono_r:
  forall {V A} (h1 h2: hstore V) (h: heap A) (SS: h1 ⊆ h2), resths h h1 ⊆ resths h h2.
Proof.
  unfold resths, pfsub. intros. specialize (SS x). destruct (h1 x), (h2 x); try discriminate.
    specialize (SS _ (eq_refl _)). injection SS as; subst. assumption.
    specialize (SS _ (eq_refl _)). discriminate.
Qed.

Lemma to_hstore_update {V} {ED:EqDec V}:
  forall s (v:V) u, to_hstore (s[v := Some u]) = (to_hstore s)[v := Some (to_hval u)].
Proof.
  intros. extensionality v0. unfold to_hstore,update. simpl. destruct (v0 == v); reflexivity.
Qed.

Lemma resths_update {V} {ED:EqDec V}:
  forall {A} (h:heap A) hs (v:V) hu, resths h (hs[v := Some hu]) = (resths h hs)[v := Some (resthv h hu)].
Proof.
  intros. extensionality v0. unfold resths,update. simpl. destruct (v0 == v); reflexivity.
Qed.



Module Type PICINAE_SLOGIC (IL: PICINAE_IL).

Import IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.
Open Scope N.

Definition sep := sepconj var.


(* In separation logic, Hoare triple {P}q{Q} asserts that executing q on any
   heap h that satisfyies P does not "go wrong" and yields a heap satisfying Q.
   "Going wrong" in this context means accessing memory outside of h's domain.
   (It does not mean type-mismatch, which is handled by the static semantics.)
   We therefore here define "go wrong" as "contracting the heap-domain of q
   that otherwise stays right does not cause q to go wrong". *)

Definition htrip_stmt P q Q :=
  forall s h s' x (PRE: P (resths h (to_hstore s))) (XS: exec_stmt htotal s q s' x),
    exec_stmt h s q s' x /\ Q (resths h (to_hstore s')).

Definition htrip_prog P p a n Q :=
  forall s h s' x (PRE: P (resths h (to_hstore s))) (XP: exec_prog htotal p a s n s' x),
    exec_prog h p a s n s' x /\ Q (resths h (to_hstore s')).




(* The key idea behind the following proofs is that executing any expression or
   statement with a restricted heap domain always yields a value or store in
   which nothing outside that domain has changed.  Output values therefore obey
   the following modeling relation: *)
Inductive hmodels (s:store) (h:hdomain) : value -> Prop :=
| HMN n w: hmodels s h (VaN n w)
| HMM m w v m' (SV: s v = Some (VaM m' w)) (FR: forall a, h a = None -> m a = m' a):
    hmodels s h (VaM m w).

Definition hmodels_store (h:hdomain) (s s':store) :=
  forall v u, s' v = Some u -> hmodels s h u.


(* Our goal is to prove the soundness of the frame rule: {P}q{Q} -> {P*R}q{Q*R}.
   But only certain properties R satisfy this rule.  In particular, R must not
   depend upon variables and memory addresses assigned by q.  We define this
   "framing" meta-property below. *)

(* R "frames" q if for all variables v assigned by q, updating v to any value u
   that satisfies the modeling relation preserves R. *)

Definition frames_stmt (R: hsprop var) q :=
  forall s (h:hdomain) u (HM: hmodels s (hopp h) u),
  allassigns (upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u))) q.

Definition frames_prog (R: hsprop var) (p:program) :=
  forall s a, match p s a with None => True | Some (_,q) => frames_stmt R q end.


(* Duals to the above:  We need duals to each of the above because if R contains
   a negation or implication, the framing requirement gets reversed for the
   negated sub-proposition or antecedent. *)

(* R "universally-frames" q if forall all variables v assigned by q, updating v
   to any value at all preserves R. *)

Definition frames'_stmt (R: hsprop var) q :=
  forall s (h:hdomain) u,
  allassigns (upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u))) q.

Definition frames'_prog (R: hsprop var) (p:program) :=
  forall s a, match p s a with None => True | Some (_,q) => frames'_stmt R q end.



(* Helper lemmas for breaking "frames" hypotheses down into their premises: *)

Lemma destruct_frames_stmt:
  forall R q (FR: frames_stmt R q),
  match q with
  | Nop | Jmp _ | Exn _ => True
  | Move v _ => forall s (h:hdomain) hu (HM: hmodels s (hopp h) hu), upd_pres R (resths h (to_hstore s)) (resthv h (to_hval hu)) v
  | Seq q1 q2 => frames_stmt R q1 /\ frames_stmt R q2
  | Rep _ q1 => frames_stmt R q1
  | If _ q1 q2 => frames_stmt R q1 /\ frames_stmt R q2
  end.
Proof.
  intros. destruct q; solve
  [ exact I
  | try split; intros s dom u HM; specialize (FR s dom u HM); inversion FR; assumption ].
Qed.

Lemma destruct_frames'_stmt:
  forall R q (FR: frames'_stmt R q),
  match q with
  | Nop | Jmp _ | Exn _ => True
  | Move v _ => forall s (h:hdomain) hu, upd_pres R (resths h (to_hstore s)) (resthv h (to_hval hu)) v
  | Seq q1 q2 => frames'_stmt R q1 /\ frames'_stmt R q2
  | Rep _ q1 => frames'_stmt R q1
  | If _ q1 q2 => frames'_stmt R q1 /\ frames'_stmt R q2
  end.
Proof.
  intros. destruct q; solve
  [ exact I
  | try split; intros s dom u; specialize (FR s dom u); inversion FR; assumption ].
Qed.



(* Proof that the IL semantics obey the modeling relation: *)

Lemma hmodels_refl:
  forall h s, hmodels_store h s s.
Proof.
  intros h s v u H. destruct u.
    apply HMN.
    eapply HMM. eassumption. reflexivity.
Qed.

Lemma hmodels_trans:
  forall h s1 s2 s3, hmodels_store h s1 s2 -> hmodels_store h s2 s3 ->
  hmodels_store h s1 s3.
Proof.
  intros h s1 s2 s3 H1 H2 v u S3V.
  specialize (H2 v u S3V). inversion H2; subst.
    apply HMN.
    specialize (H1 _ _ SV). inversion H1; subst.
      eapply HMM. eassumption. intros. rewrite (FR a H). apply FR0. assumption.
Qed.

Lemma hmodels_mono:
  forall s h1 h2 u (SS: h1 ⊆ h2) (HM: hmodels s h1 u), hmodels s h2 u.
Proof.
  intros. inversion HM; subst.
    apply HMN.
    eapply HMM. exact SV. intros. apply FR. specialize (SS a tt). destruct (h1 a).
      destruct u. rewrite SS in H. discriminate. reflexivity.
      reflexivity.
Qed.

Theorem hmodels_exp:
  forall h s e u (E: eval_exp h s e u),
  hmodels s h u.
Proof.
  intros. revert s u E. induction e; intros; inversion E; subst; try apply HMN.
    destruct u; econstructor. eassumption. reflexivity.

    apply IHe1 in E1. inversion E1; subst.
    eapply HMM. eassumption.
    intros. rewrite <- (FR _ H).
    destruct (N.lt_ge_cases a0 a). apply setmem_frame_low. assumption.
    destruct (N.le_gt_cases (a+w) a0). apply setmem_frame_high. assumption.
    rewrite <- (N.add_sub a0 a), N.add_comm, <- N.add_sub_assoc in H1 by assumption.
    apply N.add_lt_mono_l, W in H1.
    rewrite N.add_sub_assoc, N.add_comm, N.add_sub in H1 by assumption.
    apply proj1 in H1. rewrite H in H1. discriminate H1.

    destruct b; apply HMN.

    destruct u; apply HMN.

    apply IHe2 in E2. inversion E2; subst. apply HMN. destruct (vareq v0 v).
      subst v0. rewrite update_updated in SV. injection SV as; subst. apply IHe1 in E1. inversion E1; subst.
        eapply HMM. eassumption. intros. rewrite (FR a H). apply FR0. assumption.
      eapply HMM. intros. rewrite update_frame in SV by assumption. eassumption. assumption.

    destruct n1; [ apply IHe3 | apply IHe2 ]; assumption.
Qed.

Theorem hmodels_stmt:
  forall h s q s' x (XS: exec_stmt h s q s' x),
  hmodels_store h s s'.
Proof.
  intros. dependent induction XS; intros; try solve [ apply hmodels_refl | assumption ].
    intros v' u' H. destruct u'. apply HMN. destruct (vareq v' v).
      subst v'. rewrite update_updated in H. injection H as; subst. eapply hmodels_exp; eassumption.
      rewrite update_frame in H by assumption. eapply HMM. eassumption. reflexivity.
    eapply hmodels_trans; eassumption.
Qed.

Theorem hmodels_prog:
  forall h p a s n s' x (XP: exec_prog h p a s n s' x),
  hmodels_store h s s'.
Proof.
  intros. dependent induction XP; intros.
    apply hmodels_refl.
    eapply hmodels_trans. eapply hmodels_stmt. eassumption. eassumption.
    eapply hmodels_stmt. eassumption.
Qed.



(* Proof that if R frames q, then executing q preserves R. *)

Lemma frames_rep:
  forall R e q (FR: frames_stmt R q), frames_stmt R (Seq q (Rep e q)).
Proof.
  intros. intros s h u HM. apply AASeq.
    apply FR. assumption.
    apply AARep, FR. assumption.
Qed.

Lemma framed_stmt:
  forall {A} (R: hsprop var) (h:heap A) s q s' x (FR: frames_stmt R q)
         (XS: exec_stmt (hopp h) s q s' x)
         (HS: hmodels_store (hopp h) s s') (PRE: R (resths h (to_hstore s))),
  R (resths h (to_hstore s')).
Proof.
  intros. revert s s' x XS FR HS PRE.
  induction q using stmt_ind2; intros;
    inversion XS; clear XS; subst; try assumption;
    apply destruct_frames_stmt in FR.

    rewrite to_hstore_update, resths_update, <- resths_hdom, <- resthv_hdom. apply FR.
      rewrite hopp_hdom. eapply hmodels_exp. eassumption.
      rewrite resths_hdom. assumption.

    eapply IHq1; try eassumption. apply FR.
    eapply IHq2. eassumption.
      apply FR.
      eapply hmodels_stmt. eassumption.
      eapply IHq1; try eassumption.
        apply FR.
        eapply hmodels_stmt. eassumption.

    destruct c.
      eapply IHq2; try eassumption. apply FR.
      eapply IHq1; try eassumption. apply FR.

    eapply IHq2; try eassumption.
    apply Niter_invariant.
      intros s1 h1 u HM. apply AANop.
      intros q' FR' s1 h1 u HM. apply AASeq; [ apply FR | apply FR']; assumption.
Qed.

Lemma framed_prog:
  forall {A} (R: hsprop var) (h:heap A) p a s n s' x (FR: frames_prog R p)
         (XP: exec_prog (hopp h) p a s n s' x)
         (HS: hmodels_store (hopp h) s s') (PRE: R (resths h (to_hstore s))),
  R (resths h (to_hstore s')).
Proof.
  intros. revert a s s' x XP HS PRE. induction n; intros; inversion XP; clear XP; subst.
    assumption.
    eapply IHn. eassumption.
      eapply hmodels_prog. eassumption.
      eapply framed_stmt; try eassumption.
        specialize (FR s a). rewrite LU in FR. exact FR.
        eapply hmodels_stmt. eassumption.
    eapply framed_stmt; try eassumption. specialize (FR s a). rewrite LU in FR. exact FR.
Qed.


(* Main result: The frame rule of separation logic is sound.  In particular,
   if {P}q{Q} holds, and if R frames q, then {P*R}q{Q*R} holds. *)

Theorem stmt_frame:
  forall q (P Q R: hsprop var) (FR: frames_stmt R q)
         (HT: htrip_stmt P q Q),
  htrip_stmt (sep P R) q (sep Q R).
Proof.
  unfold htrip_stmt. intros. destruct PRE as [dom' [PS RS]]. split.
    eapply exec_stmt_hmono.
      eapply resth_subset.
      apply HT. rewrite <- resths_assoc. exact PS. exact XS.
    exists dom'. rewrite !resths_assoc in *. split.
      eapply HT; eassumption.
      eapply framed_stmt; try eassumption; rewrite hopp_resth, hopp_inv, updateall_comm.
        eapply exec_stmt_hmono.
          etransitivity; [|apply subset_updateall]. eapply resth_subset.
          rewrite resth_comm. apply HT. exact PS. exact XS.
        eapply hmodels_stmt. eapply exec_stmt_hmono.
          etransitivity; [|apply subset_updateall]. eapply resth_subset.
          rewrite resth_comm. apply HT. exact PS. exact XS.
Qed.

Theorem prog_frame:
  forall p a n (P Q R: hsprop var) (FR: frames_prog R p)
         (HT: htrip_prog P p a n Q),
  htrip_prog (sep P R) p a n (sep Q R).
Proof.
  unfold htrip_prog. intros. destruct PRE as [h' [PS RS]]. split.
    eapply exec_prog_hmono.
      eapply resth_subset.
      apply HT. rewrite <- resths_assoc. exact PS. exact XP.
    exists h'. rewrite !resths_assoc in *. split.
      eapply HT; eassumption.
      eapply framed_prog; try eassumption; rewrite hopp_resth, hopp_inv, updateall_comm.
        eapply exec_prog_hmono.
          etransitivity; [|apply subset_updateall]. eapply resth_subset.
          rewrite resth_comm. apply HT. exact PS. exact XP.
        eapply hmodels_prog. eapply exec_prog_hmono.
          etransitivity; [|apply subset_updateall]. eapply resth_subset.
          rewrite resth_comm. apply HT. exact PS. exact XP.
Qed.



(* At this point we have our main result, but it requires users to prove that
   R frames q in order to use it.  We here prove some general sufficiency
   conditions to help users prove this meta-property. *)

(* Sufficiency conditions for proving "R (universally-)frames q": *)
Lemma upd_pres_sep:
  forall P Q hs hu v
         (UP1: forall (h:hdomain), upd_pres P (resths h hs) (resthv h hu) v)
         (UP2: forall (h:hdomain), upd_pres Q (resths h hs) (resthv h hu) v),
  upd_pres (sep P Q) hs hu v.
Proof.
  unfold upd_pres, sep. intros. destruct H as [h [P1 Q2]].
  exists h. split; rewrite resths_update.
    apply UP1. assumption.
    apply UP2. assumption.
Qed.

(* P*Q frames q if P and Q both frame q. *)
Theorem frames_stmt_sep:
  forall P Q q (FR1: frames_stmt P q) (FR2: frames_stmt Q q),
  frames_stmt (sep P Q) q.
Proof.
  induction q; intros; unfold frames_stmt; intros; try solve [ constructor ];
  repeat match goal with [ H: frames_stmt _ (_ _) |- _ ] => apply destruct_frames_stmt in H end.
    apply AAMove, upd_pres_sep; intros dom0 H.
      rewrite resthv_assoc, resths_assoc. apply FR1.
        eapply hmodels_mono; [|eassumption]. apply hopp_mono. apply resth_subset.
        rewrite <- resths_assoc. assumption.
      rewrite resthv_assoc, resths_assoc. apply FR2.
        eapply hmodels_mono; [|eassumption]. apply hopp_mono. apply resth_subset.
        rewrite <- resths_assoc. assumption.
    apply AASeq; [ apply IHq1 | apply IHq2 ]; intros; solve [ apply FR1 | apply FR2 | assumption ].
    apply AAIf; [ apply IHq1 | apply IHq2 ]; intros; solve [ apply FR1 | apply FR2 | assumption ].
    apply AARep, IHq; intros; assumption.
Qed.

(* P*Q universally-frames q if both P and Q universally-frame q. *)
Theorem frames'_stmt_sep:
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames'_stmt Q q),
  frames'_stmt (sep P Q) q.
Proof.
  unfold frames'_stmt. induction q; intros; try solve [ constructor ].
    apply AAMove, upd_pres_sep; intros h0 H.
      specialize (FR1 s (resth h0 h) u). inversion FR1.
        rewrite resths_assoc, resthv_assoc. apply PV. rewrite <- resths_assoc. assumption.
      specialize (FR2 s (resth h0 h) u). inversion FR2.
        rewrite resths_assoc, resthv_assoc. apply PV. rewrite <- resths_assoc. assumption.
    apply AASeq; [ apply IHq1 | apply IHq2 ]; intros; solve
    [ specialize (FR1 s0 h0 u0); inversion FR1; assumption
    | specialize (FR2 s0 h0 u0); inversion FR2; assumption ].
    apply AAIf; [ apply IHq1 | apply IHq2 ]; intros; solve
    [ specialize (FR1 s0 h0 u0); inversion FR1; assumption
    | specialize (FR2 s0 h0 u0); inversion FR2; assumption ].
    apply AARep, IHq; intros.
      specialize (FR1 s0 h0 u0). inversion FR1. assumption.
      specialize (FR2 s0 h0 u0). inversion FR2. assumption.
Qed.

Theorem frames_prog_sep:
  forall P Q p (FR1: frames_prog P p) (FR2: frames_prog Q p),
  frames_prog (sep P Q) p.
Proof.
  unfold frames_prog. intros. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames_stmt_sep; assumption.
    exact I.
Qed.

Theorem frames'_prog_sep:
  forall P Q p (FR1: frames'_prog P p) (FR2: frames'_prog Q p),
  frames'_prog (sep P Q) p.
Proof.
  unfold frames'_prog. intros. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames'_stmt_sep; assumption.
    exact I.
Qed.

Theorem frames_stmt_htrue: forall q, frames_stmt htrue q.
Proof.
  unfold htrue,frames_stmt. intros.
  induction q; constructor; try intro; try assumption.
Qed.

Theorem frames'_stmt_htrue: forall q, frames'_stmt htrue q.
Proof.
  unfold htrue,frames'_stmt. intros.
  induction q; constructor; try intro; try assumption.
Qed.

Theorem frames_prog_htrue: forall p, frames_prog htrue p.
Proof.
  unfold htrue,frames_prog. intros. destruct (p s a) as [(sz,q)|].
    apply frames_stmt_htrue.
    exact I.
Qed.

Theorem frames'_prog_htrue: forall p, frames'_prog htrue p.
Proof.
  unfold htrue,frames'_prog. intros. destruct (p s a) as [(sz,q)|].
    apply frames'_stmt_htrue.
    exact I.
Qed.

Theorem frames_stmt_hfalse: forall q, frames_stmt hfalse q.
Proof.
  unfold hfalse,frames_stmt. intros.
  induction q; constructor; try intro; try assumption.
Qed.

Theorem frames'_stmt_hfalse: forall q, frames'_stmt hfalse q.
Proof.
  unfold hfalse,frames'_stmt. intros.
  induction q; constructor; try intro; try assumption.
Qed.

Theorem frames_prog_hfalse: forall p, frames_prog hfalse p.
Proof.
  unfold hfalse,frames_prog. intros. destruct (p s a) as [(sz,q)|].
    apply frames_stmt_hfalse.
    exact I.
Qed.

Theorem frames'_prog_hfalse: forall p, frames'_prog hfalse p.
Proof.
  unfold hfalse,frames'_prog. intros. destruct (p s a) as [(sz,q)|].
    apply frames'_stmt_hfalse.
    exact I.
Qed.

(* To prove that R (universally-)frames q, it sufficies to prove that R is
   update-preserving for all possible stores. *)
Lemma frames_stmt_anystore:
  forall R q, (forall s (h:hdomain) u v (HM: hmodels s (hopp h) u), upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u)) v) ->
  frames_stmt R q.
Proof.
  unfold frames_stmt. intros. induction q; intros; constructor; try assumption.
  apply H. assumption.
Qed.

Lemma frames'_stmt_anystore:
  forall R q, (forall s (h:hdomain) u v, upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u)) v) ->
  frames'_stmt R q.
Proof.
  unfold frames'_stmt. intros. induction q; intros; constructor; try assumption.
  apply H.
Qed.

(* It follows that all heap-properties frame q. *)
Theorem frames_stmt_hprop:
  forall R q, frames_stmt (hprop var R) q.
Proof.
  intros. apply frames_stmt_anystore. unfold upd_pres,hprop. intros. destruct (vareq v0 v).
    subst v0. rewrite update_updated in SV. destruct u.
      discriminate.
      inversion HM. injection SV as. subst. replace (resth h (to_heap _)) with (resth h (to_heap m')).
        eapply H. unfold resths,to_hstore. rewrite SV0. reflexivity.
        extensionality a. specialize (FR a). unfold resth. unfold hopp in FR. destruct (h a).
          unfold to_heap. destruct u. rewrite FR; reflexivity.
          reflexivity.
    rewrite update_frame in SV by assumption. eapply H. eassumption.
Qed.

(* (frames'_stmt (hprop R) q) is false for useful R's, so not worth proving
   anything about it.  This is because hprops are properties that are universally
   satisfied by all heaps in the store, and frames'_stmt requires that its
   proposition parameter R be satisfied by all values assigned to variables in q.
   Thus, if q contains any assignments at all, R would have to be universally
   true of all heaps in order for (frames'_stmt (hprop R) q) to be true.  This
   has taken me a long time to understand, so I prove it here to convince/remind
   myself. *)
Remark frames'_stmt_hprop_useless:
  forall R v e, (frames'_stmt (hprop var R) (Move v e)) -> (forall h, R h).
Proof.
  intros.
  specialize (H (fun _ => None) (hdom h) (VaM (fun a => match h a with None => 0 | Some n => n end) 0)).
  inversion H; subst. eapply PV. discriminate.
  rewrite update_updated. simpl. replace (resth _ _) with h. reflexivity.
  extensionality a. unfold to_heap, resth, hdom. destruct (h a); reflexivity.
Qed.

Theorem frames_prog_hprop:
  forall R p, frames_prog (hprop var R) p.
Proof.
  unfold frames_prog. intros. destruct (p s a) as [(sz,q)|].
    apply frames_stmt_hprop.
    exact I.
Qed.

(* (P -> Q) frames q if: P is inverse-monotonic and universally-frames q,
   and Q frames q. *)
Theorem frames_stmt_impl:
  forall P Q q (M1: monotonic' P) (FR1: frames'_stmt P q) (FR2: frames_stmt Q q),
  frames_stmt (fun hs => P hs -> Q hs) q.
Proof.
  induction q; intros; unfold frames_stmt; intros; try solve [ constructor ].

    apply AAMove. unfold upd_pres. intros.
    apply destruct_frames'_stmt in FR1. apply destruct_frames_stmt in FR2.
    apply FR2. assumption. apply H. destruct (s v) as [u0|] eqn:SV.
      replace (resths _ _) with (resths h (to_hstore (s[v:=Some u])) [ v := Some (resthv h (to_hval u0)) ]).
        apply FR1. rewrite to_hstore_update, resths_update. assumption.
        rewrite to_hstore_update, resths_update, update_cancel. extensionality v0. destruct (vareq v0 v).
          subst v0. rewrite update_updated. unfold to_hstore, resths. rewrite SV. reflexivity.
          rewrite update_frame by assumption. reflexivity.
      eapply M1; [|eassumption]. intros v0 hv SS. destruct (vareq v0 v).
        subst. unfold resths, to_hstore in SS. rewrite SV in SS. discriminate.
        rewrite update_frame; assumption.

    apply AASeq; [ apply IHq1 | apply IHq2 ]; try assumption; solve
    [ apply destruct_frames'_stmt in FR1; apply FR1
    | apply destruct_frames_stmt in FR2; apply FR2 ].

    apply AAIf; [ apply IHq1 | apply IHq2 ]; try assumption; solve
    [ apply destruct_frames'_stmt in FR1; apply FR1
    | apply destruct_frames_stmt in FR2; apply FR2 ].

    apply AARep. apply IHq; try assumption.
      apply destruct_frames'_stmt in FR1; apply FR1.
      apply destruct_frames_stmt in FR2; apply FR2.
Qed.

Theorem frames'_stmt_impl:
  forall P Q q (M1: monotonic' P) (FR1: frames'_stmt P q) (FR2: frames'_stmt Q q),
  frames'_stmt (fun hs => P hs -> Q hs) q.
Proof.
  induction q; intros; unfold frames'_stmt; intros; try solve [ constructor ].

    apply AAMove. unfold upd_pres. intros.
    apply destruct_frames'_stmt in FR1. apply destruct_frames'_stmt in FR2.
    apply FR2. apply H. destruct (s v) as [u0|] eqn:SV.
      replace (resths _ _) with (resths h (to_hstore (s[v:=Some u])) [ v := Some (resthv h (to_hval u0)) ]).
        apply FR1. rewrite to_hstore_update, resths_update. assumption.
        rewrite to_hstore_update, resths_update, update_cancel. extensionality v0. destruct (vareq v0 v).
          subst v0. rewrite update_updated. unfold to_hstore, resths. rewrite SV. reflexivity.
          rewrite update_frame by assumption. reflexivity.
      eapply M1; [|eassumption]. intros v0 hv SS. destruct (vareq v0 v).
        subst. unfold resths, to_hstore in SS. rewrite SV in SS. discriminate.
        rewrite update_frame; assumption.

    apply AASeq; [ apply IHq1 | apply IHq2 ]; try assumption; solve
    [ apply destruct_frames'_stmt in FR1; apply FR1
    | apply destruct_frames'_stmt in FR2; apply FR2 ].

    apply AAIf; [ apply IHq1 | apply IHq2 ]; try assumption; solve
    [ apply destruct_frames'_stmt in FR1; apply FR1
    | apply destruct_frames'_stmt in FR2; apply FR2 ].

    apply AARep. apply IHq; try assumption.
      apply destruct_frames'_stmt in FR1; apply FR1.
      apply destruct_frames'_stmt in FR2; apply FR2.
Qed.

Theorem frames_prog_impl:
  forall P Q p (M1: monotonic' P) (FR1: frames'_prog P p) (FR2: frames_prog Q p),
  frames_prog (fun hs => P hs -> Q hs) p.
Proof.
  intros. intros s a. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames_stmt_impl; assumption.
    exact I.
Qed.

Theorem frames'_prog_impl:
  forall P Q p (M1: monotonic' P) (FR1: frames'_prog P p) (FR2: frames'_prog Q p),
  frames'_prog (fun hs => P hs -> Q hs) p.
Proof.
  intros. intros s a. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames'_stmt_impl; assumption.
    exact I.
Qed.

Corollary frames_stmt_not:
  forall P q (M: monotonic' P) (FR: frames'_stmt P q),
  frames_stmt (fun hs => ~ P hs) q.
Proof.
  intros. apply frames_stmt_impl. assumption. assumption. apply frames_stmt_hfalse.
Qed.

Corollary frames'_stmt_not:
  forall P q (M: monotonic' P) (FR: frames'_stmt P q),
  frames'_stmt (fun hs => ~ P hs) q.
Proof.
  intros. apply frames'_stmt_impl. assumption. assumption. apply frames'_stmt_hfalse.
Qed.

Corollary frames_prog_not:
  forall P p (M: monotonic' P) (FR: frames'_prog P p),
  frames_prog (fun hs => ~ P hs) p.
Proof.
  intros. apply frames_prog_impl. assumption. assumption. apply frames_prog_hfalse.
Qed.

Corollary frames_prog'_not:
  forall P p (M: monotonic' P) (FR: frames'_prog P p),
  frames'_prog (fun hs => ~ P hs) p.
Proof.
  intros. apply frames'_prog_impl. assumption. assumption. apply frames'_prog_hfalse.
Qed.

End PICINAE_SLOGIC.


Module PicinaeSLogic (IL: PICINAE_IL) <: PICINAE_SLOGIC IL.
  Include PICINAE_SLOGIC IL.
End PicinaeSLogic.




(* Theorems about monotonicity of properties: *)

Theorem mono_sep:
  forall V P Q (M1: monotonic P) (M2: monotonic Q), monotonic (sepconj V P Q).
Proof.
  unfold monotonic. intros. destruct H as [dom [P1 Q1]]. exists dom. split.
    eapply M1; [|eassumption]. apply resths_mono_r. assumption.
    eapply M2; [|eassumption]. apply resths_mono_r. assumption.
Qed.

Theorem mono_htrue: forall A B, monotonic (@htrue (A -> option B)).
Proof. unfold htrue,monotonic. intros. assumption. Qed.

Theorem mono_hfalse: forall A B, monotonic (@hfalse (A -> option B)).
Proof. unfold hfalse,monotonic. intros. assumption. Qed.

(* Only tautological hprops are monotonic, since enlarging a store could add
   unsatisfactory heaps to its co-domain.  It is therefore not useful to prove
   any sufficiency conditions for store-monotonicity of hprops. *)
Remark mono_hprop_useless:
  forall V P, monotonic (hprop V P) -> (forall h, hprop V P h).
Proof.
  intros V P M h. apply (M (fun _ => None)).
    intros x y H. discriminate.
    intros v m w H. discriminate.
Qed.

(* Only contradictory pointsto properties are monotonic, since pointsto only
   accepts heaps with singleton domains.  It is therefore not useful to prove
   sufficiency conditions for store-monotonicity for pointsto properties. *)
Remark mono_pointsto_useless:
  forall a Q, monotonic (pointsto a Q) -> (forall h, ~ pointsto a Q h).
Proof.
  intros a Q M h PT.
  assert (h ⊆ update h (N.succ a) (Some 0)).
    unfold update. simpl. intros x y H. destruct (N.eq_dec x a).
      subst x. destruct (N.eq_dec a (N.succ a)).
        exfalso. eapply N.neq_succ_diag_l. symmetry. eassumption.
        assumption.
      contradict n. specialize (PT x). rewrite H in PT. apply PT.
  unfold monotonic in M. apply M in H.
    specialize (H (N.succ a)). rewrite update_updated in H. eapply N.neq_succ_diag_l. apply H.
    apply PT.
Qed.

(* emp is not monotonic because enlarging a store could add non-empty heaps. *)
Remark mono_emp_false: ~ monotonic emp.
Proof.
  intro.
  assert (H': (fun (_:addr) => None) ⊆ (fun _ => Some 0)). discriminate.
  unfold monotonic,emp in H. apply H in H'. discriminate. reflexivity. exact 0.
Qed.

Theorem mono_impl:
  forall {A B} (P Q: (A -> option B) -> Prop) (M1: monotonic' P) (M2: monotonic Q),
  monotonic (fun f => P f -> Q f).
Proof.
  unfold monotonic. intros. eapply M2.
    eassumption.
    apply H. eapply M1. eassumption. assumption.
Qed.

Corollary mono_not:
  forall {A B} (P: (A -> option B) -> Prop) (M: monotonic' P),
  monotonic (fun f => ~ P f).
Proof.
  intros. apply mono_impl. assumption. apply mono_hfalse.
Qed.

Theorem mono_sepimp:
  forall P Q (M: monotonic Q), monotonic (sepimp P Q).
Proof.
  intros. intros h1 h2 SS H h' DJ PRE. eapply M.
    apply updateall_mono. eassumption.
    apply H.
      eapply hdisj_mono. eassumption. assumption.
      assumption.
Qed.


(* Dual results for monotonic': *)

Theorem mono'_sep:
  forall V P Q (M1: monotonic' P) (M2: monotonic' Q), monotonic' (sepconj V P Q).
Proof.
  unfold monotonic'. intros. destruct H as [dom [P1 Q1]]. exists dom. split.
    eapply M1; [|eassumption]. apply resths_mono_r. assumption.
    eapply M2; [|eassumption]. apply resths_mono_r. assumption.
Qed.

Theorem mono'_htrue: forall A B, monotonic' (@htrue (A -> option B)).
Proof. unfold htrue,monotonic'. intros. assumption. Qed.

Theorem mono'_hfalse: forall A B, monotonic' (@hfalse (A -> option B)).
Proof. unfold hfalse,monotonic'. intros. assumption. Qed.

Theorem mono'_hprop: forall V P, monotonic' (hprop V P).
Proof. unfold hprop,monotonic'. intros. eapply H. apply SS. eassumption. Qed.

(* Only contradictory pointsto properties are monotonic', since pointsto only
   accepts heaps with singleton domains.  It is therefore not useful to prove
   any sufficiency properties for monotonic' of pointsto. *)
Remark mono'_pointsto_useless:
  forall a Q, monotonic' (pointsto a Q) -> (forall h, ~ pointsto a Q h).
Proof.
  intros a Q M h PT.
  assert ((fun _ => None) ⊆ h). intros x y H. discriminate.
  unfold monotonic' in M. apply M in H.
    specialize (H a). simpl in H. apply H. reflexivity.
    apply PT.
Qed.

Theorem mono'_emp: monotonic' emp.
Proof.
  unfold monotonic', emp. intros. specialize (SS a). destruct (h2 a).
    specialize (H a). rewrite (SS n) in H. assumption. reflexivity.
    reflexivity.
Qed.

Theorem mono'_impl:
  forall {A B} (P Q: (A -> option B) -> Prop) (M1: monotonic P) (M2: monotonic' Q),
  monotonic' (fun f => P f -> Q f).
Proof.
  unfold monotonic'. intros. eapply M2.
    eassumption.
    apply H. eapply M1. eassumption. assumption.
Qed.

Corollary mono'_not:
  forall {A B} (P: (A -> option B) -> Prop) (M: monotonic P),
  monotonic' (fun f => ~ P f).
Proof.
  intros. apply mono'_impl. assumption. apply mono'_hfalse.
Qed.

(* TODO: What conditions are sufficient for monotonic' of sepimp?
   For non-contradictory sepimp, we at least need P -> Q: *)
Remark mono'_sepimp_impl:
  forall P Q h0 (NC: sepimp P Q h0), monotonic' (sepimp P Q) -> (forall h, P h -> Q h).
Proof.
  intros P Q h0 NC M h Ph.
  unfold monotonic' in M. apply M with (h2 := fun _ => None) in NC.
    replace h with (updateall (fun _ => None) h).
      apply NC. left. reflexivity. assumption.
      extensionality a. unfold updateall. destruct (h a); reflexivity.
    discriminate.
Qed.
(* Monotonicity of P or Q is too much, since that makes non-contradictory
   sepimp tautological: *)
Remark mono'_sepimp_tautological:
  forall P Q h0 (NC: sepimp P Q h0) (M: monotonic P \/ monotonic Q),
  monotonic' (sepimp P Q) -> (forall h, sepimp P Q h).
Proof.
  intros P Q h0 NC M M' h h' DJ Ph'. destruct M as [M|M].
    eapply mono'_sepimp_impl; try eassumption. eapply M. apply subset_updateall. assumption.
    eapply M. apply subset_updateall. eapply mono'_sepimp_impl; eassumption.
Qed.
(* But monotonicity' of P and Q is insufficient. Counter-example: *)
Example mono'_sepimp_counterexample:
  exists P Q h1 h2, monotonic' P /\ monotonic' Q /\
    sepimp P Q h1 /\ h2 ⊆ h1 /\ ~sepimp P Q h2.
Proof.
  exists (fun h => forall a, h a = None \/ h a = Some 0),
         (fun h => forall a, h a = None \/ h a = Some 1),
         (fun _ => Some 1), (fun _ => None).
  repeat split.
    unfold monotonic'. intros. specialize (SS a). destruct (h2 a).
      right. destruct (H a).
        rewrite (SS n) in H0 by reflexivity. discriminate.
        rewrite <- H0. symmetry. apply SS. reflexivity.
      left. reflexivity.
    unfold monotonic'. intros. specialize (SS a). destruct (h2 a).
      right. destruct (H a).
        rewrite (SS n) in H0 by reflexivity. discriminate.
        rewrite <- H0. symmetry. apply SS. reflexivity.
      left. reflexivity.
    unfold sepimp,updateall,hdisj. intros. right. destruct (DJ a).
      discriminate.
      rewrite H0. reflexivity.
    discriminate.
    intro. edestruct H with (a:=0).
      intro. left. reflexivity.
      intro. right. reflexivity.
      discriminate.
      discriminate.
Qed.
(* Tentative conclusion: monotonic' of (sepimp P Q) doesn't seem to have any
   general, obvious sufficiency condition on P and/or Q.  Proofs are specific
   to each P and Q. *)
