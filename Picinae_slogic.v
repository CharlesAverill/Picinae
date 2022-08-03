(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2022 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
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
Inductive hval := HVN (n:N) (w:bitwidth) | HVM (m: addr -> option N) (w:bitwidth).
Definition to_heap (m: addr -> N) a := Some (m a).
Definition to_hval (u:value) :=
  match u with VaN n w => HVN n w | VaM m w => HVM (to_heap m) w end.

Definition hstore (V:Type) := V -> hval.
Definition to_hstore {V} s (v:V) := to_hval (s v).

(* restriction of heapy values and heapy stores to a given domain: *)
Definition resthv {A} (h:heap A) (hu:hval) :=
  match hu with HVN n w => HVN n w | HVM h' w => HVM (resth h h') w end.
Definition resths {V A} (h:heap A) (hs:hstore V) v := resthv h (hs v).


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
  fun hs => forall v m w (SV: hs v = HVM m w), P m.

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


(* update-preserving heapy-store-properties are preserved by updating var v to
   heapy value hu. *)
Definition upd_pres {V} {_:EqDec V} (R: hsprop V) hs hu v :=
  R hs -> R (update hs v hu).


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
  intros. extensionality a. unfold resths. rewrite resthv_hdom. reflexivity.
Qed.

Lemma resths_assoc:
  forall {V A B} (h1: heap A) (h2: heap B) (hs:hstore V),
  resths h1 (resths h2 hs) = resths (resth h1 h2) hs.
Proof.
  intros. extensionality v. unfold resths. rewrite resthv_assoc. reflexivity.
Qed.

Lemma to_hstore_update {V} {ED:EqDec V}:
  forall s (v:V) u, to_hstore (s[v:=u]) = (to_hstore s)[v := to_hval u].
Proof.
  intros. extensionality v0. unfold to_hstore,update. destruct (v0 == v); reflexivity.
Qed.

Lemma resths_update {V} {ED:EqDec V}:
  forall {A} (h:heap A) hs (v:V) hu, resths h (hs[v:=hu]) = (resths h hs)[v := resthv h hu].
Proof.
  intros. extensionality v0. unfold resths,update. destruct (v0 == v); reflexivity.
Qed.



Module Type PICINAE_SLOGIC_DEFS (IL: PICINAE_IL).

Import IL.

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
| HMM m w v m' (SV: s v = VaM m' w) (FR: forall a, h a = None -> m a = m' a):
    hmodels s h (VaM m w).

Definition hmodels_store (h:hdomain) (s s':store) :=
  forall v, hmodels s h (s' v).


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

End PICINAE_SLOGIC_DEFS.



Module Type PICINAE_SLOGIC (IL: PICINAE_IL).

Import IL.
Include PICINAE_SLOGIC_DEFS IL.

(* Helper lemmas for breaking "frames" hypotheses down into their premises: *)

Parameter destruct_frames_stmt:
  forall R q (FR: frames_stmt R q),
  match q with
  | Nop | Jmp _ | Exn _ => True
  | Move v _ => forall s (h:hdomain) hu (HM: hmodels s (hopp h) hu), upd_pres R (resths h (to_hstore s)) (resthv h (to_hval hu)) v
  | Seq q1 q2 => frames_stmt R q1 /\ frames_stmt R q2
  | Rep _ q1 => frames_stmt R q1
  | If _ q1 q2 => frames_stmt R q1 /\ frames_stmt R q2
  end.

Parameter destruct_frames'_stmt:
  forall R q (FR: frames'_stmt R q),
  match q with
  | Nop | Jmp _ | Exn _ => True
  | Move v _ => forall s (h:hdomain) hu, upd_pres R (resths h (to_hstore s)) (resthv h (to_hval hu)) v
  | Seq q1 q2 => frames'_stmt R q1 /\ frames'_stmt R q2
  | Rep _ q1 => frames'_stmt R q1
  | If _ q1 q2 => frames'_stmt R q1 /\ frames'_stmt R q2
  end.


(* The IL semantics obey the modeling relation: *)

Parameter hmodels_refl:
  forall h s, hmodels_store h s s.

Parameter hmodels_trans:
  forall h s1 s2 s3, hmodels_store h s1 s2 -> hmodels_store h s2 s3 ->
  hmodels_store h s1 s3.

Parameter hmodels_mono:
  forall s h1 h2 u (SS: h1 ⊆ h2) (HM: hmodels s h1 u), hmodels s h2 u.

Parameter hmodels_exp:
  forall h s e u (E: eval_exp h s e u),
  hmodels s h u.

Parameter hmodels_stmt:
  forall h s q s' x (XS: exec_stmt h s q s' x),
  hmodels_store h s s'.

Parameter hmodels_prog:
  forall h p a s n s' x (XP: exec_prog h p a s n s' x),
  hmodels_store h s s'.


(* If R frames q, then executing q preserves R. *)

Parameter frames_rep:
  forall R e q (FR: frames_stmt R q), frames_stmt R (Seq q (Rep e q)).

Parameter framed_stmt:
  forall {A} (R: hsprop var) (h:heap A) s q s' x (FR: frames_stmt R q)
         (XS: exec_stmt (hopp h) s q s' x)
         (HS: hmodels_store (hopp h) s s') (PRE: R (resths h (to_hstore s))),
  R (resths h (to_hstore s')).

Parameter framed_prog:
  forall {A} (R: hsprop var) (h:heap A) p a s n s' x (FR: frames_prog R p)
         (XP: exec_prog (hopp h) p a s n s' x)
         (HS: hmodels_store (hopp h) s s') (PRE: R (resths h (to_hstore s))),
  R (resths h (to_hstore s')).


(* Main result: The frame rule of separation logic is sound.  In particular,
   if {P}q{Q} holds, and if R frames q, then {P*R}q{Q*R} holds. *)

Parameter stmt_frame:
  forall q (P Q R: hsprop var) (FR: frames_stmt R q)
         (HT: htrip_stmt P q Q),
  htrip_stmt (sep P R) q (sep Q R).

Parameter prog_frame:
  forall p a n (P Q R: hsprop var) (FR: frames_prog R p)
         (HT: htrip_prog P p a n Q),
  htrip_prog (sep P R) p a n (sep Q R).


(* At this point we have our main result, but it requires users to prove that
   R frames q in order to use it.  We here prove some general sufficiency
   conditions to help users prove this meta-property. *)

Parameter upd_pres_sep:
  forall P Q hs hu v
         (UP1: forall (h:hdomain), upd_pres P (resths h hs) (resthv h hu) v)
         (UP2: forall (h:hdomain), upd_pres Q (resths h hs) (resthv h hu) v),
  upd_pres (sep P Q) hs hu v.

(* P*Q (universally-)frames q if P and Q both (universally-)frame q. *)
Parameter frames_stmt_sep:
  forall P Q q (FR1: frames_stmt P q) (FR2: frames_stmt Q q),
  frames_stmt (sep P Q) q.

Parameter frames'_stmt_sep:
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames'_stmt Q q),
  frames'_stmt (sep P Q) q.

Parameter frames_prog_sep:
  forall P Q p (FR1: frames_prog P p) (FR2: frames_prog Q p),
  frames_prog (sep P Q) p.

Parameter frames'_prog_sep:
  forall P Q p (FR1: frames'_prog P p) (FR2: frames'_prog Q p),
  frames'_prog (sep P Q) p.

(* htrue and hfalse (universally-)frame everything. *)
Parameter frames_stmt_htrue: forall q, frames_stmt htrue q.
Parameter frames'_stmt_htrue: forall q, frames'_stmt htrue q.
Parameter frames_prog_htrue: forall p, frames_prog htrue p.
Parameter frames'_prog_htrue: forall p, frames'_prog htrue p.
Parameter frames_stmt_hfalse: forall q, frames_stmt hfalse q.
Parameter frames'_stmt_hfalse: forall q, frames'_stmt hfalse q.
Parameter frames_prog_hfalse: forall p, frames_prog hfalse p.
Parameter frames'_prog_hfalse: forall p, frames'_prog hfalse p.

(* To prove that R (universally-)frames q, it sufficies to prove that R is
   update-preserving for all possible stores. *)
Parameter frames_stmt_anystore:
  forall R q, (forall s (h:hdomain) u v (HM: hmodels s (hopp h) u), upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u)) v) ->
  frames_stmt R q.

Parameter frames'_stmt_anystore:
  forall R q, (forall s (h:hdomain) u v, upd_pres R (resths h (to_hstore s)) (resthv h (to_hval u)) v) ->
  frames'_stmt R q.

(* It follows that all heap-properties frame everything. *)
Parameter frames_stmt_hprop: forall R q, frames_stmt (hprop var R) q.
Parameter frames_prog_hprop: forall R p, frames_prog (hprop var R) p.

(* (P -> Q) frames q if P universally-frames q and Q frames q. *)
Parameter frames_stmt_impl:
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames_stmt Q q),
  frames_stmt (fun hs => P hs -> Q hs) q.

Parameter frames'_stmt_impl:
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames'_stmt Q q),
  frames'_stmt (fun hs => P hs -> Q hs) q.

Parameter frames_prog_impl:
  forall P Q p (FR1: frames'_prog P p) (FR2: frames_prog Q p),
  frames_prog (fun hs => P hs -> Q hs) p.

Parameter frames'_prog_impl:
  forall P Q p (FR1: frames'_prog P p) (FR2: frames'_prog Q p),
  frames'_prog (fun hs => P hs -> Q hs) p.

(* ~P frames and universally-frames q if P universally-frames q. *)
Parameter frames_stmt_not:
  forall P q (FR: frames'_stmt P q),
  frames_stmt (fun hs => ~ P hs) q.

Parameter frames'_stmt_not:
  forall P q (FR: frames'_stmt P q),
  frames'_stmt (fun hs => ~ P hs) q.

Parameter frames_prog_not:
  forall P p (FR: frames'_prog P p),
  frames_prog (fun hs => ~ P hs) p.

Parameter frames_prog'_not:
  forall P p (FR: frames'_prog P p),
  frames'_prog (fun hs => ~ P hs) p.

End PICINAE_SLOGIC.



Module PicinaeSLogic (IL: PICINAE_IL) : PICINAE_SLOGIC IL.

Import IL.
Include PICINAE_SLOGIC_DEFS IL.
Module PTheory := PicinaeTheory IL.
Import PTheory.

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

Lemma hmodels_refl:
  forall h s, hmodels_store h s s.
Proof.
  intros h s v. destruct (s v) eqn:SV.
    apply HMN.
    eapply HMM. exact SV. reflexivity.
Qed.

Lemma hmodels_trans:
  forall h s1 s2 s3, hmodels_store h s1 s2 -> hmodels_store h s2 s3 ->
  hmodels_store h s1 s3.
Proof.
  intros h s1 s2 s3 H1 H2 v.
  specialize (H2 v). inversion H2.
    apply HMN.
    specialize (H1 v0). inversion H1.
      rewrite SV in H3. discriminate.
      rewrite SV in H3. inversion H3. subst. eapply HMM. eassumption.
        intros. rewrite (FR a H). apply FR0. assumption.
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
    destruct (s v) eqn:SV; econstructor. exact SV. reflexivity.

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
      subst v0. rewrite update_updated in SV. subst. apply IHe1 in E1. inversion E1; subst.
        eapply HMM. eassumption. intros. rewrite (FR a H). apply FR0. assumption.
      eapply HMM. rewrite update_frame in SV by assumption. eassumption. assumption.

    destruct n1; [ apply IHe3 | apply IHe2 ]; assumption.
Qed.

Theorem hmodels_stmt:
  forall h s q s' x (XS: exec_stmt h s q s' x),
  hmodels_store h s s'.
Proof.
  intros. dependent induction XS; intros; try solve [ apply hmodels_refl | assumption ].
    intro v'. destruct ((s[v:=u]) v') eqn:SV'. apply HMN. destruct (vareq v' v).
      subst v'. rewrite update_updated in SV'. subst. eapply hmodels_exp; eassumption.
      rewrite update_frame in SV' by assumption. eapply HMM. eassumption. reflexivity.
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
  specialize (H (fun _ => VaN 0 0) (hdom h) (VaM (fun a => match h a with None => 0 | Some n => n end) 0)).
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

Theorem frames_stmt_impl:
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames_stmt Q q),
  frames_stmt (fun hs => P hs -> Q hs) q.
Proof.
  induction q; intros; unfold frames_stmt; intros; try solve [ constructor ].

    apply AAMove. unfold upd_pres. intros.
    apply destruct_frames'_stmt in FR1. apply destruct_frames_stmt in FR2.
    apply FR2. assumption. apply H.
    replace (resths _ _) with (resths h (to_hstore (s[v:=u])) [v := resthv h (to_hval (s v))]).
      apply FR1. rewrite to_hstore_update, resths_update. assumption.
      rewrite to_hstore_update, resths_update, update_cancel. extensionality v0. destruct (vareq v0 v).
        subst v0. rewrite update_updated. unfold to_hstore, resths. reflexivity.
        rewrite update_frame by assumption. reflexivity.

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
  forall P Q q (FR1: frames'_stmt P q) (FR2: frames'_stmt Q q),
  frames'_stmt (fun hs => P hs -> Q hs) q.
Proof.
  induction q; intros; unfold frames'_stmt; intros; try solve [ constructor ].

    apply AAMove. unfold upd_pres. intros.
    apply destruct_frames'_stmt in FR1. apply destruct_frames'_stmt in FR2.
    apply FR2. apply H.
    replace (resths _ _) with (resths h (to_hstore (s[v:=u])) [v := resthv h (to_hval (s v))]).
      apply FR1. rewrite to_hstore_update, resths_update. assumption.
      rewrite to_hstore_update, resths_update, update_cancel. extensionality v0. destruct (vareq v0 v).
        subst v0. rewrite update_updated. unfold to_hstore, resths. reflexivity.
        rewrite update_frame by assumption. reflexivity.

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
  forall P Q p (FR1: frames'_prog P p) (FR2: frames_prog Q p),
  frames_prog (fun hs => P hs -> Q hs) p.
Proof.
  intros. intros s a. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames_stmt_impl; assumption.
    exact I.
Qed.

Theorem frames'_prog_impl:
  forall P Q p (FR1: frames'_prog P p) (FR2: frames'_prog Q p),
  frames'_prog (fun hs => P hs -> Q hs) p.
Proof.
  intros. intros s a. specialize (FR1 s a). specialize (FR2 s a). destruct (p s a) as [(sz,q)|].
    apply frames'_stmt_impl; assumption.
    exact I.
Qed.

Corollary frames_stmt_not:
  forall P q (FR: frames'_stmt P q),
  frames_stmt (fun hs => ~ P hs) q.
Proof.
  intros. apply frames_stmt_impl. assumption. apply frames_stmt_hfalse.
Qed.

Corollary frames'_stmt_not:
  forall P q (FR: frames'_stmt P q),
  frames'_stmt (fun hs => ~ P hs) q.
Proof.
  intros. apply frames'_stmt_impl. assumption. apply frames'_stmt_hfalse.
Qed.

Corollary frames_prog_not:
  forall P p (FR: frames'_prog P p),
  frames_prog (fun hs => ~ P hs) p.
Proof.
  intros. apply frames_prog_impl. assumption. apply frames_prog_hfalse.
Qed.

Corollary frames_prog'_not:
  forall P p (FR: frames'_prog P p),
  frames'_prog (fun hs => ~ P hs) p.
Proof.
  intros. apply frames'_prog_impl. assumption. apply frames'_prog_hfalse.
Qed.

End PicinaeSLogic.
