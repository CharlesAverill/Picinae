(* PARTIAL handoff: first full build failed. Unverified declarations are
   aborted, never exported as assumed theorems. No second Astra compile. *)
(* Finite ring refinement of the two checked FreeRTOS list IL transitions.
   Initial author: OpenAI gpt-6-astra, xhigh/default, one-shot.
   Final proof producer: unset until a successful full kernel check.

   Official FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Unchanged generated maps / layout: Examples/FreeRTOS/{abi.json,
   vListInsertEnd_armv6m.v,uxListRemove_armv6m.v}. Checked r03 prerequisite
   7e49f57f76af3afaedf1c2b7bd5cf810cf4efef2 and r04 prerequisite
   18dcb8cb928ba1e712aaa9aa8bb8f43aef51910f; shared r00 memory kit.

   SPECIFICATION: List_t occupies 20 bytes at L. Its embedded 12-byte
   sentinel S=L+8 has maximum value and closes a finite sequence of distinct
   real 20-byte ListItem_t objects. Every original next/previous/container,
   opaque value/owner, header count, and cursor is represented in byte memory.
   All objects are nonnull, aligned and nonwrapping; real objects are mutually
   separate and separate from the HEADER, never from a separately allocated
   sentinel. In particular empty/singleton and equal-neighbor cases are legal.
   V and O are ghost maps of opaque 32-bit contents, not executable code.

   Insertion is at a split xs=left++right whose head (sentinel for []) is the
   current index. It inserts P BEFORE that index, preserving cursor and opaque
   fields. The mathematical count bound length(xs)+1<2^32 explicitly excludes
   wraparound; the local r03 contract itself still uses modular increment.
   Removal deletes the selected member at xs=left++P::right. If P is current,
   index becomes the predecessor (possibly sentinel); otherwise unchanged.
   Removed links/value/owner remain original and container becomes zero.

   AAPCS32 R0=L,R1=P for insertion; R0=P on removal entry, count-1 on exit.
   Permissions explicitly cover all bytes of the header and real objects,
   plus fresh P for insertion. Register frames and finite program typing/nwc
   are inherited from checked r03/r04, as are their exit/invariant definitions.
   Corollaries assume an actual execution reaching BX (0x70 / 0xbc) from
   entry 0x5c / 0xa0 without a previous exit. No trace existence, termination,
   IRQ/concurrency, scheduler, hardware, or binary/lifter soundness is claimed.
   No additional CPU tunables, calls, or result contracts are assumed.
 *)
Require Import Picinae_armv6m armv6m_list_model.
Require Import vListInsertEnd_armv6m uxListRemove_armv6m.
Require Import armv6m_vListInsertEnd_proof armv6m_uxListRemove_proof.
From Stdlib Require Import NArith Lia List.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition ring_sentinel L := L+8.
Fixpoint ring_last (previous:N) (xs:list N) : N :=
  match xs with [] => previous | p::ys => ring_last p ys end.
Fixpoint ring_chain (m L previous:N) (xs:list N) (V O:N->N) : Prop :=
  match xs with
  | [] => True
  | p::ys => item_contents m p (V p) (hd (ring_sentinel L) ys)
                  previous (O p) L /\ ring_chain m L p ys V O
  end.
Definition ring_geometry (L:N) (xs:list N) :=
  NoDup (L::xs) /\
  (forall p, In p (L::xs) -> object32 p 20) /\
  (forall p q, In p (L::xs) -> In q (L::xs) -> p<>q ->
     p+20<=q \/ q+20<=p).
Record ring_rep (m L:N) (xs:list N) (idx:N) (V O:N->N) : Prop := {
  ring_geom : ring_geometry L xs;
  ring_count_bound : N.of_nat (length xs)<2^32;
  ring_cursor : idx=ring_sentinel L \/ In idx xs;
  ring_header : list_header m L (N.of_nat (length xs)) idx;
  ring_front : field32 m L 12=hd (ring_sentinel L) xs;
  ring_back : field32 m L 16=ring_last (ring_sentinel L) xs;
  ring_nodes : ring_chain m L (ring_sentinel L) xs V O
}.
Definition ring_fresh m L xs P (V O:N->N) :=
  object32 P 20 /\ ~ In P (L::xs) /\
  (forall q, In q (L::xs) -> P+20<=q \/ q+20<=P) /\
  field32 m P 0=V P /\ field32 m P 12=O P.
Definition ring_permissions (s:store) L xs :=
  forall p, In p (L::xs) ->
    MemAcc mem_readable s p 32 20 /\ MemAcc mem_writable s p 32 20.
Definition ring_insert_permissions (s:store) L xs P :=
  ring_permissions s L xs /\
  MemAcc mem_readable s P 32 20 /\ MemAcc mem_writable s P 32 20.
Definition ring_outside_frame m m' L xs :=
  forall a, (forall p, In p (L::xs) -> separate32 a 1 p 20) ->
    getmem 32 LittleE 1 m' a=getmem 32 LittleE 1 m a.
Definition ring_remove_cursor idx P previous :=
  if idx =? P then previous else idx.

Lemma ring_last_app : forall a xs ys,
  ring_last a (xs++ys)=ring_last (ring_last a xs) ys.
Proof. intros a xs. revert a. induction xs; intros; cbn; auto. Qed.
Check ring_last_app.
Print Assumptions ring_last_app.
Lemma ring_last_member : forall a xs, ring_last a xs=a \/ In (ring_last a xs) xs.
Proof.
  intros a xs. revert a. induction xs as [|p xs IH]; intros a; cbn; auto.
  destruct (IH p) as [EQ|IN]; right; auto.
Qed.
Check ring_last_member.
Print Assumptions ring_last_member.
Lemma ring_hd_member : forall (a:N) (xs:list N), hd a xs=a \/ In (hd a xs) xs.
Proof. intros a [|p xs]; cbn; auto. Qed.
Lemma ring_count_insert : forall (left right:list N) P,
  N.of_nat (length (left++P::right))=N.of_nat (length (left++right))+1.
Proof. intros. rewrite !app_length. cbn. rewrite !Nat2N.inj_add, Nat2N.inj_succ. lia. Qed.
Lemma ring_count_remove : forall (left right:list N) P,
  0<N.of_nat (length (left++P::right)) /\
  N.of_nat (length (left++right))=N.of_nat (length (left++P::right))-1.
Proof. intros. rewrite ring_count_insert. lia. Qed.
Lemma ring_members_insert : forall (left right:list N) P q,
  In q (left++P::right) <-> q=P \/ In q (left++right).
Proof. intros. rewrite !in_app_iff. cbn. intuition congruence. Qed.
Lemma ring_members_remove : forall (left right:list N) P q,
  NoDup (left++P::right) ->
  (In q (left++right) <-> In q (left++P::right) /\ q<>P).
Proof.
  intros left right P q ND.
  apply NoDup_remove in ND. destruct ND as [ND NOT].
  rewrite ring_members_insert. split.
  - intro IN. split; [auto|]. intro EQ. subst. contradiction.
  - intros [[EQ|IN] NE]; [contradiction|assumption].
Qed.
Lemma ring_nodup_insert : forall (left right:list N) P,
  NoDup (left++right) -> ~In P (left++right) -> NoDup (left++P::right).
Proof.
  intros left. induction left as [|q left IH]; intros right P ND NOT; cbn in *.
  - constructor; assumption.
  - inversion ND as [|q' xs NQ NX]; subst. constructor.
    + rewrite ring_members_insert. intros [EQ|IN].
      * subst q. apply NOT. left. reflexivity.
      * exact (NQ IN).
    + apply IH; [exact NX|]. intro IN. apply NOT. right. exact IN.
Qed.
Lemma ring_regions_separate : forall L xs p q,
  ring_geometry L xs -> In p (L::xs) -> In q (L::xs) -> p<>q ->
  separate32 p 20 q 20.
Proof.
  intros L xs p q [_ [OBJ SEP]] IP IQ NE.
  apply ranges32_separate.
  - exact (proj2 (proj2 (OBJ p IP))).
  - exact (proj2 (proj2 (OBJ q IQ))).
  - exact (SEP p q IP IQ NE).
Qed.
Lemma ring_object_fields_separate : forall L xs p q i j,
  ring_geometry L xs -> In p (L::xs) -> In q (L::xs) ->
  In i fields20 -> In j fields20 -> p<>q \/ i<>j ->
  separate32 (p+i) 4 (q+j) 4.
Proof.
  intros L xs p q i j GEO IP IQ II IJ NE.
  destruct (N.eq_dec p q) as [EQ|NEQ].
  - subst q. apply fields20_separate.
    + exact (proj2 (proj2 (proj2 ((proj1 (proj2 GEO)) p IP)))).
    + exact II.
    + exact IJ.
    + tauto.
  - apply noverlap_index_index with (len1:=20) (len2:=20).
    + exact (ring_regions_separate L xs p q GEO IP IQ NEQ).
    + unfold fields20 in II. repeat destruct II as [<-|II]; try contradiction; lia.
    + unfold fields20 in IJ. repeat destruct IJ as [<-|IJ]; try contradiction; lia.
Qed.
Lemma ring_fresh_geometry : forall m L left right P V O,
  ring_geometry L (left++right) -> ring_fresh m L (left++right) P V O ->
  ring_geometry L (left++P::right).
Proof.
  intros m L left right P V O [ND [OBJ SEP]] [PO [NOT [PS REST]]].
  assert (NEW:forall q, In q (L::left++P::right) <->
    q=P \/ In q (L::left++right)).
  { intro q. exact (ring_members_insert (L::left) right P q). }
  split.
  - change (NoDup ((L::left)++P::right)).
    apply ring_nodup_insert; assumption.
  - split.
    + intros q IN. apply NEW in IN. destruct IN as [->|IN].
      * exact PO.
      * exact (OBJ q IN).
    + intros q r IQ IR NE. apply NEW in IQ, IR.
      destruct IQ as [->|IQ]; destruct IR as [->|IR].
      * contradiction.
      * exact (PS r IR).
      * destruct (PS q IQ); auto.
      * exact (SEP q r IQ IR NE).
Qed.

(* A byte-range permission includes each contained word. *)
Lemma ring_permission_word : forall (perm:store->addr->Prop) s p off,
  MemAcc perm s p 32 20 -> off+4<=20 -> MemAcc perm s (p+off) 32 4.
Proof.
  unfold MemAcc. intros perm s p off ACC B i I.
  replace (p+off+i) with (p+(off+i)) by lia.
  apply ACC. lia.
Qed.

(* Split-independent topology query. Both sentinel and real cursor cases
   are included; right=[] selects the sentinel. *)
Lemma ring_chain_suffix : forall m L left right a V O,
  ring_chain m L a (left++right) V O ->
  ring_chain m L (ring_last a left) right V O.
Proof.
  intros m L left. induction left as [|p left IH]; intros; cbn in *.
  - assumption.
  - apply IH. tauto.
Qed.
Lemma ring_chain_boundary : forall m L left right a V O,
  left<>[] -> ring_chain m L a (left++right) V O ->
  field32 m (ring_last a left) 4=hd (ring_sentinel L) right.
Proof.
  intros m L left. induction left as [|p left IH]; intros right a V O NE CH.
  - contradiction.
  - destruct left as [|q left].
    + exact (proj1 (proj2 (proj1 CH))).
    + apply (IH right p V O); [discriminate|exact (proj2 CH)].
Qed.
Lemma ring_insert_links : forall m L left right idx V O,
  ring_rep m L (left++right) idx V O -> idx=hd (ring_sentinel L) right ->
  insert_end_links m L idx (ring_last (ring_sentinel L) left).
Proof.
  intros m L left right idx V O REP IDX.
  destruct REP as [G B C [COUNT [INDEX MAX]] FRONT BACK CH].
  split; [exact INDEX|]. rewrite IDX. clear IDX. split.
  - pose proof (ring_chain_suffix m L left right (ring_sentinel L) V O CH) as SUF.
    destruct right as [|q right].
    + cbn [hd]. rewrite app_nil_r in BACK.
      unfold ring_sentinel, field32. rewrite <- N.add_assoc. exact BACK.
    + exact (proj1 (proj2 (proj2 (proj1 SUF)))).
  - destruct left as [|p left].
    + cbn [ring_last app] in *. unfold ring_sentinel, field32.
      rewrite <- N.add_assoc. exact FRONT.
    + exact (ring_chain_boundary m L (p::left) right (ring_sentinel L) V O
        ltac:(discriminate) CH).
Qed.
Lemma ring_remove_original : forall m L left P right idx V O,
  ring_rep m L (left++P::right) idx V O ->
  list_remove_original m P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx.
Proof.
  intros m L left P right idx V O REP.
  destruct REP as [G B C [COUNT [INDEX MAX]] F BK CH].
  pose proof (proj1 (ring_chain_suffix m L left (P::right)
    (ring_sentinel L) V O CH)) as ITEM.
  destruct ITEM as [VAL [NEXT [PREV [OWNER CONT]]]].
  unfold list_remove_original, rm_read. unfold field32 in *.
  rewrite N.add_0_r in COUNT. repeat split; assumption.
Qed.

(* Link prefixes may be embedded in the header. These lemmas deliberately
   retain that alias rather than requiring a separately allocated sentinel. *)
Lemma ring_node_not_header : forall L xs p,
  ring_geometry L xs -> In p xs -> p<>L.
Proof.
  intros L xs p [ND _] IN EQ. subst p. inversion ND; contradiction.
Qed.
Lemma ring_node_not_sentinel : forall L xs p,
  ring_geometry L xs -> In p xs -> p<>ring_sentinel L.
Proof.
  intros L xs p G IN EQ.
  assert (NE:p<>L) by (exact (ring_node_not_header L xs p G IN)).
  pose proof ((proj2 (proj2 G)) p L (or_intror IN) (or_introl eq_refl) NE) as SEP.
  unfold ring_sentinel in EQ. clear - EQ SEP. destruct SEP; lia.
Qed.
Lemma ring_object_prefix : forall p,
  object32 p 20 -> object32 p 12.
Proof. intros p [NZ [AL [B END]]]. repeat split; try assumption; lia. Qed.
Lemma ring_sentinel_object : forall L,
  object32 L 20 -> object32 (ring_sentinel L) 12.
Proof.
  intros L [NZ [AL [B END]]]. unfold ring_sentinel.
  repeat split; lia.
Qed.
Lemma ring_link_object : forall L xs p,
  ring_geometry L xs -> (p=ring_sentinel L \/ In p xs) -> object32 p 12.
Proof.
  intros L xs p [_ [OBJ _]] [->|IN].
  - apply ring_sentinel_object. apply OBJ. left; reflexivity.
  - apply ring_object_prefix. apply OBJ. right; exact IN.
Qed.
Lemma ring_item_link_separate : forall L xs P q,
  ring_geometry L xs -> In P xs ->
  (q=ring_sentinel L \/ In q xs /\ q<>P) -> separate32 P 20 q 12.
Proof.
  intros L xs P q G IP [->|[IQ NE]].
  - unfold ring_sentinel. rewrite <- (N.add_0_r P) at 1.
    apply noverlap_index_index with (len1:=20) (len2:=20); try (clear; lia).
    apply (ring_regions_separate L xs P L G); cbn; auto.
    apply ring_node_not_header with (xs:=xs); assumption.
  - rewrite <- (N.add_0_r P) at 1. rewrite <- (N.add_0_r q) at 1.
    apply noverlap_index_index with (len1:=20) (len2:=20); try (clear; lia).
    apply (ring_regions_separate L xs P q G); cbn; auto; congruence.
Qed.

(* For each local word, choose its allocation base and field offset. *)
Ltac ring_field_sep G :=
  lazymatch type of G with ring_geometry ?L ?xs =>
    unfold ring_sentinel; rewrite <- ?N.add_assoc; rewrite ?N.add_0_r;
    lazymatch goal with |- separate32 ?a 4 ?b 4 =>
      let p := lazymatch a with ?q+?i => q | _ => a end in
      let i := lazymatch a with ?q+?i => i | _ => constr:(0) end in
      let q := lazymatch b with ?q+?j => q | _ => b end in
      let j := lazymatch b with ?q+?j => j | _ => constr:(0) end in
      let SEP := fresh "SEP" in
      assert (SEP:separate32 (p+i) 4 (q+j) 4) by
        (apply (ring_object_fields_separate L xs p q i j G);
          [cbn; tauto|cbn; tauto|cbn; tauto|cbn; tauto|intuition congruence]);
      rewrite ?N.add_0_r in SEP; exact SEP
    end
  end.

Lemma ring_insert_local_layout : forall L xs P I B,
  ring_geometry L xs -> In P xs ->
  (I=ring_sentinel L \/ In I xs /\ I<>P) ->
  (B=ring_sentinel L \/ In B xs /\ B<>P) -> insert_end_layout L P I B.
Proof.
  intros L xs P I B G IP II IB.
  assert (PL:P<>L) by (eapply ring_node_not_header; eassumption).
  assert (OL:object32 L 20) by (apply (proj1 (proj2 G)); cbn; auto).
  assert (OP:object32 P 20) by (apply (proj1 (proj2 G)); cbn; auto).
  unfold insert_end_layout. split; [exact OL|]. split; [exact OP|].
  split; [apply (ring_link_object L xs I G); tauto|].
  split; [apply (ring_link_object L xs B G); tauto|].
  split; [apply (ring_regions_separate L xs P L G); cbn; auto|].
  split; [apply (ring_item_link_separate L xs P I G IP II)|].
  split; [apply (ring_item_link_separate L xs P B G IP IB)|].
  destruct II as [->|[II INE]]; destruct IB as [->|[IB BNE]].
    all: try (assert (IL:I<>L) by (eapply ring_node_not_header; eassumption)).
    all: try (assert (BL:B<>L) by (eapply ring_node_not_header; eassumption)).
    all: cbn [insert_end_words insert_separate_words insert_apart_from];
      repeat split; try exact I;
      try solve [ring_field_sep G].
Qed.

Lemma ring_remove_local_layout : forall L xs P I B,
  ring_geometry L xs -> In P xs ->
  (I=ring_sentinel L \/ In I xs /\ I<>P) ->
  (B=ring_sentinel L \/ In B xs /\ B<>P) -> list_remove_layout P I B L.
Proof.
  intros L xs P I B G IP II IB.
  assert (PL:P<>L) by (eapply ring_node_not_header; eassumption).
  assert (OL:object32 L 20) by (apply (proj1 (proj2 G)); cbn; auto).
  assert (OP:object32 P 20) by (apply (proj1 (proj2 G)); cbn; auto).
  unfold list_remove_layout. split; [exact OP|]. split; [exact OL|].
  split; [apply (ring_link_object L xs I G); tauto|].
  split; [apply (ring_link_object L xs B G); tauto|].
  split; [apply (ring_regions_separate L xs P L G); cbn; auto|].
  split; [apply (ring_item_link_separate L xs P I G IP II)|].
  split; [apply (ring_item_link_separate L xs P B G IP IB)|].
  destruct II as [->|[II INE]]; destruct IB as [->|[IB BNE]].
  all: try (assert (IL:I<>L) by (eapply ring_node_not_header; eassumption)).
  all: try (assert (BL:B<>L) by (eapply ring_node_not_header; eassumption)).
  all: unfold rm_separated; intros i j BI BJ NE;
    assert (CI:i=0%nat \/ i=1%nat \/ i=2%nat \/ i=3%nat \/ i=4%nat \/
      i=5%nat \/ i=6%nat \/ i=7%nat \/ i=8%nat \/ i=9%nat) by lia;
    assert (CJ:j=0%nat \/ j=1%nat \/ j=2%nat \/ j=3%nat \/ j=4%nat \/
      j=5%nat \/ j=6%nat \/ j=7%nat \/ j=8%nat \/ j=9%nat) by lia;
    repeat destruct CI as [CI|CI]; subst i;
    repeat destruct CJ as [CJ|CJ]; subst j; try contradiction;
    cbn [rm_slot]; unfold ring_sentinel; rewrite <- ?N.add_assoc.
  all: ring_field_sep G.
Qed.
Lemma ring_link_fresh : forall m L left right P V O q,
  ring_fresh m L (left++right) P V O ->
  (q=ring_sentinel L \/ In q (left++right)) ->
  (q=ring_sentinel L \/ In q (left++P::right) /\ q<>P).
Proof.
  intros m L left right P V O q [_ [NOT _]] [EQ|IN]; [auto|].
  right. split; [apply ring_members_insert; auto|].
  intro EQ. subst q. apply NOT. right; exact IN.
Qed.
Lemma ring_link_remove : forall L left right P q,
  NoDup (left++P::right) ->
  (q=ring_sentinel L \/ In q (left++right)) ->
  (q=ring_sentinel L \/ In q (left++P::right) /\ q<>P).
Proof.
  intros L left right P q ND [EQ|IN]; [auto|]. right.
  split; [apply ring_members_insert; auto|].
  apply (proj1 (ring_members_remove left right P q ND)) in IN. tauto.
Qed.

(* Geometry-to-local-layout obligations are intentionally separate from
   byte-memory transition lemmas. No local contract is assumed as an oracle. *)
Lemma ring_insert_layout : forall m L left right idx P V O,
  ring_rep m L (left++right) idx V O -> idx=hd (ring_sentinel L) right ->
  ring_fresh m L (left++right) P V O ->
  insert_end_layout L P idx (ring_last (ring_sentinel L) left).
Proof.
  intros m L left right idx P V O REP IDX FRESH.
  apply (ring_insert_local_layout L (left++P::right)).
  - exact (ring_fresh_geometry m L left right P V O
      (ring_geom _ _ _ _ _ _ REP) FRESH).
  - apply ring_members_insert. auto.
  - apply (ring_link_fresh m L left right P V O idx FRESH). subst idx.
    destruct (ring_hd_member (ring_sentinel L) right) as [EQ|IN].
    + left; exact EQ.
    + right. apply in_or_app; right; exact IN.
  - apply (ring_link_fresh m L left right P V O _ FRESH).
    destruct (ring_last_member (ring_sentinel L) left) as [EQ|IN].
    + left; exact EQ.
    + right. apply in_or_app; left; exact IN.
Qed.
Lemma ring_remove_layout : forall m L left P right idx V O,
  ring_rep m L (left++P::right) idx V O ->
  list_remove_layout P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L.
Proof.
  intros m L left P right idx V O REP.
  pose proof (ring_geom _ _ _ _ _ _ REP) as G.
  assert (ND:NoDup (left++P::right)) by (pose proof (proj1 G) as ND0; inversion ND0; assumption).
  apply (ring_remove_local_layout L (left++P::right)); [exact G| | | ].
  - apply ring_members_insert. auto.
  - apply (ring_link_remove L left right P _ ND).
    destruct (ring_hd_member (ring_sentinel L) right) as [EQ|IN].
    + left; exact EQ.
    + right. apply in_or_app; right; exact IN.
  - apply (ring_link_remove L left right P _ ND).
    destruct (ring_last_member (ring_sentinel L) left) as [EQ|IN].
    + left; exact EQ.
    + right. apply in_or_app; left; exact IN.
Qed.

Lemma ring_permission_link_word : forall perm s L xs q off,
  (forall p, In p (L::xs) -> MemAcc perm s p 32 20) ->
  (q=ring_sentinel L \/ In q xs) -> off+4<=12 ->
  MemAcc perm s (q+off) 32 4.
Proof.
  intros perm s L xs q off ACC [EQ|IN] B.
  - subst q. unfold ring_sentinel. rewrite <- N.add_assoc.
    apply ring_permission_word; [apply ACC; left; reflexivity|].
    clear - B; lia.
  - apply ring_permission_word; [apply ACC; right; exact IN|].
    clear - B; lia.
Qed.

Theorem ring_insert_pre : forall s L left right idx P V O,
  ring_rep (s V_MEM32) L (left++right) idx V O ->
  idx=hd (ring_sentinel L) right -> ring_fresh (s V_MEM32) L (left++right) P V O ->
  ring_insert_permissions s L (left++right) P ->
  s R_R0=L -> s R_R1=P -> insert_end_ordinary_lr (s R_LR) ->
  insert_end_pre s L P idx (ring_last (ring_sentinel L) left).
Proof.
  intros s L left right idx P V O REP IDX FRESH [PERM [PR PW]] R0 R1 LR.
  assert (II:idx=ring_sentinel L \/ In idx (left++right)).
  { subst idx. destruct (ring_hd_member (ring_sentinel L) right) as [EQ|IN].
    - left; exact EQ.
    - right. apply in_or_app; right; exact IN. }
  assert (IB:ring_last (ring_sentinel L) left=ring_sentinel L \/
    In (ring_last (ring_sentinel L) left) (left++right)).
  { destruct (ring_last_member (ring_sentinel L) left) as [EQ|IN].
    - left; exact EQ.
    - right. apply in_or_app; left; exact IN. }
  assert (RD:forall q, In q (L::left++right) -> MemAcc mem_readable s q 32 20)
    by (intros q IN; exact (proj1 (PERM q IN))).
  assert (WR:forall q, In q (L::left++right) -> MemAcc mem_writable s q 32 20)
    by (intros q IN; exact (proj2 (PERM q IN))).
  unfold insert_end_pre. split; [eapply ring_insert_layout; eassumption|].
  split; [exact R0|]. split; [exact R1|].
  split; [eapply ring_insert_links; eassumption|]. split; [|exact LR].
  unfold insert_end_permissions. split.
  - apply ring_permission_word; [apply RD; left; reflexivity|reflexivity].
  - split; [apply (ring_permission_link_word _ _ _ _ _ _ RD II); reflexivity|].
    split.
    + rewrite <- (N.add_0_r L) at 1.
      apply ring_permission_word; [apply RD; left; reflexivity|reflexivity].
    + intros a IN. cbn [insert_end_writes In] in IN.
      destruct IN as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
      * apply ring_permission_word; [exact PW|reflexivity].
      * apply ring_permission_word; [exact PW|reflexivity].
      * apply (ring_permission_link_word _ _ _ _ _ _ WR IB); reflexivity.
      * apply (ring_permission_link_word _ _ _ _ _ _ WR II); reflexivity.
      * apply ring_permission_word; [exact PW|reflexivity].
      * apply ring_permission_word; [apply WR; left; reflexivity|reflexivity].
Qed.
Theorem ring_remove_pre : forall s L left P right idx V O,
  ring_rep (s V_MEM32) L (left++P::right) idx V O ->
  ring_permissions s L (left++P::right) -> s R_R0=P ->
  list_remove_pre P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx s.
Proof.
  intros s L left P right idx V O REP PERM R0.
  assert (II:hd (ring_sentinel L) right=ring_sentinel L \/
    In (hd (ring_sentinel L) right) (left++P::right)).
  { destruct (ring_hd_member (ring_sentinel L) right) as [EQ|IN].
    - left; exact EQ.
    - right. apply in_or_app; right; right; exact IN. }
  assert (IB:ring_last (ring_sentinel L) left=ring_sentinel L \/
    In (ring_last (ring_sentinel L) left) (left++P::right)).
  { destruct (ring_last_member (ring_sentinel L) left) as [EQ|IN].
    - left; exact EQ.
    - right. apply in_or_app; left; exact IN. }
  assert (IP:In P (L::left++P::right)).
  { right. apply ring_members_insert; auto. }
  assert (RD:forall q, In q (L::left++P::right) -> MemAcc mem_readable s q 32 20)
    by (intros q IN; exact (proj1 (PERM q IN))).
  assert (WR:forall q, In q (L::left++P::right) -> MemAcc mem_writable s q 32 20)
    by (intros q IN; exact (proj2 (PERM q IN))).
  unfold list_remove_pre. split; [eapply ring_remove_layout; eassumption|].
  split; [exact (proj1 (ring_count_remove left right P))|]. split; [exact R0|].
  split; [eapply ring_remove_original; eassumption|]. split.
  - intros a IN. cbn [In] in IN.
    destruct IN as [<-|[<-|[<-|[<-|[<-|[]]]]]].
    all: try (apply ring_permission_word; [apply RD; exact IP|reflexivity]).
    + rewrite <- (N.add_0_r L) at 1.
      apply ring_permission_word; [apply RD; left; reflexivity|reflexivity].
    + apply ring_permission_word; [apply RD; left; reflexivity|reflexivity].
  - split.
    + intros a IN. cbn [In] in IN. destruct IN as [<-|[<-|[<-|[<-|[]]]]].
      * apply (ring_permission_link_word _ _ _ _ _ _ WR II); reflexivity.
      * apply (ring_permission_link_word _ _ _ _ _ _ WR IB); reflexivity.
      * apply ring_permission_word; [apply WR; exact IP|reflexivity].
      * rewrite <- (N.add_0_r L) at 1.
        apply ring_permission_word; [apply WR; left; reflexivity|reflexivity].
    + intros _. apply ring_permission_word; [apply WR; left; reflexivity|reflexivity].
Qed.

(* Segments expose only finite list topology; they are not executable kernels. *)
Fixpoint ring_segment (m L before after:N) (xs:list N) (V O:N->N) : Prop :=
  match xs with
  | [] => True
  | q::ys => item_contents m q (V q) (hd after ys) before (O q) L /\
             ring_segment m L q after ys V O
  end.
Lemma ring_chain_segment : forall m L a xs V O,
  ring_chain m L a xs V O <-> ring_segment m L a (ring_sentinel L) xs V O.
Proof.
  intros m L a xs. revert a. induction xs; intros; cbn; [tauto|].
  rewrite IHxs. tauto.
Qed.
Lemma ring_segment_app : forall m L xs ys before after V O,
  ring_segment m L before after (xs++ys) V O <->
  ring_segment m L before (hd after ys) xs V O /\
  ring_segment m L (ring_last before xs) after ys V O.
Proof.
  intros m L xs. induction xs as [|q xs IH]; intros; cbn; [tauto|].
  assert (HD:hd after (xs++ys)=hd (hd after ys) xs) by (destruct xs; reflexivity).
  rewrite HD, IH. tauto.
Qed.
Lemma ring_segment_transport : forall m m' L xs before after V O,
  (forall q nxt prev, In q xs -> item_contents m q (V q) nxt prev (O q) L ->
    item_contents m' q (V q) nxt prev (O q) L) ->
  ring_segment m L before after xs V O -> ring_segment m' L before after xs V O.
Proof.
  intros m m' L xs. induction xs as [|q xs IH]; intros before after V O F CH; cbn in *.
  - exact I.
  - split.
    + apply F; [left; reflexivity|tauto].
    + apply (IH q after V O); [|tauto]. intros r nxt prev IN ITEM.
      apply F; [right; exact IN|exact ITEM].
Qed.
Lemma ring_segment_change_front : forall m m' L xs before before' after V O,
  NoDup xs ->
  (forall q nxt prev, In q xs -> item_contents m q (V q) nxt prev (O q) L ->
    item_contents m' q (V q) nxt
      (if q =? hd after xs then before' else prev) (O q) L) ->
  ring_segment m L before after xs V O ->
  ring_segment m' L before' after xs V O.
Proof.
  intros m m' L [|p xs] before before' after V O ND F CH; [exact I|].
  cbn in CH |- *. inversion ND as [|p' xs' NOT ND']; subst.
  split.
  - specialize (F p (hd after xs) before (or_introl eq_refl) (proj1 CH)).
    cbn [hd] in F. rewrite N.eqb_refl in F. exact F.
  - apply (ring_segment_transport m m' L xs p after V O); [|exact (proj2 CH)].
    intros q nxt prev IN ITEM.
    specialize (F q nxt prev (or_intror IN) ITEM). cbn [hd] in F.
    assert (NE:q<>p) by (intro EQ; subst q; contradiction).
    rewrite (proj2 (N.eqb_neq q p) NE) in F. exact F.
Qed.
Lemma ring_segment_change_back : forall m m' L xs before after after' V O,
  NoDup xs ->
  (forall q nxt prev, In q xs -> item_contents m q (V q) nxt prev (O q) L ->
    item_contents m' q (V q)
      (if q =? ring_last before xs then after' else nxt) prev (O q) L) ->
  ring_segment m L before after xs V O ->
  ring_segment m' L before after' xs V O.
Proof.
  intros m m' L xs. induction xs using rev_ind;
    intros before after after' V O ND F CH; [exact I|].
  rewrite ring_segment_app in CH |- *. destruct CH as [PREFIX LAST].
  assert (NOT:~In x xs).
  { pose proof (NoDup_remove_2 xs [] x ND) as NOT. rewrite app_nil_r in NOT. exact NOT. }
  assert (LASTEQ:ring_last before (xs++[x])=x) by (rewrite ring_last_app; reflexivity).
  split.
  - apply (ring_segment_transport m m' L xs before x V O); [|exact PREFIX].
    intros q nxt prev IN ITEM.
    specialize (F q nxt prev (in_or_app _ _ _ (or_introl IN)) ITEM).
    rewrite LASTEQ in F.
    assert (NE:q<>x) by (intro EQ; subst q; contradiction).
    rewrite (proj2 (N.eqb_neq q x) NE) in F. exact F.
  - cbn in LAST |- *. split; [|exact I].
    specialize (F x after (ring_last before xs)
      (in_or_app _ _ _ (or_intror (or_introl eq_refl))) (proj1 LAST)).
    rewrite LASTEQ, N.eqb_refl in F. exact F.
Qed.

Lemma ring_insert_word_frame : forall m L P I B q off,
  (forall w, In w (insert_end_writes L P I B) -> separate32 (q+off) 4 w 4) ->
  field32 (insert_end_memory m L P I B) q off=field32 m q off.
Proof.
  intros m L P I B q off OUT.
  unfold insert_end_memory, insert_end_prefix, field32, write_field32.
  repeat rewrite getmem_noverlap by
    (apply OUT; cbn [insert_end_writes In]; tauto).
  reflexivity.
Qed.
Lemma ring_node_link_field_separate : forall L xs q r i j,
  ring_geometry L xs -> In q xs -> (r=ring_sentinel L \/ In r xs) ->
  In i fields20 -> (j=4 \/ j=8) -> (q<>r \/ i<>j) ->
  separate32 (q+i) 4 (r+j) 4.
Proof.
  intros L xs q r i j G IQ [->|IR] II [->|->] NE.
  - unfold ring_sentinel. rewrite <- N.add_assoc.
    apply (ring_object_fields_separate L xs q L i 12 G).
    + right; exact IQ.
    + left; reflexivity.
    + exact II.
    + cbn; tauto.
    + left. apply (ring_node_not_header L xs q G IQ).
  - unfold ring_sentinel. rewrite <- N.add_assoc.
    apply (ring_object_fields_separate L xs q L i 16 G).
    + right; exact IQ.
    + left; reflexivity.
    + exact II.
    + cbn; tauto.
    + left. apply (ring_node_not_header L xs q G IQ).
  - apply (ring_object_fields_separate L xs q r i 4 G); cbn; tauto.
  - apply (ring_object_fields_separate L xs q r i 8 G); cbn; tauto.
Qed.
Lemma ring_header_link_field_separate : forall L xs r i j,
  ring_geometry L xs -> (r=ring_sentinel L \/ In r xs) ->
  In i fields20 -> (j=4 \/ j=8) -> i<>8+j ->
  separate32 (L+i) 4 (r+j) 4.
Proof.
  intros L xs r i j G [->|IR] II [->|->] NE.
  - unfold ring_sentinel. rewrite <- N.add_assoc.
    apply (ring_object_fields_separate L xs L L i 12 G); cbn; tauto.
  - unfold ring_sentinel. rewrite <- N.add_assoc.
    apply (ring_object_fields_separate L xs L L i 16 G); cbn; tauto.
  - apply (ring_object_fields_separate L xs L r i 4 G); try solve [cbn; tauto].
    left. intro EQ. subst r. exact (ring_node_not_header L xs L G IR eq_refl).
  - apply (ring_object_fields_separate L xs L r i 8 G); try solve [cbn; tauto].
    left. intro EQ. subst r. exact (ring_node_not_header L xs L G IR eq_refl).
Qed.

Lemma ring_remove_geometry : forall L left P right,
  ring_geometry L (left++P::right) -> ring_geometry L (left++right).
Proof.
  intros L left P right [ND [OBJ SEP]].
  assert (INCL:forall q, In q (L::left++right) -> In q (L::left++P::right)).
  { intros q [EQ|IN]; [left; exact EQ|]. right.
    apply ring_members_insert; auto. }
  split.
  - exact (NoDup_remove_1 (L::left) right P ND).
  - split.
    + intros q IN. exact (OBJ q (INCL q IN)).
    + intros q r IQ IR NE. exact (SEP q r (INCL q IQ) (INCL r IR) NE).
Qed.
Lemma ring_remove_cursor_valid : forall L left P right idx,
  ring_geometry L (left++P::right) ->
  (idx=ring_sentinel L \/ In idx (left++P::right)) ->
  ring_remove_cursor idx P (ring_last (ring_sentinel L) left)=ring_sentinel L \/
  In (ring_remove_cursor idx P (ring_last (ring_sentinel L) left)) (left++right).
Proof.
  intros L left P right idx G CUR. unfold ring_remove_cursor.
  destruct (N.eqb_spec idx P) as [EQ|NE].
  - destruct (ring_last_member (ring_sentinel L) left) as [S|IN].
    + left; exact S.
    + right. apply in_or_app; left; exact IN.
  - destruct CUR as [S|IN]; [left; exact S|]. right.
    assert (ND:NoDup (left++P::right)) by (pose proof (proj1 G) as ND0; inversion ND0; assumption).
    apply (proj2 (ring_members_remove left right P idx ND)). split; assumption.
Qed.

(* Main pure-memory obligations: exact r03/r04 memory expressions, not an
   abstract replacement kernel. Both ghost maps remain unchanged. *)
Theorem ring_insert_memory : forall m L left right idx P V O,
  ring_rep m L (left++right) idx V O -> idx=hd (ring_sentinel L) right ->
  ring_fresh m L (left++right) P V O -> N.of_nat (length (left++right))+1<2^32 ->
  ring_rep (insert_end_memory m L P idx (ring_last (ring_sentinel L) left))
    L (left++P::right) idx V O.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_remove_memory : forall m L left P right idx V O,
  ring_rep m L (left++P::right) idx V O ->
  ring_rep (list_remove_mem m P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx)
    L (left++right) (ring_remove_cursor idx P (ring_last (ring_sentinel L) left)) V O.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

Theorem ring_insert_frame : forall m L P idx prev,
  insert_end_byte_frame m (insert_end_memory m L P idx prev) L P idx prev.
Proof. exact insert_end_memory_frame. Qed.
Theorem ring_remove_frame : forall m P nxt prev L c idx,
  list_remove_byte_frame m (list_remove_mem m P nxt prev L c idx) P nxt prev L idx.
Proof. intros m P nxt prev L c idx a OUT. apply list_remove_mem_frame. exact OUT. Qed.

(* These bridges certify the actual accepted programs independently of the
   remaining finite sequence memory-transition obligations. *)
Theorem ring_insert_local_contract : forall s0 t s L left right idx P V O,
  ring_rep (s0 V_MEM32) L (left++right) idx V O ->
  idx=hd (ring_sentinel L) right -> ring_fresh (s0 V_MEM32) L (left++right) P V O ->
  ring_insert_permissions s0 L (left++right) P ->
  s0 R_R0=L -> s0 R_R1=P -> insert_end_ordinary_lr (s0 R_LR) ->
  models armv6mtypctx s0 -> startof t (Addr 0x70,s)=(Addr 0x5c,s0) ->
  exec_prog vListInsertEnd_armv6m_prog ((Addr 0x70,s)::t) -> unterminated insert_end_exit t ->
  insert_end_post s0 L P idx (ring_last (ring_sentinel L) left) s.
Proof.
  intros s0 t s L left right idx P V O REP IDX FRESH PERM R0 R1 LR MDL ENTRY XP UT.
  exact (insert_end_at_bx s0 t s L P idx (ring_last (ring_sentinel L) left)
    ENTRY MDL (ring_insert_pre s0 L left right idx P V O REP IDX FRESH PERM R0 R1 LR) XP UT).
Qed.
Theorem ring_remove_local_contract : forall s0 t s L left P right idx V O,
  ring_rep (s0 V_MEM32) L (left++P::right) idx V O ->
  ring_permissions s0 L (left++P::right) -> s0 R_R0=P -> models armv6mtypctx s0 ->
  startof t (Addr 0xbc,s)=(Addr 0xa0,s0) ->
  exec_prog uxListRemove_armv6m_prog ((Addr 0xbc,s)::t) -> unterminated list_remove_exit t ->
  list_remove_post s0 P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx s /\
  list_remove_effects (s0 V_MEM32) (s V_MEM32) P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx /\
  (forall v, list_remove_preserved v -> s v=s0 v).
Proof.
  intros s0 t s L left P right idx V O REP PERM R0 MDL ENTRY XP UT.
  exact (list_remove_at_bx s0 t s P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx
    ENTRY MDL (ring_remove_pre s0 L left P right idx V O REP PERM R0) XP UT).
Qed.

(* Actual IL connections; the original finite program is retained verbatim. *)
Theorem ring_insert_refines : forall s0 t s L left right idx P V O,
  ring_rep (s0 V_MEM32) L (left++right) idx V O ->
  idx=hd (ring_sentinel L) right -> ring_fresh (s0 V_MEM32) L (left++right) P V O ->
  N.of_nat (length (left++right))+1<2^32 ->
  ring_insert_permissions s0 L (left++right) P ->
  s0 R_R0=L -> s0 R_R1=P -> insert_end_ordinary_lr (s0 R_LR) ->
  models armv6mtypctx s0 -> startof t (Addr 0x70,s)=(Addr 0x5c,s0) ->
  exec_prog vListInsertEnd_armv6m_prog ((Addr 0x70,s)::t) -> unterminated insert_end_exit t ->
  ring_rep (s V_MEM32) L (left++P::right) idx V O /\
  (forall q, In q (left++P::right) <-> q=P \/ In q (left++right)) /\
  field32 (s V_MEM32) L 0=N.of_nat (length (left++right))+1 /\
  insert_end_post s0 L P idx (ring_last (ring_sentinel L) left) s.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_remove_refines : forall s0 t s L left P right idx V O,
  ring_rep (s0 V_MEM32) L (left++P::right) idx V O ->
  ring_permissions s0 L (left++P::right) -> s0 R_R0=P -> models armv6mtypctx s0 ->
  startof t (Addr 0xbc,s)=(Addr 0xa0,s0) ->
  exec_prog uxListRemove_armv6m_prog ((Addr 0xbc,s)::t) -> unterminated list_remove_exit t ->
  ring_rep (s V_MEM32) L (left++right)
    (ring_remove_cursor idx P (ring_last (ring_sentinel L) left)) V O /\
  (forall q, In q (left++right) <-> In q (left++P::right) /\ q<>P) /\
  s R_R0=N.of_nat (length (left++right)) /\
  list_remove_effects (s0 V_MEM32) (s V_MEM32) P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx /\
  (forall v, list_remove_preserved v -> s v=s0 v).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

(* Concrete witnesses are finite byte images, not replacement kernels.
   Values=42 and owner=99 are arbitrary opaque data. All cursor positions
   in these rings are allowed by the following three statements. *)
Definition ring_singleton_image idx :=
  image20 (image20 0 4096 1 idx list_max_value 8192 8192)
    8192 42 4104 4104 99 4096.
Definition ring_multi_image idx :=
  image20 (image20 (image20 0 4096 2 idx list_max_value 8192 12288)
    8192 42 12288 4104 99 4096) 12288 42 4104 8192 99 4096.
Ltac ring_concrete_geometry :=
  clear; unfold ring_geometry; repeat split;
  try solve [repeat constructor; cbn; intuition discriminate];
  intros; cbn in *;
  repeat match goal with H:_ \/ _ |- _ => destruct H end;
  subst; try contradiction;
  try solve [unfold object32, range32; vm_compute; repeat split; congruence];
  lia.
Ltac ring_concrete_fields :=
  unfold ring_chain, list_header, item_contents, field32, image20, write_field32,
    item_value_offset, item_next_offset, item_previous_offset,
    item_owner_offset, item_container_offset,
    list_count_offset, list_index_offset, list_end_offset, ring_sentinel;
  cbn [hd ring_last length N.of_nat]; repeat split;
  repeat first [rewrite getmem_setmem by discriminate
    | rewrite getmem_noverlap by (apply ranges32_separate; unfold range32; clear; lia)];
  rewrite ?N.mod_small by (clear; lia); reflexivity.
Lemma ring_image20_word_frame : forall m p v0 v4 v8 v12 v16 q off,
  separate32 (q+off) 4 p 20 ->
  field32 (image20 m p v0 v4 v8 v12 v16) q off=field32 m q off.
Proof.
  intros m p v0 v4 v8 v12 v16 q off SEP. unfold image20.
  repeat rewrite field32_frame by
    (apply noverlap_index_r with (len2:=20); [exact SEP|reflexivity]).
  reflexivity.
Qed.
Ltac ring_image_field :=
  lazymatch goal with
  | |- field32 (image20 ?m ?p ?v0 ?v4 ?v8 ?v12 ?v16) ?p ?off = _ =>
    let F := fresh "FIELDS" in
    pose proof (image20_fields m p v0 v4 v8 v12 v16
      ltac:(clear; reflexivity) ltac:(reflexivity) ltac:(reflexivity)
      ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)) as F;
    destruct F as [? [? [? [? ?]]]]; assumption
  | |- field32 (image20 ?m ?p ?v0 ?v4 ?v8 ?v12 ?v16) ?q ?off = _ =>
    rewrite (ring_image20_word_frame m p v0 v4 v8 v12 v16 q off) by
      (apply ranges32_separate; unfold range32; clear; lia);
    ring_image_field
  end.
Ltac ring_witness_fields :=
  cbn [ring_chain hd ring_last length];
  unfold list_header, item_contents, list_count_offset, list_index_offset,
    list_end_offset, item_value_offset, item_next_offset, item_previous_offset,
    item_owner_offset, item_container_offset;
  repeat split; ring_image_field.

Theorem ring_empty_witness :
  ring_rep (empty_image 0 4096) 4096 [] 4104 (fun _=>42) (fun _=>99).
Proof.
  pose proof (empty_image_spec 0 4096 (proj1 list_regions_witness)) as E.
  destruct E as [OBJ [HEADER [FRONT BACK]]]. constructor.
  - ring_concrete_geometry.
  - reflexivity.
  - left; reflexivity.
  - exact HEADER.
  - exact FRONT.
  - exact BACK.
  - exact I.
Qed.
Theorem ring_singleton_witness : forall idx, idx=4104 \/ idx=8192 ->
  ring_rep (ring_singleton_image idx) 4096 [8192] idx (fun _=>42) (fun _=>99).
Proof.
  intros idx CUR. destruct CUR as [->|->]; (constructor;
    [ring_concrete_geometry|reflexivity|cbn; tauto|
     unfold ring_singleton_image; ring_witness_fields|
     unfold ring_singleton_image; ring_witness_fields|
     unfold ring_singleton_image; ring_witness_fields|
     unfold ring_singleton_image; ring_witness_fields]).
Qed.
Theorem ring_multi_witness : forall idx, idx=4104 \/ idx=8192 \/ idx=12288 ->
  ring_rep (ring_multi_image idx) 4096 [8192;12288] idx (fun _=>42) (fun _=>99).
Proof.
  intros idx CUR. destruct CUR as [->|[->|->]]; (constructor;
    [ring_concrete_geometry|reflexivity|cbn; tauto|
     unfold ring_multi_image; ring_witness_fields|
     unfold ring_multi_image; ring_witness_fields|
     unfold ring_multi_image; ring_witness_fields|
     unfold ring_multi_image; ring_witness_fields]).
Qed.
Theorem ring_empty_insert_witness : exists s,
  models armv6mtypctx s /\
  ring_rep (s V_MEM32) 4096 [] 4104 (fun p=>field32 (s V_MEM32) p 0)
    (fun p=>field32 (s V_MEM32) p 12) /\
  insert_end_pre s 4096 8192 4104 4104.
Proof.
  assert (MT:empty_image 0 4096<memsize 32).
  { unfold empty_image. apply image20_welltyped. change (0<2^(2^32*8)). apply mp2_gt_0. }
  assert (LINKS:insert_end_links (empty_image 0 4096) 4096 4104 4104).
  { exact (ring_insert_links _ _ [] [] _ _ _ ring_empty_witness eq_refl). }
  destruct (insert_end_entry_witness _ _ _ _ _ MT insert_end_empty_layout LINKS)
    as [s [MDL [PRE MEM]]]. exists s. split; [exact MDL|]. split; [|exact PRE].
  rewrite MEM. destruct ring_empty_witness as [G B C H F BK CH].
  constructor; [exact G|exact B|exact C|exact H|exact F|exact BK|exact I].
Qed.
Theorem ring_singleton_remove_witness : forall equal:bool, exists s,
  models armv6mtypctx s /\
  ring_rep (s V_MEM32) 4096 [8192] (if equal then 8192 else 4104)
    (fun _=>42) (fun _=>99) /\
  list_remove_pre 8192 4104 4104 4096 1 (if equal then 8192 else 4104) s.
Proof.
  intro equal. destruct (list_remove_singleton_witness 0 42 99 equal
    ltac:(change (0<2^(2^32*8)); apply mp2_gt_0)
    ltac:(reflexivity) ltac:(reflexivity)) as [s [MDL [PRE [MEM LR]]]].
  exists s. split; [exact MDL|]. split; [|exact PRE]. rewrite MEM.
  apply ring_singleton_witness. destruct equal; auto.
Qed.
Theorem ring_multi_remove_witness : forall idx,
  idx=4104 \/ idx=8192 \/ idx=12288 -> exists s,
  models armv6mtypctx s /\ ring_rep (s V_MEM32) 4096 [8192;12288] idx
    (fun _=>42) (fun _=>99) /\ list_remove_pre 8192 12288 4104 4096 2 idx s.
Proof.
  intros idx CUR. pose proof (ring_multi_witness idx CUR) as REP.
  assert (MT:ring_multi_image idx<memsize 32).
  { unfold ring_multi_image. repeat apply image20_welltyped.
    change (0<2^(2^32*8)). apply mp2_gt_0. }
  pose proof (ring_remove_layout _ _ [] _ _ _ _ _ REP) as LAY.
  pose proof (ring_remove_original _ _ [] _ _ _ _ _ REP) as ORIG.
  destruct (list_remove_entry_witness _ _ _ _ _ _ _ 257 MT LAY
    ltac:(reflexivity) ORIG ltac:(reflexivity)) as [s [MDL [PRE [MEM LR]]]].
  exists s. split; [exact MDL|]. split; [rewrite MEM; exact REP|exact PRE].
Qed.
