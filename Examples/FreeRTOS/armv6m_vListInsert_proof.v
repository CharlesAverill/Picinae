(* vListInsert: finite sorted insertion, original-memory and AAPCS32 contract.

   PROVENANCE: official FreeRTOS V11.1.0 commit
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0; Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Accepted e05 finite map vListInsert_armv6m_prog, entry 0x72, 46 bytes;
   unchanged generated source. r00 kit at 4ff26413448da4d8f064b0273ac5472cc9de7e5a.
   Initial author: OpenAI gpt-6-astra, xhigh/default, one-shot.
   Final proof producer: unassigned pending full validation.
   Exact initial attempt, diagnostics and status: notes/r05-list-insert/.

   INPUT: R0=L, R1=P, SP aligned to 8, SP>=12, ordinary odd LR<0xfffffff0.
   L is a 20-byte List_t with embedded 12-byte sentinel at L+8. P and each
   finite old node are aligned nonnull nonwrapping 20-byte ListItem_t objects.
   Old nodes, L, P and the 12-byte stack spill are byte-disjoint. The sentinel
   is deliberately embedded in L, never required to be disjoint from L.
   The old chain has exact forward/backward links and container=L, count is
   length modulo 2^32, index is sentinel or a node, values sorted unsigned.
   P has value X<2^32 and owner O<2^32; its old links/container are unrestricted.
   Permissions cover old/new/list fields and the stack; no external contracts.

   EFFECT: insert P after all old values <=X, including equal values. For
   X=UINT32_MAX the actual 0x9c path selects sentinel.prev without traversal.
   PUSH saves R4,R5,LR at SP-12,SP-8,SP-4. The six actual body stores are
   P.next=next; next.prev=P; P.prev=prev; prev.next=P; P.container=L;
   L.count=(old count+1) mod 2^32. Every other original byte is preserved.
   All old values/owners and P.value/P.owner survive; index is unchanged.
   Output chain is the exact old prefix ++ [P] ++ old suffix, still sorted.
   At POP 0x9a, R4=prev,R5=X,SP=old SP-12. The actual POP restores R4,R5,SP
   and returns through armv6m_bxwritepc to LR & 0xfffffffe. R0/R1 unchanged;
   R2 is next.value (normal path) or zero (max path); R3 incremented count.
   NZCV are precisely the final ADDS count flags. No CPU tunables.

   SCOPE: sequential IL partial correctness of finite traces and the ordinary
   guarded return step. This does not prove termination, hardware/lifter
   refinement, scheduling, IRQ safety, or any TCB/owner dereference claim.
 *)
Require Import Picinae_armv6m vListInsert_armv6m armv6m_list_model.
From Stdlib Require Import NArith Lia List Sorting.Sorted FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Theorem sorted_insert_nwc : forall s1 s2,
  vListInsert_armv6m_prog s1 = vListInsert_armv6m_prog s2.
Proof. reflexivity. Qed.
Print Assumptions sorted_insert_nwc.
Theorem sorted_insert_welltyped : welltyped_prog armv6mtypctx vListInsert_armv6m_prog.
Proof. exact vListInsert_armv6m_welltyped. Qed.
Print Assumptions sorted_insert_welltyped.

Definition si_preserved (v:armv6mvar) :=
  match v with V_MEM32 | R_R2 | R_R3 | R_R4 | R_R5 | R_SP |
    F_N | F_Z | F_C | F_V => False | _ => True end.
Theorem sorted_insert_register_frame : forall v, si_preserved v ->
  forall_endstates vListInsert_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof.
  intros v KEEP. destruct v; cbn in KEEP; try contradiction;
    apply noassign_prog_same; prove_noassign.
Qed.
Print Assumptions sorted_insert_register_frame.

Record si_node := SiNode { si_ptr:N; si_value:N; si_owner:N }.
Definition si_order (a b:si_node) := si_value a <= si_value b.
Definition si_sorted := StronglySorted si_order.
Definition si_first sentinel (xs:list si_node) :=
  match xs with [] => sentinel | x::_ => si_ptr x end.
Definition si_last sentinel (xs:list si_node) :=
  match rev xs with [] => sentinel | x::_ => si_ptr x end.
Fixpoint si_split (value:N) (xs:list si_node) : list si_node * list si_node :=
  match xs with
  | [] => ([],[])
  | a::rest => if si_value a <=? value then
      let '(lo,hi) := si_split value rest in (a::lo,hi)
    else ([],xs)
  end.
Definition si_cut value xs :=
  if value =? list_max_value then (xs,[]) else si_split value xs.
Definition si_before value xs := fst (si_cut value xs).
Definition si_after value xs := snd (si_cut value xs).
Definition si_result (new:si_node) xs :=
  si_before (si_value new) xs ++ new :: si_after (si_value new) xs.
Definition si_prev L new xs := si_last (L+8) (si_before (si_value new) xs).
Definition si_next L new xs := si_first (L+8) (si_after (si_value new) xs).

Fixpoint si_chain m L sentinel previous (xs:list si_node) : Prop :=
  match xs with
  | [] => field32 m sentinel 8 = previous /\ field32 m previous 4 = sentinel
  | a::rest => item_contents m (si_ptr a) (si_value a) (si_first sentinel rest)
                previous (si_owner a) L /\ si_chain m L sentinel (si_ptr a) rest
  end.
Definition si_ring m L index xs :=
  list_header m L (N.of_nat (length xs) mod 2^32) index /\
  field32 m (L+8) 4 = si_first (L+8) xs /\
  si_chain m L (L+8) (L+8) xs /\ si_sorted xs.
Fixpoint si_apart (xs:list si_node) : Prop :=
  match xs with [] => True | a::rest =>
    Forall (fun b => separate32 (si_ptr a) 20 (si_ptr b) 20) rest /\ si_apart rest
  end.
Definition si_layout L P sp xs :=
  object32 L 20 /\ object32 P 20 /\
  12 <= sp /\ sp < 2^32 /\ sp mod 8 = 0 /\
  separate32 P 20 L 20 /\ separate32 (sp-12) 12 L 20 /\
  separate32 (sp-12) 12 P 20 /\
  Forall (fun a => object32 (si_ptr a) 20 /\ si_value a < 2^32 /\
    si_owner a < 2^32 /\ separate32 (si_ptr a) 20 L 20 /\
    separate32 (si_ptr a) 20 P 20 /\ separate32 (sp-12) 12 (si_ptr a) 20) xs /\
  si_apart xs /\ NoDup (map si_ptr xs).
Definition si_access_words L P sp xs :=
  [L;L+4;L+8;L+12;L+16;P;P+4;P+8;P+12;P+16;sp-12;sp-8;sp-4] ++
  flat_map (fun a => map (fun k => si_ptr a+k) fields20) xs.
Definition si_permissions (s:store) L P sp xs :=
  forall a, In a (si_access_words L P sp xs) ->
    MemAcc mem_readable s a 32 4 /\ MemAcc mem_writable s a 32 4.
Definition si_ordinary_return lr := lr mod 2 = 1 /\ lr < 0xfffffff0.
Definition si_pre (s:store) L (new:si_node) index xs :=
  si_layout L (si_ptr new) (s R_SP) xs /\
  s R_R0=L /\ s R_R1=si_ptr new /\
  si_value new < 2^32 /\ si_owner new < 2^32 /\
  field32 (s V_MEM32) (si_ptr new) 0=si_value new /\
  field32 (s V_MEM32) (si_ptr new) 12=si_owner new /\
  si_ring (s V_MEM32) L index xs /\
  In index ((L+8)::map si_ptr xs) /\
  si_permissions s L (si_ptr new) (s R_SP) xs /\
  si_ordinary_return (s R_LR).

(* Exact write sequences over the original memory, not replacement code. *)
Definition si_write m (av:N*N) := write_field32 m (fst av) 0 (snd av).
Definition si_apply m (writes:list (N*N)) := fold_left si_write writes m.
Definition si_stack_writes (s:store) :=
  [(s R_SP-12,s R_R4);(s R_SP-8,s R_R5);(s R_SP-4,s R_LR)].
Definition si_stackmem (s:store) := si_apply (s V_MEM32) (si_stack_writes s).
Definition si_body_writes m L P previous next :=
  [(P+4,next);(next+8,P);(P+8,previous);(previous+4,P);(P+16,L);
   (L,(field32 m L 0+1) mod 2^32)].
Definition si_memory (s0:store) L new xs :=
  si_apply (si_stackmem s0)
    (si_body_writes (s0 V_MEM32) L (si_ptr new)
      (si_prev L new xs) (si_next L new xs)).
Definition si_all_writes (s0:store) L new xs := si_stack_writes s0 ++
  si_body_writes (s0 V_MEM32) L (si_ptr new) (si_prev L new xs) (si_next L new xs).
Definition si_frame m m' (writes:list (N*N)) :=
  forall a, (forall w v, In (w,v) writes -> separate32 a 1 w 4) ->
    getmem 32 LittleE 1 m' a = getmem 32 LittleE 1 m a.
Definition si_flags c (s:store) :=
  let r := (c+1) mod 2^32 in
  s F_N = cast CAST_HIGH 32 1 r /\ s F_Z = eval_binop OP_EQ 32 r 0 /\
  s F_C = eval_binop OP_LT 32 r c /\
  s F_V = cast CAST_HIGH 32 1 (N.land (N.lxor c r) (N.lxor 1 r)).
Definition si_memory_post (s0:store) L new index xs (s:store) :=
  s V_MEM32=si_memory s0 L new xs /\
  si_ring (s V_MEM32) L index (si_result new xs) /\
  field32 (s V_MEM32) L 0 = (field32 (s0 V_MEM32) L 0+1) mod 2^32 /\
  field32 (s V_MEM32) (si_ptr new) 0 = si_value new /\
  field32 (s V_MEM32) (si_ptr new) 12 = si_owner new /\
  field32 (s V_MEM32) (si_ptr new) 16 = L /\
  (forall a, In a xs -> field32 (s V_MEM32) (si_ptr a) 0 = si_value a /\
                       field32 (s V_MEM32) (si_ptr a) 12 = si_owner a) /\
  si_frame (s0 V_MEM32) (s V_MEM32) (si_all_writes s0 L new xs).
Definition si_at_pop (s0:store) L new index xs (s:store) :=
  si_memory_post s0 L new index xs s /\
  s R_R4=si_prev L new xs /\ s R_R5=si_value new /\ s R_SP=s0 R_SP-12 /\
  s R_R2=(if si_value new =? list_max_value then 0
    else field32 (s0 V_MEM32) (si_next L new xs) 0) /\
  s R_R3=(field32 (s0 V_MEM32) L 0+1) mod 2^32 /\
  si_flags (field32 (s0 V_MEM32) L 0) s /\
  (forall v, si_preserved v -> s v=s0 v).
Definition si_returned (s0:store) L new index xs (s:store) :=
  si_memory_post s0 L new index xs s /\
  s R_R4=s0 R_R4 /\ s R_R5=s0 R_R5 /\ s R_SP=s0 R_SP /\
  s R_R2=(if si_value new =? list_max_value then 0
    else field32 (s0 V_MEM32) (si_next L new xs) 0) /\
  s R_R3=(field32 (s0 V_MEM32) L 0+1) mod 2^32 /\
  si_flags (field32 (s0 V_MEM32) L 0) s /\
  (forall v, si_preserved v -> s v=s0 v).

(* The loop has traversed exactly done, and cursor is its last element or
   the embedded sentinel. Unread memory is the original memory plus PUSH. *)
Definition si_loop (s0:store) L new xs (s:store) :=
  exists done todo, xs=done++todo /\
    Forall (fun a => si_value a <= si_value new) done /\
    si_value new < list_max_value /\
    s V_MEM32=si_stackmem s0 /\ s R_R0=L /\ s R_R1=si_ptr new /\
    s R_R5=si_value new /\ s R_R3=si_last (L+8) done /\
    s R_SP=s0 R_SP-12 /\ (forall v, si_preserved v -> s v=s0 v).
Definition si_join (s0:store) L new xs (s:store) :=
  s V_MEM32=si_stackmem s0 /\ s R_R0=L /\ s R_R1=si_ptr new /\
  s R_R4=si_prev L new xs /\ s R_R5=si_value new /\ s R_SP=s0 R_SP-12 /\
  s R_R2=(if si_value new =? list_max_value then 0
    else field32 (s0 V_MEM32) (si_next L new xs) 0) /\
  (forall v, si_preserved v -> s v=s0 v).
Definition si_exit (t:trace) :=
  match t with (Addr 0x9a,_)::_ => true | _ => false end.
Definition si_invs (s0:store) L new index xs (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x72 => Some (s=s0)
  | 0x7e => Some (si_loop s0 L new xs s)
  | 0x88 => Some (si_join s0 L new xs s)
  | 0x9a => Some (si_at_pop s0 L new index xs s)
  | _ => None end | _ => None end.

Theorem si_apply_frame : forall writes m,
  si_frame m (si_apply m writes) writes.
Proof.
  induction writes as [|[w v] rest IH]; intros m a OUT.
  - reflexivity.
  - change (getmem 32 LittleE 1 (si_apply (write_field32 m w 0 v) rest) a = getmem 32 LittleE 1 m a).
    rewrite (IH (write_field32 m w 0 v) a).
    + unfold write_field32. rewrite N.add_0_r. apply getmem_noverlap.
      apply (OUT w v). now left.
    + intros w' v' IN. apply (OUT w' v'). now right.
Qed.
Print Assumptions si_apply_frame.
Theorem si_apply_typed : forall writes m,
  m < memsize 32 -> si_apply m writes < memsize 32.
Proof.
  induction writes as [|[w v] rest IH]; intros m MT.
  - exact MT.
  - apply IH. unfold si_write, write_field32. apply setmem_welltyped. exact MT.
Qed.
Print Assumptions si_apply_typed.
Theorem si_memory_frame : forall s0 L new xs,
  si_frame (s0 V_MEM32) (si_memory s0 L new xs) (si_all_writes s0 L new xs).
Proof.
  intros. unfold si_memory, si_stackmem, si_all_writes, si_apply.
  rewrite <- fold_left_app. apply si_apply_frame.
Qed.
Print Assumptions si_memory_frame.

Theorem si_split_partition : forall xs value,
  xs=fst (si_split value xs) ++ snd (si_split value xs).
Proof.
  induction xs as [|a xs IH]; intro value; [reflexivity|].
  cbn [si_split]. destruct (si_value a <=? value).
  - specialize (IH value). destruct (si_split value xs) as [lo hi].
    cbn in *. now rewrite <- IH.
  - reflexivity.
Qed.
Print Assumptions si_split_partition.
Theorem si_cut_partition : forall xs value,
  xs=si_before value xs ++ si_after value xs.
Proof.
  intros. unfold si_before, si_after, si_cut.
  destruct (value =? list_max_value); cbn.
  - now rewrite app_nil_r.
  - apply si_split_partition.
Qed.
Print Assumptions si_cut_partition.
Theorem si_result_length : forall new xs,
  length (si_result new xs)=S (length xs).
Proof.
  intros. unfold si_result. rewrite app_length. cbn [length].
  pose proof (si_cut_partition xs (si_value new)) as E.
  apply (f_equal (@length si_node)) in E. rewrite app_length in E. lia.
Qed.
Print Assumptions si_result_length.
Theorem si_result_membership : forall new xs a,
  In a (si_result new xs) <-> a=new \/ In a xs.
Proof.
  intros. unfold si_result. rewrite in_app_iff. cbn [In].
  assert (OLD: In a xs <-> In a (si_before (si_value new) xs) \/
    In a (si_after (si_value new) xs)).
  { rewrite (si_cut_partition xs (si_value new)) at 1. apply in_app_iff. }
  rewrite OLD. intuition congruence.
Qed.
Print Assumptions si_result_membership.
Theorem si_max_cut : forall xs,
  si_before list_max_value xs=xs /\ si_after list_max_value xs=[].
Proof. intros. unfold si_before, si_after, si_cut. rewrite N.eqb_refl. auto. Qed.
Print Assumptions si_max_cut.

Theorem si_split_bounds : forall xs value,
  si_sorted xs ->
  Forall (fun a => si_value a <= value) (fst (si_split value xs)) /\
  Forall (fun a => value < si_value a) (snd (si_split value xs)).
Proof.
  intros xs value SORT. induction SORT as [|a rest SORT IH ALL].
  - split; constructor.
  - cbn [si_split]. destruct (si_value a <=? value) eqn:LE.
    + apply N.leb_le in LE. destruct (si_split value rest) as [lo hi].
      cbn in IH. destruct IH as [LOW HIGH]. cbn. split; [constructor|]; assumption.
    + apply N.leb_gt in LE. cbn. split; [constructor|].
      constructor; [exact LE|]. eapply Forall_impl; [|exact ALL].
      intros b AB. unfold si_order in AB. lia.
Qed.
Print Assumptions si_split_bounds.

Theorem si_result_sorted : forall new xs,
  si_sorted xs -> si_value new < 2^32 ->
  Forall (fun a => si_value a < 2^32) xs -> si_sorted (si_result new xs).
Proof.
  intros new xs SORT NEW BOUNDS.
  unfold si_result, si_before, si_after, si_cut.
  destruct (si_value new =? list_max_value) eqn:MAX.
  - apply N.eqb_eq in MAX. cbn.
    induction SORT as [|a rest SORT IH ALL]; cbn.
    + repeat constructor.
    + inversion BOUNDS; subst. constructor.
      * apply IH. assumption.
      * apply Forall_app. split; [exact ALL|]. constructor; [|constructor].
        unfold si_order. rewrite MAX. unfold list_max_value. lia.
  - induction SORT as [|a rest SORT IH ALL]; cbn [si_split].
    + repeat constructor.
    + inversion BOUNDS; subst. destruct (si_value a <=? si_value new) eqn:LE.
      * apply N.leb_le in LE. destruct (si_split (si_value new) rest) as [lo hi] eqn:CUT.
        cbn in *. constructor.
        -- apply IH. assumption.
        -- rewrite Forall_forall in *. intros b IN.
           apply in_app_iff in IN. destruct IN as [IN|[EQ|IN]].
           ++ apply ALL. rewrite (si_split_partition rest (si_value new)), CUT.
              apply in_app_iff. now left.
           ++ subst b. exact LE.
           ++ apply ALL. rewrite (si_split_partition rest (si_value new)), CUT.
              apply in_app_iff. now right.
      * apply N.leb_gt in LE. cbn. constructor.
        -- constructor; assumption.
        -- constructor; [unfold si_order; lia|].
           eapply Forall_impl; [|exact ALL]. intros b AB. unfold si_order in *. lia.
Qed.
Print Assumptions si_result_sorted.

Lemma si_apply_word_frame : forall writes m a,
  (forall w v, In (w,v) writes -> separate32 a 4 w 4) ->
  getmem 32 LittleE 4 (si_apply m writes) a = getmem 32 LittleE 4 m a.
Proof.
  induction writes as [|[w v] rest IH]; intros m a OUT.
  - reflexivity.
  - change (getmem 32 LittleE 4 (si_apply (write_field32 m w 0 v) rest) a =
      getmem 32 LittleE 4 m a).
    rewrite (IH (write_field32 m w 0 v) a).
    + unfold write_field32. rewrite N.add_0_r. apply getmem_noverlap.
      apply (OUT w v). now left.
    + intros w' v' IN. apply (OUT w' v'). now right.
Qed.

Lemma si_before_member : forall value xs a,
  In a (si_before value xs) -> In a xs.
Proof.
  intros value xs a IN. rewrite (si_cut_partition xs value).
  apply in_or_app. now left.
Qed.
Lemma si_after_member : forall value xs a,
  In a (si_after value xs) -> In a xs.
Proof.
  intros value xs a IN. rewrite (si_cut_partition xs value).
  apply in_or_app. now right.
Qed.
Lemma si_last_member : forall sentinel ys,
  si_last sentinel ys=sentinel \/
  exists a, In a ys /\ si_last sentinel ys=si_ptr a.
Proof.
  intros sentinel ys. unfold si_last. destruct (rev ys) as [|a rest] eqn:E.
  - now left.
  - right. exists a. split; [|reflexivity].
    apply in_rev. rewrite E. now left.
Qed.
Lemma si_first_member : forall sentinel ys,
  si_first sentinel ys=sentinel \/
  exists a, In a ys /\ si_first sentinel ys=si_ptr a.
Proof.
  intros sentinel [|a rest]; [now left|].
  right. exists a. split; [now left|reflexivity].
Qed.
Lemma si_endpoints : forall L new xs,
  (si_prev L new xs=L+8 \/ exists a, In a xs /\ si_prev L new xs=si_ptr a) /\
  (si_next L new xs=L+8 \/ exists a, In a xs /\ si_next L new xs=si_ptr a).
Proof.
  intros. split.
  - destruct (si_last_member (L+8) (si_before (si_value new) xs))
      as [E|[a [IN E]]]; [now left|].
    right. exists a. split; [eapply si_before_member; exact IN|exact E].
  - destruct (si_first_member (L+8) (si_after (si_value new) xs))
      as [E|[a [IN E]]]; [now left|].
    right. exists a. split; [eapply si_after_member; exact IN|exact E].
Qed.

Lemma si_stack_body_separate : forall L new sp xs a,
  si_layout L (si_ptr new) sp xs ->
  (a=L+8 \/ exists node, In node xs /\ a=si_ptr node) ->
  separate32 (sp-12) 12 (a+4) 4 /\ separate32 (sp-12) 12 (a+8) 4.
Proof.
  intros L new sp xs a LAY EP.
  destruct LAY as [LO [PO [SB [ST [SA [PL [SL [SP [NODES REST]]]]]]]]].
  destruct EP as [->|[node [IN ->]]].
  - split.
    + replace (L+8+4) with (L+12) by lia.
      exact (noverlap_index_r 32 (sp-12) 12 L 20 12 4 SL ltac:(discriminate)).
    + replace (L+8+8) with (L+16) by lia.
      exact (noverlap_index_r 32 (sp-12) 12 L 20 16 4 SL ltac:(discriminate)).
  - rewrite Forall_forall in NODES. specialize (NODES node IN).
    destruct NODES as [_ [_ [_ [_ [_ SN]]]]].
    split; (eapply noverlap_index_r; [exact SN|discriminate]).
Qed.

Lemma si_body_spill_frame : forall s0 L new xs a,
  si_layout L (si_ptr new) (s0 R_SP) xs ->
  separate32 a 4 (si_ptr new) 20 ->
  separate32 a 4 L 20 ->
  separate32 a 4 (si_prev L new xs+4) 4 ->
  separate32 a 4 (si_next L new xs+8) 4 ->
  getmem 32 LittleE 4 (si_memory s0 L new xs) a =
  getmem 32 LittleE 4 (si_stackmem s0) a.
Proof.
  intros s0 L new xs a LAY AP AL APR ANX.
  unfold si_memory. apply si_apply_word_frame.
  intros w v IN. unfold si_body_writes in IN. cbn [In] in IN.
  destruct IN as [E|[E|[E|[E|[E|[E|E]]]]]];
    try contradiction; inversion E; subst w v.
  - exact (noverlap_index_r 32 a 4 (si_ptr new) 20 4 4 AP ltac:(discriminate)).
  - exact ANX.
  - exact (noverlap_index_r 32 a 4 (si_ptr new) 20 8 4 AP ltac:(discriminate)).
  - exact APR.
  - exact (noverlap_index_r 32 a 4 (si_ptr new) 20 16 4 AP ltac:(discriminate)).
  - replace L with (L+0) at 1 by lia.
    exact (noverlap_index_r 32 a 4 L 20 0 4 AL ltac:(discriminate)).
Qed.

Lemma si_stack_read : forall s0,
  models armv6mtypctx s0 -> 12 <= s0 R_SP -> s0 R_SP < 2^32 ->
  getmem 32 LittleE 4 (si_stackmem s0) (s0 R_SP-12)=s0 R_R4 /\
  getmem 32 LittleE 4 (si_stackmem s0) (s0 R_SP-8)=s0 R_R5 /\
  getmem 32 LittleE 4 (si_stackmem s0) (s0 R_SP-4)=s0 R_LR.
Proof.
  intros s0 MDL SB ST.
  unfold si_stackmem, si_stack_writes, si_apply, si_write, write_field32.
  cbn [fold_left fst snd]. rewrite !N.add_0_r.
  repeat apply conj;
    repeat lazymatch goal with
    | |- getmem 32 LittleE 4 (setmem 32 LittleE 4 ?M ?W ?V) ?A = _ =>
      first [constr_eq W A; rewrite getmem_setmem by discriminate
        | rewrite getmem_noverlap by
            (apply ranges32_separate; clear - SB ST; unfold range32; lia)]
    end;
    apply N.mod_small; apply MDL; reflexivity.
Qed.

Lemma si_memory_spill_frame : forall s0 L new xs off,
  si_layout L (si_ptr new) (s0 R_SP) xs -> off+4 <= 12 ->
  getmem 32 LittleE 4 (si_memory s0 L new xs) (s0 R_SP-12+off) =
  getmem 32 LittleE 4 (si_stackmem s0) (s0 R_SP-12+off).
Proof.
  intros s0 L new xs off LAY OFF.
  pose proof LAY as LAY0.
  destruct LAY as [LO [PO [SB [ST [SA [PL [SL [SP REST]]]]]]]].
  destruct (si_endpoints L new xs) as [EP EN].
  destruct (si_stack_body_separate L new (s0 R_SP) xs (si_prev L new xs) LAY0 EP)
    as [SPR _].
  destruct (si_stack_body_separate L new (s0 R_SP) xs (si_next L new xs) LAY0 EN)
    as [_ SNX].
  apply si_body_spill_frame; [exact LAY0| | | | ];
    eapply noverlap_index_l; eassumption.
Qed.

Lemma si_memory_stack_read : forall s0 L new index xs,
  models armv6mtypctx s0 -> si_pre s0 L new index xs ->
  getmem 32 LittleE 4 (si_memory s0 L new xs) (s0 R_SP-12)=s0 R_R4 /\
  getmem 32 LittleE 4 (si_memory s0 L new xs) (s0 R_SP-8)=s0 R_R5 /\
  getmem 32 LittleE 4 (si_memory s0 L new xs) (s0 R_SP-4)=s0 R_LR.
Proof.
  intros s0 L new index xs MDL [LAY REST].
  pose proof LAY as FULL.
  destruct LAY as [LO [PO [SB [ST LAY]]]].
  destruct (si_stack_read s0 MDL SB ST) as [R4 [R5 LR]].
  pose proof (si_memory_spill_frame s0 L new xs 0 FULL ltac:(discriminate)) as F0.
  pose proof (si_memory_spill_frame s0 L new xs 4 FULL ltac:(discriminate)) as F4.
  pose proof (si_memory_spill_frame s0 L new xs 8 FULL ltac:(discriminate)) as F8.
  rewrite N.add_0_r in F0.
  replace (s0 R_SP-12+4) with (s0 R_SP-8) in F4 by (clear - SB; lia).
  replace (s0 R_SP-12+8) with (s0 R_SP-4) in F8 by (clear - SB; lia).
  rewrite F0, F4, F8. auto.
Qed.

(* The abstract memory splice is proved separately from machine stepping. *)
Theorem si_memory_refinement : forall s0 L new index xs,
  si_pre s0 L new index xs ->
  si_memory_post s0 L new index xs (update s0 V_MEM32 (si_memory s0 L new xs)).
Proof.
  (* Restored original attempt is retained in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.

Theorem sorted_insert_correct : forall s0 t s' x' L new index xs,
  startof t (x',s')=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  satisfies_all vListInsert_armv6m_prog (si_invs s0 L new index xs)
    si_exit ((x',s')::t).
Proof.
  (* Restored original attempt is retained in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.

Theorem sorted_insert_at_pop : forall s0 t s L new index xs,
  startof t (Addr 0x9a,s)=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  exec_prog vListInsert_armv6m_prog ((Addr 0x9a,s)::t) ->
  unterminated si_exit t -> si_at_pop s0 L new index xs s.
Proof.
  (* Restored original attempt is retained in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.

Lemma si_eval_load_plus : forall c s off value,
  c V_MEM32=Some (8*2^32) -> c R_SP=Some 32 ->
  s R_SP+off < 2^32 -> field32 (s V_MEM32) (s R_SP) off=value ->
  MemAcc mem_readable s (s R_SP+off) 32 4 ->
  eval_exp c s (Load (Var V_MEM32)
    (BinOp OP_PLUS (Var R_SP) (Word off 32)) LittleE 4) value 32.
Proof.
  intros c s off value CM CS B RD ACC.
  unfold field32 in RD. rewrite <- RD.
  assert (PLUS: eval_binop OP_PLUS 32 (s R_SP) off=s R_SP+off).
  { cbn [eval_binop]. apply N.mod_small. exact B. }
  rewrite <- PLUS.
  eapply ELoad with (w:=32).
  - apply EVar. exact CM.
  - apply EBinOp; [apply EVar; exact CS|apply EWord].
  - rewrite PLUS. exact ACC.
Qed.

Lemma si_eval_load_minus4 : forall c s value,
  c V_MEM32=Some (8*2^32) -> c R_SP=Some 32 ->
  4 <= s R_SP -> s R_SP < 2^32 ->
  getmem 32 LittleE 4 (s V_MEM32) (s R_SP-4)=value ->
  MemAcc mem_readable s (s R_SP-4) 32 4 ->
  eval_exp c s (Load (Var V_MEM32)
    (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4) value 32.
Proof.
  intros c s value CM CS SB ST RD ACC. rewrite <- RD.
  assert (MINUS: eval_binop OP_MINUS 32 (s R_SP) 4=s R_SP-4).
  { cbn [eval_binop]. rewrite msub_sub by exact SB.
    apply N.mod_small. clear - ST; lia. }
  rewrite <- MINUS.
  eapply ELoad with (w:=32).
  - apply EVar. exact CM.
  - apply EBinOp; [apply EVar; exact CS|apply EWord].
  - rewrite MINUS. exact ACC.
Qed.

Ltac si_updates :=
  repeat first [rewrite update_frame by discriminate | rewrite update_updated].

Lemma si_pop_execution : forall s sp a b lr,
  s R_SP=sp -> sp+12 < 2^32 ->
  field32 (s V_MEM32) sp 0=a -> field32 (s V_MEM32) sp 4=b ->
  field32 (s V_MEM32) sp 8=lr -> lr mod 2=1 ->
  MemAcc mem_readable s sp 32 4 ->
  MemAcc mem_readable s (sp+4) 32 4 ->
  MemAcc mem_readable s (sp+8) 32 4 ->
  exists c', exec_stmt armv6mtypctx s (armv6m_pop 48 true) c'
    (update (update (update s R_R4 a) R_R5 b) R_SP (sp+12))
    (Some (Addr (N.land lr 0xfffffffe))).
Proof.
  intros s sp a b lr SP B R4 R5 LR ODD A0 A4 A8.
  set (s1:=update s R_R4 a).
  set (s2:=update s1 R_R5 b).
  set (sr:=update s2 R_SP (sp+12)).
  set (c1:=update armv6mtypctx R_R4 (Some 32)).
  set (c2:=update c1 R_R5 (Some 32)).
  set (cr:=update c2 R_SP (Some 32)).
  exists cr.
  change (exec_stmt armv6mtypctx s
    (Seq (Move R_R4 (Load (Var V_MEM32)
      (BinOp OP_PLUS (Var R_SP) (Word 0 32)) LittleE 4))
    (Seq (Move R_R5 (Load (Var V_MEM32)
      (BinOp OP_PLUS (Var R_SP) (Word 4 32)) LittleE 4))
    (Seq (Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 12 32)))
      (armv6m_bxwritepc (Load (Var V_MEM32)
        (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4)))))
    cr sr (Some (Addr (N.land lr 0xfffffffe)))).
  eapply XSeq2 with (c2:=c1) (s2:=s1).
  - apply XMove. apply si_eval_load_plus; try reflexivity;
      rewrite SP, ?N.add_0_r; try exact R4; try exact A0; clear - B; lia.
  - eapply XSeq2 with (c2:=c2) (s2:=s2).
    + apply XMove. apply si_eval_load_plus.
      * reflexivity.
      * reflexivity.
      * unfold s1. si_updates. rewrite SP. clear - B; lia.
      * unfold s1. si_updates. rewrite SP. exact R5.
      * unfold MemAcc, mem_readable, s1. si_updates. rewrite SP. exact A4.
    + eapply XSeq2 with (c2:=cr) (s2:=sr).
      * apply XMove.
        assert (ADD: eval_binop OP_PLUS 32 (s2 R_SP) 12=sp+12).
        { unfold s2, s1. si_updates. rewrite SP.
          cbn [eval_binop]. apply N.mod_small. exact B. }
        rewrite <- ADD. apply EBinOp; [apply EVar; reflexivity|apply EWord].
      * assert (ELR: eval_exp cr sr (Load (Var V_MEM32)
          (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4) lr 32).
        { apply si_eval_load_minus4.
          - reflexivity.
          - reflexivity.
          - unfold sr. rewrite update_updated. lia.
          - unfold sr. rewrite update_updated. exact B.
          - unfold sr, s2, s1. si_updates.
            replace (sp+12-4) with (sp+8) by lia. exact LR.
          - unfold MemAcc, mem_readable, sr, s2, s1. si_updates.
            replace (sp+12-4) with (sp+8) by lia. exact A8. }
        unfold armv6m_bxwritepc. eapply XIf with (b:=1).
        -- assert (COND: eval_exp cr sr
             (Cast CAST_LOW 1 (Load (Var V_MEM32)
               (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4))
             (cast CAST_LOW 32 1 lr) 1) by (apply ECast; exact ELR).
           assert (CAST: cast CAST_LOW 32 1 lr=1) by exact ODD.
           rewrite CAST in COND. exact COND.
        -- eapply XJmp with (w:=32). change (eval_exp cr sr
             (BinOp OP_AND (Load (Var V_MEM32)
               (BinOp OP_MINUS (Var R_SP) (Word 4 32)) LittleE 4)
               (Word 0xfffffffe 32)) (eval_binop OP_AND 32 lr 0xfffffffe) 32).
           apply EBinOp; [exact ELR|apply EWord].
Qed.
Print Assumptions si_pop_execution.

Theorem sorted_insert_return_step : forall s0 s L new index xs,
  models armv6mtypctx s0 -> si_pre s0 L new index xs -> si_at_pop s0 L new index xs s ->
  exists sr, can_step vListInsert_armv6m_prog
    ((Addr (N.land (s0 R_LR) 0xfffffffe),sr),(Addr 0x9a,s)) /\
    si_returned s0 L new index xs sr.
Proof.
  intros s0 s L new index xs MDL INPUT POST.
  idtac "BEGIN return".
  pose proof (si_memory_stack_read s0 L new index xs MDL INPUT) as [SR4 [SR5 SLR]].
  pose proof INPUT as INPUT0.
  destruct INPUT as [LAY [_ [_ [_ [_ [_ [_ [_ [_ [PERM [ODD LRBOUND]]]]]]]]]]].
  destruct LAY as [LO [PO [SB [ST REST]]]].
  destruct POST as [MP [R4 [R5 [SP [R2 [R3 [FLAGS KEEP]]]]]]].
  pose proof (proj1 MP) as MEM.
  assert (STACK: forall a, In a [s0 R_SP-12;s0 R_SP-8;s0 R_SP-4] ->
    MemAcc mem_readable s a 32 4).
  { intros a IN. unfold MemAcc, mem_readable.
    rewrite (KEEP A_READ I).
    exact (proj1 (PERM a ltac:(unfold si_access_words; apply in_or_app;
      left; cbn [In] in *; tauto))). }
  assert (BASE: s0 R_SP-12+12=s0 R_SP) by (clear - SB; lia).
  assert (OFF4: s0 R_SP-12+4=s0 R_SP-8) by (clear - SB; lia).
  assert (OFF8: s0 R_SP-12+8=s0 R_SP-4) by (clear - SB; lia).
  destruct (si_pop_execution s (s0 R_SP-12) (s0 R_R4) (s0 R_R5) (s0 R_LR)
    SP ltac:(rewrite BASE; exact ST)
    ltac:(unfold field32; rewrite N.add_0_r, MEM; exact SR4)
    ltac:(unfold field32; rewrite OFF4, MEM; exact SR5)
    ltac:(unfold field32; rewrite OFF8, MEM; exact SLR)
    ODD ltac:(apply STACK; now left)
    ltac:(rewrite OFF4; apply STACK; cbn; tauto)
    ltac:(rewrite OFF8; apply STACK; cbn; tauto)) as [cr EXEC].
  rewrite BASE in EXEC.
  set (sr:=update (update (update s R_R4 (s0 R_R4)) R_R5 (s0 R_R5)) R_SP (s0 R_SP)).
  exists sr. split.
  - assert (RESET: reset_temps s sr=sr).
    { unfold sr, reset_temps, reset_vars. apply functional_extensionality.
      intro v. destruct v; reflexivity. }
    rewrite <- RESET.
    change (can_step vListInsert_armv6m_prog
      ((exitof (0x9a+2) (Some (Addr (N.land (s0 R_LR) 0xfffffffe))),
        reset_temps s sr),(Addr 0x9a,s))).
    eapply CanStep; [reflexivity|exact EXEC].
  - unfold si_returned. split.
    + unfold si_memory_post. unfold sr. si_updates. exact MP.
    + split; [unfold sr; si_updates; reflexivity|].
      split; [unfold sr; si_updates; reflexivity|].
      split; [unfold sr; si_updates; reflexivity|].
      split; [unfold sr; si_updates; exact R2|].
      split; [unfold sr; si_updates; exact R3|].
      split.
      * unfold si_flags, sr in *. si_updates. exact FLAGS.
      * intros v V. unfold sr. destruct v; cbn [si_preserved] in V;
          try contradiction; si_updates; apply KEEP; exact V.
Qed.
Print Assumptions sorted_insert_return_step.
Theorem sorted_insert_trace_returns : forall s0 t s L new index xs,
  startof t (Addr 0x9a,s)=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  exec_prog vListInsert_armv6m_prog ((Addr 0x9a,s)::t) ->
  unterminated si_exit t -> exists sr,
    si_returned s0 L new index xs sr /\
    exec_prog vListInsert_armv6m_prog
      ((Addr (N.land (s0 R_LR) 0xfffffffe),sr)::(Addr 0x9a,s)::t).
Proof.
  (* Restored original attempt is retained in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.

(* Finite images witness the entry specification. No source-level substitute
   for vListInsert is used; these functions only initialize test memory. *)
Fixpoint si_fixture_nodes m L previous (xs:list si_node) :=
  match xs with [] => write_field32 m (L+8) 8 previous
  | a::rest => si_fixture_nodes
      (image20 m (si_ptr a) (si_value a) (si_first (L+8) rest)
        previous (si_owner a) L) L (si_ptr a) rest
  end.
Definition si_fixture L new xs :=
  si_fixture_nodes
    (image20 (image20 0 L (N.of_nat (length xs)) (L+8) list_max_value
      (si_first (L+8) xs) (si_last (L+8) xs))
      (si_ptr new) (si_value new) 0 0 (si_owner new) 0) L (L+8) xs.
Definition si_entry m L P : store :=
  update (update (update (update (update (update (memory_store32 m)
    A_READ (N.ones (2^32))) A_WRITE (N.ones (2^32))) R_R0 L) R_R1 P)
    R_SP 65536) R_LR 257.
Definition si_new := SiNode 8192 7 42.
Definition si_one := SiNode 12288 7 43.
Definition si_two := SiNode 16384 11 44.
Lemma si_fixture_nodes_typed : forall xs m L previous,
  m < memsize 32 -> si_fixture_nodes m L previous xs < memsize 32.
Proof.
  induction xs as [|a xs IH]; intros m L previous MT.
  - cbn [si_fixture_nodes]. unfold write_field32. apply setmem_welltyped. exact MT.
  - cbn [si_fixture_nodes]. apply IH. apply image20_welltyped. exact MT.
Qed.

Lemma si_fixture_typed : forall L new xs, si_fixture L new xs < memsize 32.
Proof.
  intros. unfold si_fixture. apply si_fixture_nodes_typed.
  repeat apply image20_welltyped.
  assert (Z: forall w, 0 < memsize w).
  { intro w. change (0 < 2^(2^w*8)). apply mp2_gt_0. }
  exact (Z 32).
Qed.

Lemma si_entry_typed : forall m L P,
  m < memsize 32 -> L < 2^32 -> P < 2^32 ->
  models armv6mtypctx (si_entry m L P).
Proof.
  intros m L P MT LB PB. unfold si_entry.
  apply models_update; [reflexivity|].
  apply models_update; [reflexivity|].
  apply models_update; [exact PB|].
  apply models_update; [exact LB|].
  apply models_update; [apply ones_bound|].
  apply models_update; [apply ones_bound|].
  apply memory_store32_welltyped. exact MT.
Qed.

Lemma si_entry_access : forall m L P a,
  MemAcc mem_readable (si_entry m L P) a 32 4 /\
  MemAcc mem_writable (si_entry m L P) a 32 4.
Proof.
  intros. split; intros n BN; unfold mem_readable, mem_writable, si_entry;
    repeat rewrite update_frame by discriminate; rewrite update_updated;
    apply N.ones_spec_low; apply mp2_mod_lt.
Qed.

(* Only word addresses and scalar values are computed; memory stays opaque. *)
Ltac si_fixture_read :=
  unfold field32, image20, write_field32,
    item_value_offset, item_next_offset, item_previous_offset,
    item_owner_offset, item_container_offset,
    list_count_offset, list_index_offset, list_end_offset;
  repeat lazymatch goal with
  | |- getmem 32 LittleE 4 (setmem 32 LittleE 4 ?M ?W ?V) ?A = ?R =>
    let w := eval vm_compute in W in
    let a := eval vm_compute in A in
    change (getmem 32 LittleE 4 (setmem 32 LittleE 4 M w V) a = R);
    first [ constr_eq w a;
            rewrite getmem_setmem by discriminate
          | rewrite getmem_noverlap by
              (apply ranges32_separate; unfold range32; lia) ]
  end;
  reflexivity.

Theorem sorted_insert_nonvacuity : forall xs,
  xs=[] \/ xs=[si_one] \/ xs=[si_one;si_two] ->
  exists s, models armv6mtypctx s /\ si_pre s 4096 si_new 4104 xs.
Proof.
  intros xs CASES. idtac "BEGIN witness". exists (si_entry (si_fixture 4096 si_new xs) 4096 8192).
  split.
  - apply si_entry_typed; [apply si_fixture_typed|reflexivity|reflexivity].
  - destruct CASES as [->|[->|->]];
      unfold si_pre;
      repeat rewrite update_frame by discriminate;
      cbn [si_entry update];
      unfold si_layout, si_ring, si_chain, si_apart, si_ordinary_return,
        si_fixture, si_new, si_one, si_two;
      cbn [si_fixture_nodes si_first si_last rev length N.of_nat si_ptr si_value si_owner];
      repeat split.
    all: try solve [apply si_entry_access].
    all: try solve [unfold si_permissions; intros; apply si_entry_access].
    all: try solve [unfold object32, range32; vm_compute; repeat split; congruence].
    all: try solve [apply ranges32_separate; unfold range32; lia].
    all: try solve [repeat constructor; unfold si_order; cbn; congruence].
    all: try solve [unfold list_header, item_contents; repeat split; si_fixture_read].
    all: try solve [si_fixture_read].
Qed.
Print Assumptions sorted_insert_nonvacuity.
