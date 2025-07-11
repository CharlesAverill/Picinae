Require Import linked_list.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto. 

Module find_in_linked_listTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (linked_list_bin a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x10250.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x102b8 => true
    | _ => false
  end | _ => false end.
End find_in_linked_listTime.

Module find_in_linked_listAuto := TimingAutomation find_in_linked_listTime.
Import find_in_linked_listTime find_in_linked_listAuto.

Definition list_node_value (mem : addr -> N) (node : addr) : N :=
    mem Ⓓ[node].
Definition list_node_next (mem : addr -> N) (node : addr) : N :=
    mem Ⓓ[4 + node].
Definition NULL : N := 0.

Inductive key_in_linked_list : (addr -> N) -> addr -> N -> nat -> Prop :=
| KeyAtHead mem node key :
    list_node_value mem node = key ->
    key_in_linked_list mem node key 0
| KeyAtNext mem node key idx :
    key_in_linked_list mem (list_node_next mem node) key idx ->
    key_in_linked_list mem node key (S idx).

Fixpoint key_in_linked_list_dec (mem : addr -> N) (node : addr) (key : N) (idx : nat)
        : {key_in_linked_list mem node key idx} + {~ key_in_linked_list mem node key idx}.
    destruct idx as [| idx'].
    - (* Base case: idx = 0 *)
        destruct (N.eq_dec (list_node_value mem node) key) as [Heq | Hneq].
        + left. constructor. exact Heq.
        + right. intros H. inversion H. subst. contradiction.
    - (* Inductive case: idx = S idx' *)
        destruct (key_in_linked_list_dec mem (list_node_next mem node) key idx') as [IN | NOT_IN].
        + left. constructor. exact IN.
        + right. intros H. inversion H. subst. apply NOT_IN. assumption.
Qed.

Inductive well_formed_list : (addr -> N) -> addr -> list addr -> Prop :=
| wf_nil : forall mem,
    list_node_next mem NULL <> NULL ->
    well_formed_list mem NULL []
| wf_cons : forall mem n visited,
    n <> NULL ->
    list_node_next mem n <> n ->
    (* next not in visited to avoid cycles *)
    ~ In (list_node_next mem n) visited ->
    well_formed_list mem (list_node_next mem n) (n :: visited) ->
    well_formed_list mem n visited.

Inductive node_distance : addr -> addr -> nat -> Prop :=
| Dst0 node :
    node_distance node node 0
| DstSn mem src dst len :
    well_formed_list mem src [] ->
    src <> dst ->
    node_distance (list_node_next mem src) dst len ->
    node_distance src dst (S len).

Lemma well_formed_impl_next_neq_curr : forall mem src,
    well_formed_list mem src [] ->
    list_node_next mem src <> src.
Proof.
    intros. induction H; subst.
        assumption.
    intro. rewrite H3 in *. contradiction.
Qed.    

Lemma node_distance_len_nonzero : forall head len,
    node_distance head NULL len ->
    negb (head =? NULL) = true ->
    (0 < len)%nat.
Proof.
    intros. revert H0. induction H; intros.
        rewrite N.eqb_refl in H0; inversion H0.
    lia.
Qed.

Lemma node_distance_same : forall h n,
    node_distance h h n -> n = O.
Proof.
    intros. inversion H; subst. reflexivity.
    contradiction.
Qed.

Lemma node_distance_null_dupe : forall head tail n1 n2,
    node_distance head tail n1 ->
    node_distance head tail n2 ->
    n1 = n2.
Abort.
    

Definition time_of_find_in_linked_list (mem : addr -> N) 
        (head : addr) (key : N) (len : nat) (found_idx : option N)
        (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        2 + 2 * time_mem + 2 + 3 * time_mem +
        if head =? NULL then
            3 + 2 + time_branch + 2 + 2 * time_mem + 2 + time_branch
        else (
            time_branch + time_mem + time_branch +
            (match found_idx with None => N.of_nat len | Some idx => idx end) *
            (3 * time_mem + time_branch + 4 * time_mem + time_branch)
        ).

Definition timing_postcondition (mem : addr -> N) (head : addr)
        (key : N) (t : trace) : Prop :=
    exists len, node_distance head NULL len /\
    time_of_find_in_linked_list mem head key len None t.

Definition find_in_linked_list_timing_invs (s : store) (base_mem : addr -> N)
    (sp : N) (head : addr) (key : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x10250 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_SP = Ⓓsp /\
    s R_A0 = Ⓓhead /\ s R_A1 = Ⓓkey /\
    node_distance head NULL len /\
    cycle_count_of_trace t' = 0)
| 0x10278 => Some (exists ctr mem curr, s V_MEM32 = Ⓜmem /\ mem Ⓓ[sp ⊖ 20] = curr /\
    s R_S0 = Ⓓsp /\
    node_distance head curr ctr /\
    node_distance head NULL len /\
    (ctr < len)%nat /\
    (head =? NULL) = false /\
    cycle_count_of_trace t' = 
        (* startup time *)
        2 + 2 * time_mem + 2 + 3 * time_mem + time_branch + time_mem + time_branch +
        (* loop iterations *)
        (N.of_nat ctr) *
        (3 * time_mem + time_branch + 4 * time_mem + time_branch))
| 0x102b8 => Some (timing_postcondition base_mem head key t)
| _ => None end | _ => None end.

Definition lifted_find_in_linked_list : program :=
    lift_riscv linked_list_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Lemma Npos_P_of_succ_nat :
    forall n : nat, N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n).
Proof. lia. Qed.

Theorem find_in_linked_list_timing:
  forall s t s' x' base_mem sp head key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (SP: s R_SP = Ⓓsp)
         (A0: s R_A0 = Ⓓhead)
         (A1: s R_A1 = Ⓓkey)
         (* list length is finite *)
         (LEN: node_distance head NULL len),
  satisfies_all 
    lifted_find_in_linked_list
    (find_in_linked_list_timing_invs s base_mem sp head key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x10250 -> 0x10278 *)
    destruct PRE as (Mem & SP & A0 & A1 & Len & Cycles).
    repeat step.
    (* 0x10278 *) {
        exists 0%nat. eexists. exists head.
        repeat split; auto. now psimpl.
        constructor. eauto using node_distance_len_nonzero. 
        now apply Bool.negb_true_iff.
        hammer.
    }

    (* head = NULL, contradiction because we checked at the start *)
    inversion BC.

    (* head = null, postcondition *)
    unfold timing_postcondition. exists 0%nat. split. 
    apply Bool.negb_false_iff, N.eqb_eq in BC. subst.
        constructor.
    unfold time_of_find_in_linked_list, NULL.
    hammer.

    (* 0x10278 *)
    destruct PRE as (ctr & mem & curr & Mem & Curr & S0 & Dist & Len & 
        CtrLen & HeadNonNull & Cycles).
    remember 0%nat as fuel; clear Heqfuel.
    destruct (key_in_linked_list_dec base_mem head key fuel) as [IN|NOT_IN].
    (* The key does exist in the linked list *) {
        repeat step.
        (* next iteration *)
            exists (S ctr). repeat eexists; auto.
            psimpl.
                fold (list_node_next mem (mem Ⓓ[ 4294967276 + sp ])).
                constructor.
            fold_big_subs. intro; rewrite H in *; rewrite <- Curr in *.
            revert BC BC0.
                fold (list_node_next mem (mem Ⓓ[ 4294967276 + sp ])).
                fold_big_subs. intros. rewrite Curr in *.
                clear - Dist Len BC0 CtrLen HeadNonNull.
            hammer. find_rewrites. rewrite Npos_P_of_succ_nat, N.mul_succ_l.
            unfold time_mem, time_branch. lia.
        (* curr->next = null *)
            unfold timing_postcondition. exists len.
            repeat split; auto. unfold time_of_find_in_linked_list.
            hammer. find_rewrites. unfold time_mem, time_branch. psimpl.
            replace ctr with len. admit.

    }
Qed.

