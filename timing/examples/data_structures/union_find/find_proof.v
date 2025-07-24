Require Import union_find.
Require Import riscvTiming.
Import RISCVNotations.
Require Import timing_auto.

Module findTime <: TimingModule.
    Definition time_of_addr (s : store) (a : addr) : N :=
        match neorv32_cycles_upper_bound s (union_find_bin a) with
        | Some x => x | _ => 999 end.

    Definition entry_addr : N := 0x44c.

    Definition exits (t:trace) : bool :=
    match t with (Addr a,_)::_ => match a with
    | 0x478 => true
    | _ => false
  end | _ => false end.
End findTime.

Module findAuto := TimingAutomation findTime.
Import findTime findAuto.

Definition set_size (mem : addr -> N) (set : addr) : N :=
    mem Ⓓ[set].
Definition set_parent (mem : addr -> N) (set : addr) : addr :=
    mem Ⓓ[set + 4].
Definition nth_parent (mem : addr -> N) (set : addr) (n : N) : N :=
    mem Ⓓ[set_parent mem set + (n << 2)].
Definition set_rank (mem : addr -> N) (set : addr) : addr :=
    mem Ⓓ[set + 8].
Definition nth_rank (mem : addr -> N) (set : addr) (n : N) : N :=
    mem Ⓓ[set_rank mem set + (n << 2)].

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint _node_parent (mem : addr -> N) (set : addr) (node : N) (fuel : nat) : N :=
    match fuel with
    | O => if N.eq_dec node (nth_parent mem set node) then
            node
           else
            1 + set_size mem set
    | S fuel' =>
        if N.eq_dec node (nth_parent mem set node) then
            node
        else
            _node_parent mem set (nth_parent mem set node) fuel'
    end.
Definition node_parent mem set node :=
    _node_parent mem set node (N.to_nat (set_size mem set)).

Fixpoint _node_parent_dist (mem : addr -> N) (set node parent : addr) (fuel : nat) : option N :=
    match fuel with
    | O => if N.eq_dec node parent then
            Some 0
           else
            None
    | S fuel' => 
        if N.eq_dec node parent then 
            Some 0
        else
            match _node_parent_dist mem set (nth_parent mem set node) parent fuel' with
            | Some x => Some (1 + x)
            | None => None
            end
    end.
Definition node_parent_dist mem set node parent :=
    _node_parent_dist mem set node parent (N.to_nat (set_size mem set)).

Lemma _node_parent_dist_0 : forall mem set x fuel,
    _node_parent_dist mem set x x fuel = Some 0.
Proof.
    intros. destruct fuel;
    simpl; (destruct N.eq_dec; [reflexivity|contradiction]).
Qed.

Lemma _node_parent_dist_Sfuel : forall fuel mem set x y dist,
    _node_parent_dist mem set x y fuel = Some dist ->
    _node_parent_dist mem set x y (S fuel) = Some dist.
Proof.
    induction fuel; intros.
        simpl in H. destruct N.eq_dec in H.
            now rewrite e, _node_parent_dist_0.
        inversion H.
    simpl in H. destruct N.eq_dec in H.
        subst. inversion H. simpl.
        destruct N.eq_dec. reflexivity. contradiction.
    simpl. destruct N.eq_dec. contradiction.
    destruct N.eq_dec. rewrite <- e in *.
        now rewrite _node_parent_dist_0 in H.
    destruct fuel; simpl in H.
        destruct N.eq_dec. contradiction. inversion H.
    destruct N.eq_dec in H. contradiction.
    
Qed.

Lemma _node_parent_dist_0_inv : forall fuel mem set x y,
    _node_parent_dist mem set x y fuel = 0 ->
    x = y.
Proof.
    induction fuel; intros.
        simpl in H. destruct N.eq_dec in H. assumption.
        lia.
    eapply IHfuel, _node_parent_dist_Sfuel_0, H.
Qed.

Lemma _node_parent_dist_nonzero_impl_fuel_nonzero : forall fuel mem set x y dist,
    x <> y ->
    dist <> set_size mem set ->
    _node_parent_dist mem set x y (N.to_nat fuel) = N.succ dist ->
    0 < fuel.
Proof.
    destruct fuel using N_peano_ind_Set; intros.
        simpl in H1. destruct N.eq_dec in H1.
            contradiction.
        rewrite N.add_1_l in H1.
        apply N.succ_inj in H1. subst. contradiction.
    lia.
Qed.

Lemma node_parent_dist_next (mem : addr -> N) (set : addr) (x y dist : N) :
    0 < set_size mem set ->
    x <> y ->
    dist <> set_size mem set ->
    node_parent_dist mem set x y = N.succ dist ->
    node_parent_dist mem set (nth_parent mem set x) y = dist.
Proof.
    intros. unfold node_parent_dist in *.
    revert dist x y H1 H0 H H2.
    induction (set_size mem set) using N_peano_ind_Set; intros.
        lia.
    rewrite N2Nat.inj_succ in *. cbn [_node_parent_dist] in *.
    destruct N.eq_dec.
        contradiction. clear n0.
    rewrite N.add_1_l in H2. apply N.succ_inj in H2.
    destruct (N.eq_dec (nth_parent mem set x) y).
    destruct n using N_peano_ind_Set.
        simpl in H2. rewrite e in H2.
            destruct N.eq_dec. assumption. contradiction.
        rewrite e in *. rewrite _node_parent_dist_0 in H2.
        now symmetry.
    destruct dist using N_peano_ind_Set.
        apply _node_parent_dist_0_inv in H2. contradiction.
    rewrite IHn with (dist := dist). apply N.add_1_l.
        intro. subst. contradiction.
        assumption.
    apply (_node_parent_dist_nonzero_impl_fuel_nonzero 
            n mem set (nth_parent mem set x) y dist n0).
    destruct (N.eq_dec n 0).
        subst. simpl in *. destruct N.eq_dec in H1.
        contradiction.
    lia.
Admitted.

Definition time_of_find (mem : addr -> N) (set : addr) (x : N)
        (parent : addr) (t : trace):=
    cycle_count_of_trace t =
        (* setup time *)
        time_mem + 2 +
        (* find loop *)
        (node_parent_dist mem set x parent) *
        (2 + (3 + 2) + 2 + time_mem + time_branch) +
        (2 + (3 + 2) + 2 + time_mem + 3) +
        (* path compression loop *)
        (node_parent_dist mem set x parent) *
        ((3 + 2) + 2 + time_mem + time_branch + time_mem + time_branch) +
        ((3 + 2) + 2 + time_mem + 3) +
        (* return *)
        time_branch.

Definition find_timing_invs (s : store) (base_mem : addr -> N)
    (set : addr) (x : N) (parent : addr) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x44c => Some (s R_A0 = Ⓓx /\ s R_A1 = Ⓓset /\ s V_MEM32 = Ⓜbase_mem /\
                    cycle_count_of_trace t' = 0)
| 0x454 => Some (exists a4 curr_dist,
                    s V_MEM32 = Ⓜbase_mem /\ s R_A4 = Ⓓa4 /\
                    node_parent_dist base_mem set a4 parent = curr_dist /\
                    cycle_count_of_trace t' =
                        time_mem + 2 +
                        (node_parent_dist base_mem set x parent - curr_dist) *
                        (2 + (3 + 2) + 2 + time_mem + time_branch))
| 0x101c8 => Some (time_of_find base_mem set x parent t)
| _ => None end | _ => None end.

Definition lifted_find : program :=
    lift_riscv union_find_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Definition NULL : N := 0.
Definition set_well_formed (mem : addr -> N) (set : addr) :=
    (* struct validity *)
    0 < set_size mem set /\
    set_parent mem set <> NULL /\
    set_rank mem set <> NULL /\
    (* parent is a forest *)
    (forall i, i < set_size mem set ->
        nth_parent mem set i < set_size mem set).

Theorem find_timing:
  forall s t s' x' base_mem x set
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (A0: s R_A0 = Ⓓx)
         (A2: s R_A1 = Ⓓset)
         (* union-find DS is well-formed *)
         (WF: set_well_formed base_mem set)
         (* x is a node in the DS *)
         (IN: x < set_size base_mem set),
  satisfies_all 
    lifted_find
    (find_timing_invs s base_mem set x (node_parent base_mem set x))
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := time rv_step.

    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x44c -> 0x454 *)
    destruct PRE as (A0 & A1 & Mem & Cycles).
    repeat step. exists x, 
        (node_parent_dist base_mem set x (node_parent base_mem set x)).
    repeat split. hammer.

    (* 0x454 -> *)
    destruct PRE as (root & curr_dist & Mem &A4 & CurrDist & Cycles).
    do 5 step.
        (* haven't found root yet *)
        eexists. exists (curr_dist - 1). repeat split.

        (* found root *)
Qed.
            

