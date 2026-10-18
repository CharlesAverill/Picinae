(* Timing proof for binary search on NEORV32.

   The loop body updates left and right without branching (sltu, neg, and,
   andn, or), so every iteration that does not find the key takes body_time,
   and the total time is

       setup_time + k * body_time + (found_exit_time | notfound_exit_time)

   for k non-matching iterations. k is bounded by tracking the size sz of the
   search interval [left, right]:

     - left := mid + 1 shrinks sz to sz/2, and N.size sz decreases by 1
     - right := mid - 1 shrinks sz to (sz-1)/2, and N.log2 (sz+1) decreases by 1

   so k < N.size len when the key is found, and
   N.log2 (len+1) <= k <= N.size len when it is not. Each bound is reached
   for some sorted array. The timing theorem does not assume the array is
   sorted.

   The binary uses the Zbb instruction andn (R5_Andn in Picinae_riscv.v). *)

Require Import binary_search.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import NArith ZArith Lia.
Open Scope N.

(* Machine arithmetic *)

Lemma toZ_small : forall x, x < 2^31 -> toZ 32 x = Z.of_N x.
Proof.
    intros. unfold toZ, canonicalZ. change (Z.pred (Z.of_N 32)) with 31%Z.
    rewrite Z.mod_small; lia.
Qed.

Lemma right_ptr : forall l sz, l + sz < 2^31 ->
    l + sz ⊖ 1 = if l + sz =? 0 then 2^32 - 1 else l + sz - 1.
Proof.
    intros. unfold msub. destruct (N.eqb_spec (l + sz) 0).
    - rewrite e. reflexivity.
    - rewrite (N.mod_small 1) by lia.
      replace (l + sz + (2^32 - 1)) with (l + sz - 1 + 1 * 2^32) by lia.
      rewrite N.mod_add by lia. apply N.mod_small. lia.
Qed.

(* The loop guard [bge right, left] is taken exactly when the interval is non-empty. *)
Lemma loop_guard : forall l sz, l + sz < 2^31 ->
    slt 32 (l + sz ⊖ 1) l = (sz =? 0).
Proof.
    intros. unfold slt. rewrite right_ptr, (toZ_small l) by lia.
    destruct (N.eqb_spec (l + sz) 0).
    - replace sz with 0 by lia. replace l with 0 by lia. reflexivity.
    - rewrite toZ_small by lia. destruct (N.eqb_spec sz 0); lia.
Qed.

Lemma loop_guard_time : forall l sz, l + sz < 2^31 ->
    Z.geb (toZ 32 (l + sz ⊖ 1)) (toZ 32 l) = negb (sz =? 0).
Proof.
    intros. pose proof (loop_guard l sz H) as G. unfold slt in G.
    rewrite Z.geb_leb, Z.leb_antisym, G. reflexivity.
Qed.

(* mid - left = (right - left) >>> 1 = (sz - 1) / 2 *)
Lemma half_width : forall sz, 1 <= sz -> sz < 2^31 ->
    (sz ⊖ 1) >>> 1 = (sz - 1) / 2.
Proof.
    intros. replace (sz ⊖ 1) with (0 + sz ⊖ 1) by reflexivity.
    rewrite right_ptr by lia. replace (0 + sz =? 0) with false by lia.
    unfold ashiftr, sbop1. rewrite toZ_small by lia.
    rewrite Z.shiftr_div_pow2 by lia. unfold ofZ.
    rewrite Z.mod_small.
    - rewrite Z2N.inj_div by lia. rewrite N2Z.id. reflexivity.
    - split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma decr_mod : forall h l, (h ⊖ 1) ⊕ l = l + h ⊖ 1.
Proof.
    intros. unfold msub. rewrite (N.mod_small 1) by lia.
    rewrite N.add_mod_idemp_l by lia. f_equal. lia.
Qed.

(* Logarithmic measures of the search interval *)

Lemma size_mono : forall a b, a <= b -> N.size a <= N.size b.
Proof.
    intros. destruct (N.eqb_spec a 0). subst. simpl. lia.
    pose proof (N.log2_le_mono a b H).
    rewrite (N.size_log2 a), (N.size_log2 b) by lia. lia.
Qed.

Lemma log2_half : forall x, 2 <= x -> N.log2 (x / 2) + 1 = N.log2 x.
Proof.
    intros. change (x / 2) with (x / 2^1). rewrite <- N.shiftr_div_pow2.
    rewrite N.log2_shiftr. assert (1 <= N.log2 x).
    { change 1 with (N.log2 2). apply N.log2_le_mono, H. } lia.
Qed.

(* Moving the left pointer: the interval shrinks to sz/2, and N.size drops by exactly 1. *)
Lemma size_half : forall sz, 1 <= sz -> N.size (sz / 2) + 1 = N.size sz.
Proof.
    intros. destruct (N.eqb_spec sz 1). subst. reflexivity.
    rewrite !N.size_log2. rewrite <- (log2_half sz) by lia. lia.
    lia. intro. apply N.div_small_iff in H0; lia.
Qed.

Lemma size_go_right : forall sz, 1 <= sz -> N.size (sz - 1 - (sz - 1) / 2) + 1 <= N.size sz.
Proof.
    intros. rewrite <- (size_half sz H). apply N.add_le_mono_r, size_mono.
    assert (sz - 1 - (sz - 1) / 2 = sz / 2) by lia.
    lia.
Qed.

Lemma size_go_left : forall sz, 1 <= sz -> N.size ((sz - 1) / 2) + 1 <= N.size sz.
Proof.
    intros. rewrite <- (size_half sz H). apply N.add_le_mono_r, size_mono.
    apply N.div_le_mono; lia.
Qed.

(* Moving the right pointer: the interval shrinks to (sz-1)/2, and log2(sz+1) drops by exactly 1. *)
Lemma log2_go_left : forall sz, 1 <= sz -> N.log2 ((sz - 1) / 2 + 1) + 1 = N.log2 (sz + 1).
Proof.
    intros. rewrite <- (log2_half (sz + 1)) by lia. f_equal. f_equal.
    replace (sz + 1) with ((sz - 1) + 1 * 2) by lia. rewrite N.div_add by lia. reflexivity.
Qed.

Lemma log2_go_right : forall sz, 1 <= sz ->
    N.log2 (sz + 1) <= N.log2 (sz - 1 - (sz - 1) / 2 + 1) + 1.
Proof.
    intros. rewrite <- (log2_go_left sz H). apply N.add_le_mono_r, N.log2_le_mono.
    pose proof (N.div_le_upper_bound (sz - 1) 2 (sz - 1 - (sz - 1) / 2)).
    pose proof (N.mul_div_le (sz - 1) 2). lia.
Qed.

(* Tightness of the iteration-count bounds *)

Fixpoint iterate (f : N -> N) (n : nat) (x : N) : N :=
    match n with O => x | S n' => iterate f n' (f x) end.

(* Always moving left (key above every element) takes exactly N.size len iterations. *)
Lemma always_left_iterations : forall n x, N.size x = N.of_nat n ->
    iterate (fun sz => sz / 2) n x = 0 /\
    (forall j, (j < n)%nat -> iterate (fun sz => sz / 2) j x <> 0).
Proof.
    induction n; intros x SZ.
    - destruct x; [|destruct p; discriminate]. split. reflexivity. intros. lia.
    - assert (X: x <> 0) by (intro; subst; simpl in *; lia).
      assert (SZ': N.size (x / 2) = N.of_nat n) by (pose proof (size_half x); lia).
      destruct (IHn (x / 2) SZ') as [Z NZ]. split. exact Z.
      intros [|j] J; simpl. exact X. apply NZ. lia.
Qed.

(* Always moving right (key below every element) takes exactly N.log2 (len+1) iterations. *)
Lemma always_right_iterations : forall n x, N.log2 (x + 1) = N.of_nat n ->
    iterate (fun sz => (sz - 1) / 2) n x = 0 /\
    (forall j, (j < n)%nat -> iterate (fun sz => (sz - 1) / 2) j x <> 0).
Proof.
    induction n; intros x L.
    - assert (x = 0). { destruct (N.eqb_spec x 0). assumption.
        pose proof (N.log2_le_mono 2 (x + 1) ltac:(lia)). simpl in *. lia. }
      subst. split. reflexivity. intros. lia.
    - assert (X: x <> 0) by (intro; subst; simpl in *; lia).
      assert (L': N.log2 ((x - 1) / 2 + 1) = N.of_nat n) by (pose proof (log2_go_left x); lia).
      destruct (IHn _ L') as [Z NZ]. split. exact Z.
      intros [|j] J; simpl. exact X. apply NZ. lia.
Qed.

(* Timing proof *)

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_binary_search <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1f8 => true
        | _ => false
    end | _ => false end.

    Definition binary := binary_search.
End Program_binary_search.

Module RISCVTiming := RISCVTiming cpu Program_binary_search.
Module binary_searchAuto := RISCVTimingAutomation RISCVTiming.
Import Program_binary_search binary_searchAuto.

(* a3 := arr; right := len - 1; left := 0 *)
Definition setup_time : N := taddi + taddi + taddi.

(* One iteration that does not find the key *)
Definition body_time : N :=
    ttbge + tsub + tsrai 1 + tadd + tslli 2 + tadd + tlw + taddi + tfbeq +
    (* branchless left/right update *)
    tsltu + tsltu +
    taddi + tsub + tand + tandn + tor +
    taddi + tsub + tand + tandn + tor +
    tjal.

(* Final iteration in which arr[mid] = key *)
Definition found_exit_time : N :=
    ttbge + tsub + tsrai 1 + tadd + tslli 2 + tadd + tlw + taddi + ttbeq + tjalr.

(* Loop guard fails: return -1 *)
Definition notfound_exit_time : N := tfbge + taddi + tjalr.

Definition time_of_binary_search (found : bool) (k : N) (t : trace) : Prop :=
    cycle_count_of_trace t =
        setup_time + k * body_time +
        if found then found_exit_time else notfound_exit_time.

Definition postcondition (base_mem : memory) (arr key len : N) (s : store) (t : trace) :=
    exists k,
    (s R_A0 < len /\ base_mem Ⓓ[arr + (s R_A0 << 2)] = key /\
        k < N.size len /\ time_of_binary_search true k t) \/
    (s R_A0 = 2^32 - 1 /\
        N.log2 (len + 1) <= k <= N.size len /\ time_of_binary_search false k t).

Definition binary_search_timing_invs (base_mem : memory) (arr key len : N)
        (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ s R_A0 = arr /\ s R_A1 = len /\
            s R_A2 = key /\ cycle_count_of_trace t' = 0)
(* loop head: left = l, right = l + sz - 1, after k non-matching iterations *)
| 0x1f0 => Some (exists k l sz,
    s V_MEM32 = base_mem /\ s R_A3 = arr /\ s R_A2 = key /\
    s R_A5 = l /\ s R_A1 = l + sz ⊖ 1 /\
    l + sz <= len /\ len < 2^31 /\
    k + N.size sz <= N.size len /\
    N.log2 (len + 1) <= k + N.log2 (sz + 1) /\
    cycle_count_of_trace t' = setup_time + k * body_time)
| 0x1f8 => Some (postcondition base_mem arr key len s t)
| _ => None end | _ => None end.

Theorem binary_search_timing:
  forall s (t : trace) s' x' base_mem arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = arr)
         (A1: s R_A1 = len)
         (A2: s R_A2 = key)
         (* indices are C ints *)
         (LEN: len < 2^31),
  satisfies_all
    lifted_prog
    (binary_search_timing_invs base_mem arr key len)
    exits
  ((x',s')::t).
Proof using.
    intros. apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL LEN. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x1e4 -> loop head *)
    destruct PRE as (Mem & A0 & A1 & A2 & Cycles).
    repeat step.
    exists 0, 0, len. repeat split; auto; try lia.
    unfold setup_time. hammer.

    (* loop head *)
    destruct PRE as (k & l & sz & Mem & A3 & A2 & A5 & A1 & LSZ & _ &
        SIZE & LOG & Cycles).
    step; rewrite loop_guard in BC by lia;
        rewrite loop_guard_time in Cycles by lia.

    (* left > right: return -1 *)
    - apply N.eqb_eq in BC. subst sz. rewrite N.add_0_r in *.
    repeat step.
    unfold postcondition. exists k. right.
    replace (N.log2 (0 + 1)) with 0 in LOG by reflexivity.
    replace (N.size 0) with 0 in SIZE by reflexivity.
      repeat split; try lia.
      unfold time_of_binary_search, notfound_exit_time. hammer. simpl. lia.

    (* left <= right: probe arr[mid] *)
    - apply N.eqb_neq in BC.
      replace (negb (sz =? 0)) with true in Cycles
        by (symmetry; apply negb_true_iff, N.eqb_neq, BC).
      repeat step; rewrite half_width in * by lia; set (h := (sz - 1) / 2) in *;
        assert (HH: 2 * h <= sz - 1) by (unfold h; apply N.mul_div_le; lia);
        rewrite (N.mod_small (h + l)) by lia.

      (* arr[mid] = key: return mid *)
      + unfold postcondition. exists k. left.
        pose proof (size_mono 1 sz ltac:(lia)). simpl (N.size 1) in *.
        repeat split; try lia. (* lia also discharges arr[mid] = key from BC0 *)
        unfold time_of_binary_search, found_exit_time. hammer.

      (* arr[mid] <> key: branchless pointer update, back to the loop head *)
      + set (M := base_mem Ⓓ[ arr + (h + l << 2) ]) in *.
        destruct (M <? key) eqn:LT.
        (* arr[mid] < key: left := mid + 1, interval shrinks to sz/2 *)
        * replace (key <? M) with false
            by (apply N.ltb_lt in LT; symmetry; apply N.ltb_ge; lia).
          pose proof (size_go_right sz ltac:(lia)) as G1.
          pose proof (log2_go_right sz ltac:(lia)) as G2. fold h in G1, G2.
          exists (1 + k), (1 + h + l), (sz - 1 - h).
          repeat split; auto; try lia.
            replace (1 + h + l + (sz - 1 - h)) with (l + sz) by lia. reflexivity.
          rewrite N.mul_add_distr_r, N.mul_1_l. remember (k * body_time) as KB.
          unfold body_time. hammer.
        (* key < arr[mid]: right := mid - 1, interval shrinks to (sz-1)/2 *)
        * replace (key <? M) with true
            by (apply N.ltb_ge in LT; apply N.eqb_neq in BC0; symmetry; apply N.ltb_lt; lia).
          pose proof (size_go_left sz ltac:(lia)) as G1.
          pose proof (log2_go_left sz ltac:(lia)) as G2. fold h in G1, G2.
          exists (1 + k), l, h.
          repeat split; auto; try lia.
            apply decr_mod.
          rewrite N.mul_add_distr_r, N.mul_1_l. remember (k * body_time) as KB.
          unfold body_time. hammer.
Qed.

(* Closed-form lower and upper bounds *)

(* Lower bound: key at the first midpoint (found, k = 0), or for a non-empty
   array not containing the key, the shortest miss path (k = log2 (len+1)). *)
Definition lower_bound (len : N) : N :=
    setup_time +
    if len =? 0 then notfound_exit_time
    else N.min found_exit_time
               (N.log2 (len + 1) * body_time + notfound_exit_time).

(* Upper bound: found on the deepest probe (k = size len - 1), or a miss on
   the longest path (k = size len = floor(log2 len) + 1). *)
Definition upper_bound (len : N) : N :=
    setup_time +
    if len =? 0 then notfound_exit_time
    else N.max ((N.size len - 1) * body_time + found_exit_time)
               (N.size len * body_time + notfound_exit_time).

Theorem binary_search_bounds :
    forall base_mem arr key len s t,
    postcondition base_mem arr key len s t ->
    lower_bound len <= cycle_count_of_trace t <= upper_bound len.
Proof.
    intros. unfold postcondition, time_of_binary_search, lower_bound, upper_bound in *.
    destruct H as (k & [(_ & _ & K & T) | (_ & K & T)]); rewrite T; clear T.
    - (* found *)
      assert (len <> 0) by (intro; subst; simpl in K; lia).
      replace (len =? 0) with false by (symmetry; apply N.eqb_neq; assumption).
      pose proof (N.mul_le_mono_r k (N.size len - 1) body_time ltac:(lia)).
      split; lia.
    - (* not found *)
      destruct (N.eqb_spec len 0).
      + subst. simpl in K. replace k with 0 by lia. lia.
      + pose proof (N.mul_le_mono_r _ _ body_time (proj1 K)).
        pose proof (N.mul_le_mono_r _ _ body_time (proj2 K)).
        split; lia.
Qed.

End TimingProof.

(* Instantiation for NEORV32 *)

Require Import NEORV32.
Module NRV32 := NEORV32 NEORV32BaseConfig.
Module NEORV32TimingProof := TimingProof NRV32.
Import NEORV32TimingProof NRV32.

Goal setup_time = 6 /\ body_time = 62 + 2 * T_inst_latency + T_data_latency /\
     found_exit_time = 36 + 3 * T_inst_latency + T_data_latency /\
     notfound_exit_time = 10 + T_inst_latency.
Proof. unfold setup_time, body_time, found_exit_time, notfound_exit_time. unfold taddi, tsub, tsrai, tadd, tslli, tlw, tfbeq, tsltu, tand, tandn, tor, tjal, ttbge, ttbeq, tjalr, tfbge, T_shift_latency; simpl. lia. Qed.

(* On NEORV32 the minimum is always "found at the first midpoint" and the
   maximum is always "miss after floor(log2 len) + 1 probes". *)
Goal forall len, len <> 0 ->
    lower_bound len = 42 + 3 * T_inst_latency + T_data_latency /\
    upper_bound len = 16 + T_inst_latency +
        (N.log2 len + 1) * (62 + 2 * T_inst_latency + T_data_latency).
Proof.
    intros len L. unfold lower_bound, upper_bound.
    replace (len =? 0) with false by (symmetry; apply N.eqb_neq; assumption).
    rewrite N.size_log2 by assumption.
    assert (1 <= N.log2 (len + 1)) by
        (pose proof (N.log2_le_mono 2 (len + 1) ltac:(lia)); simpl in *; lia).
    unfold setup_time, body_time, found_exit_time, notfound_exit_time.
    unfold taddi, tsub, tsrai, tadd, tslli, tlw, tfbeq, tsltu, tand, tandn, tor, tjal, ttbge, ttbeq, tjalr, tfbge, T_shift_latency; simpl.
    set (B := 62 + 2 * T_inst_latency + T_data_latency).
    split; nia.
Qed.

Print Assumptions NEORV32TimingProof.binary_search_timing.
