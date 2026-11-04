(* prvSearchForNameWithinSingleList: proposed sequential IL contract.
   Initial author: OpenAI gpt-6-astra, xhigh, default tier, r27-find-task.
   Final proof producer: not certified; Sol repair remains PARTIAL.
   See notes/r27-find-task-fix/README.md. No full unit vo or assumptions audit.

   PROVENANCE: FreeRTOS V11.1.0, dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   ELF SHA256 5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   The unchanged generated finite program is the accepted e05 call-free body.
   tasks.c SHA256 6a54883765441f12b45b7f2e36838727e8e0aa872054df30c814c473ee3e4149.
   Layout evidence: Examples/freertos/cortex-m0/evidence/layout.json;
   configMAX_TASK_NAME_LEN=16, configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES=0.
   List count/head/sentinel offsets 0/12/8; item next/owner offsets 4/12;
   TCB size 84, task-name offset 52. No globals, literals, calls or tunables.

   SPECIFICATION: AAPCS32 R0=list, R1=query. A finite sentinel-terminated
   next-link chain describes traversal order, and the count equals its length.
   Return the owner of the FIRST item whose task name and query have equal
   bytes through a common NUL at an index strictly below 16; otherwise NULL.
   In particular 16 equal nonzero bytes do NOT match. Owners are nonnull TCB
   objects. No precondition requires a matching name or a NUL in either input.
   Count/list/TCB consistency is a local representation hypothesis, not a
   scheduler-cardinality theorem. No task creation or whole-kernel assumption.

   All pointers are 32-bit. List/item/TCB objects are aligned, nonnull and
   nonwrapping; query has 16 nonwrapping bytes. SP is 8-byte aligned, >=20,
   and <2^32. The 20 bytes below SP are disjoint from the list, every item,
   every TCB, and query; other input overlaps are allowed if their field
   predicates coexist. Required bytes are readable, stack bytes writable.
   LR is odd and below 0xfffffff0 (ordinary Thumb, excludes EXC_RETURN).

   Entry 0x5d0; after PUSH 0x5d2; outer head 0x5f0; inner head 0x5f8;
   advance 0x5ea; successful comparison 0x5e6; exit cut BEFORE POP 0x60e.
   The actual return is POP {r4,r5,r6,r7,pc}, using armv6m_bxwritepc; there
   is no standalone BX LR in this body. The separate return obligation steps
   that actual instruction, restores R4-R11/SP and preserves LR. Memory is
   exactly original memory with saved R4,R5,R6,R7,LR in the five stack words;
   bytes outside that area equal ORIGINAL bytes. POP does not erase them.

   The pure list/name definitions below are specifications only. The program
   in every execution theorem is the generated finite IL, not a replacement.
   No callee oracle, CPU IRQ/hardware refinement, concurrency, termination,
   or stronger binary-soundness claim than the inherited lift provenance.
 *)
Require Import Picinae_armv6m armv6m_list_model.
Require Import prvSearchForNameWithinSingleList_armv6m.
From Stdlib Require Import NArith Arith Lia List Bool FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Definition search_task_byte (m owner:N) (j:nat) :=
  getmem 32 LittleE 1 m (owner + 52 + N.of_nat j).
Definition search_query_byte (m query:N) (j:nat) :=
  getmem 32 LittleE 1 m (query + N.of_nat j).
Definition search_name_match (m query owner:N) :=
  exists k:nat, (k < 16)%nat /\ search_task_byte m owner k = 0 /\
    forall j:nat, (j <= k)%nat ->
      search_task_byte m owner j = search_query_byte m query j.
Definition search_name_matchb (m query owner:N) :=
  existsb (fun k => (search_task_byte m owner k =? 0) &&
    forallb (fun j => search_task_byte m owner j =? search_query_byte m query j)
      (seq 0 (S k))) (seq 0 16).
Definition search_prefix (m query owner:N) (k:nat) :=
  forall j:nat, (j < k)%nat ->
    search_task_byte m owner j = search_query_byte m query j /\
    search_task_byte m owner j <> 0.

Definition search_nodes := list (N*N).
Fixpoint search_result (m query:N) (nodes:search_nodes) : N :=
  match nodes with
  | [] => 0
  | (_,owner)::tail => if search_name_matchb m query owner then owner
                      else search_result m query tail
  end.
Fixpoint search_chain (m sentinel head:N) (nodes:search_nodes) : Prop :=
  match nodes with
  | [] => head = sentinel
  | (item,owner)::tail =>
      head = item /\ item <> sentinel /\ object32 item 20 /\
      object32 owner 84 /\ field32 m item 12 = owner /\
      search_chain m sentinel (field32 m item 4) tail
  end.
Definition search_layout (m listptr:N) (nodes:search_nodes) :=
  object32 listptr 20 /\
  field32 m listptr 0 = N.of_nat (length nodes) /\
  search_chain m (listptr+8) (field32 m listptr 12) nodes.
Definition search_disjoint (listptr query sp:N) (nodes:search_nodes) :=
  separate32 listptr 20 (sp-20) 20 /\
  separate32 query 16 (sp-20) 20 /\
  Forall (fun io => separate32 (fst io) 20 (sp-20) 20 /\
                   separate32 (snd io) 84 (sp-20) 20) nodes.
Definition search_read_range (s:store) (p n:N) :=
  forall j, j < n -> mem_readable s ((p+j) mod 2^32).
Definition search_write_range (s:store) (p n:N) :=
  forall j, j < n -> mem_writable s ((p+j) mod 2^32).
Definition search_permissions (s:store) (nodes:search_nodes) :=
  search_read_range s (s R_R0) 20 /\
  search_read_range s (s R_R1) 16 /\
  search_read_range s (s R_SP-20) 20 /\
  search_write_range s (s R_SP-20) 20 /\
  Forall (fun io => search_read_range s (fst io) 20 /\
                   search_read_range s (snd io) 84) nodes.
Definition search_precondition (s:store) (nodes:search_nodes) :=
  models armv6mtypctx s /\ search_layout (s V_MEM32) (s R_R0) nodes /\
  range32 (s R_R1) 16 /\ 20 <= s R_SP /\ s R_SP < 2^32 /\
  s R_SP mod 8 = 0 /\
  search_disjoint (s R_R0) (s R_R1) (s R_SP) nodes /\
  search_permissions s nodes /\
  N.odd (s R_LR) = true /\ s R_LR < 0xfffffff0.

Definition search_stack_image (s:store) :=
  image20 (s V_MEM32) (s R_SP-20) (s R_R4) (s R_R5) (s R_R6) (s R_R7) (s R_LR).
Definition search_fixed_registers :=
  [R_R1;R_R8;R_R9;R_R10;R_R11;R_R12;R_LR;A_READ;A_WRITE;A_EXEC].
Definition search_fixed_frame (initial current:store) :=
  forall v, In v search_fixed_registers -> current v = initial v.
Definition search_running (initial current:store) :=
  current V_MEM32 = search_stack_image initial /\
  current R_SP = initial R_SP-20 /\ search_fixed_frame initial current.
Definition search_pop_post (initial current:store) (nodes:search_nodes) :=
  search_running initial current /\
  current R_R0 = search_result (initial V_MEM32) (initial R_R1) nodes.
Definition search_postcondition (initial final:store) (nodes:search_nodes) :=
  final R_R0 = search_result (initial V_MEM32) (initial R_R1) nodes /\
  final V_MEM32 = search_stack_image initial /\
  outside_frame32 (initial V_MEM32) (final V_MEM32) (initial R_SP-20) 20 /\
  (forall v, In v [R_R4;R_R5;R_R6;R_R7;R_R8;R_R9;R_R10;R_R11;R_SP;R_LR] ->
     final v = initial v) /\ search_fixed_frame initial final.

Definition search_position (initial current:store) (nodes:search_nodes)
    (item owner:N) (tail:search_nodes) :=
  exists before, nodes = before ++ (item,owner)::tail /\
    Forall (fun io => search_name_matchb (initial V_MEM32) (initial R_R1) (snd io) = false) before /\
    current R_R6 = item /\ current R_R7 = initial R_R0+8.
Definition search_outer (initial current:store) (nodes:search_nodes) :=
  search_running initial current /\
  exists item owner tail, search_position initial current nodes item owner tail.
Definition search_inner (initial current:store) (nodes:search_nodes) :=
  search_running initial current /\
  exists item owner tail k,
    search_position initial current nodes item owner tail /\ (k<16)%nat /\
    current R_R0 = owner /\ current R_R5 = owner+52 /\
    current R_R3 = N.of_nat k /\ search_prefix (initial V_MEM32) (initial R_R1) owner k.
Definition search_advance (initial current:store) (nodes:search_nodes) :=
  search_running initial current /\
  exists item owner tail, search_position initial current nodes item owner tail /\
    search_name_matchb (initial V_MEM32) (initial R_R1) owner = false.
Definition search_found (initial current:store) (nodes:search_nodes) :=
  search_running initial current /\
  exists item owner tail, search_position initial current nodes item owner tail /\
    current R_R0 = owner /\
    search_name_matchb (initial V_MEM32) (initial R_R1) owner = true.
Definition search_exit (t:trace) : bool :=
  match t with (Addr 0x60e,_)::_ => true | _ => false end.
Definition search_invariants (initial:store) (nodes:search_nodes) (t:trace) : option Prop :=
  match t with
  | (Addr 0x5d0,s)::_ => Some (s=initial)
  | (Addr 0x5d2,s)::_ => Some (search_running initial s /\ s R_R0=initial R_R0)
  | (Addr 0x5f0,s)::_ => Some (search_outer initial s nodes)
  | (Addr 0x5f8,s)::_ => Some (search_inner initial s nodes)
  | (Addr 0x5ea,s)::_ => Some (search_advance initial s nodes)
  | (Addr 0x5e6,s)::_ => Some (search_found initial s nodes)
  | (Addr 0x60e,s)::_ => Some (search_pop_post initial s nodes)
  | _ => None
  end.

(* The concrete witness permits arbitrary typed memories and argument values.
   It does not assume correctness, successful execution or any helper contract. *)
Definition search_entry_witness (m listptr query sp lr:N) : store := fun v =>
  match v with
  | V_MEM32 => m | R_R0 => listptr | R_R1 => query | R_SP => sp | R_LR => lr
  | A_READ | A_WRITE | A_EXEC => N.ones (2^32)
  | _ => 0
  end.

Theorem search_nwc : forall s2 s1,
  prvSearchForNameWithinSingleList_armv6m_prog s1 =
  prvSearchForNameWithinSingleList_armv6m_prog s2.
Proof. reflexivity. Qed.
Theorem search_welltyped :
  welltyped_prog armv6mtypctx prvSearchForNameWithinSingleList_armv6m_prog.
Proof. exact prvSearchForNameWithinSingleList_armv6m_welltyped. Qed.
Theorem search_saved_bytes_frame : forall s,
  outside_frame32 (s V_MEM32) (search_stack_image s) (s R_SP-20) 20.
Proof. intro s. apply image20_frame. Qed.

Lemma search_matchb_spec : forall m q o,
  search_name_matchb m q o = true <-> search_name_match m q o.
Proof.
  intros m q o. unfold search_name_matchb, search_name_match.
  rewrite existsb_exists. split.
  - intros [k [IN B]]. apply in_seq in IN.
    apply andb_true_iff in B. destruct B as [ZERO EQ].
    apply N.eqb_eq in ZERO. exists k. split; [exact (proj2 IN)|]. split; [exact ZERO|].
    intros j LE. apply forallb_forall with (x:=j) in EQ.
    + apply N.eqb_eq. exact EQ.
    + apply in_seq. clear - LE. lia.
  - intros [k [LT [ZERO EQ]]]. exists k. split.
    + apply in_seq. clear - LT. lia.
    + apply andb_true_iff. split; [apply N.eqb_eq; exact ZERO|].
      apply forallb_forall. intros j IN. apply in_seq in IN.
      apply N.eqb_eq. apply EQ. clear - IN. lia.
Qed.

Lemma search_match_at_zero : forall m q o k,
  (k<16)%nat -> search_prefix m q o k ->
  search_task_byte m o k = 0 -> search_query_byte m q k = 0 ->
  search_name_matchb m q o = true.
Proof.
  intros m q o k LT PRE T Q. apply search_matchb_spec.
  exists k. split; [exact LT|]. split; [exact T|].
  intros j LE. destruct (Nat.eq_dec j k) as [->|NE].
  - rewrite T, Q. reflexivity.
  - apply (proj1 (PRE j ltac:(clear - LE NE; lia))).
Qed.

Lemma search_mismatch : forall m q o k,
  search_prefix m q o k ->
  search_task_byte m o k <> search_query_byte m q k ->
  search_name_matchb m q o = false.
Proof.
  intros m q o k PRE NE. destruct (search_name_matchb m q o) eqn:B; [|reflexivity].
  apply search_matchb_spec in B. destruct B as [j [LT [ZERO EQ]]].
  destruct (Nat.lt_ge_cases j k) as [JK|KJ].
  - exfalso. exact (proj2 (PRE j JK) ZERO).
  - exfalso. apply NE. apply EQ. exact KJ.
Qed.

Lemma search_exhausted : forall m q o,
  search_prefix m q o 16 -> search_name_matchb m q o = false.
Proof.
  intros m q o PRE. destruct (search_name_matchb m q o) eqn:B; [|reflexivity].
  apply search_matchb_spec in B. destruct B as [j [LT [ZERO EQ]]].
  exfalso. exact (proj2 (PRE j LT) ZERO).
Qed.

Lemma search_skip_prefix : forall m q before tail,
  Forall (fun io => search_name_matchb m q (snd io)=false) before ->
  search_result m q (before++tail) = search_result m q tail.
Proof.
  intros m q before tail F. induction F as [|[i o] before B F IH].
  - reflexivity.
  - cbn [app search_result]. change (search_name_matchb m q o = false) in B. rewrite B. exact IH.
Qed.

Theorem search_result_first_match : forall m q nodes,
  (Forall (fun io => search_name_matchb m q (snd io)=false) nodes /\
   search_result m q nodes=0) \/
  exists before item owner after,
    nodes=before++(item,owner)::after /\
    Forall (fun io => search_name_matchb m q (snd io)=false) before /\
    search_name_match m q owner /\ search_result m q nodes=owner.
Proof.
  intros m q nodes. induction nodes as [|[i o] tail IH].
  - left. split; [constructor|reflexivity].
  - destruct (search_name_matchb m q o) eqn:B.
    + right. exists [], i, o, tail. split; [reflexivity|].
      split; [constructor|]. split; [apply search_matchb_spec; exact B|].
      cbn [search_result]. rewrite B. reflexivity.
    + destruct IH as [[F Z]|[before [item [owner [after [E [F [MATCH RES]]]]]]]].
      * left. split; [constructor; assumption|]. cbn [search_result]. rewrite B. exact Z.
      * right. exists ((i,o)::before), item, owner, after.
        split; [cbn; rewrite E; reflexivity|].
        split; [constructor; assumption|]. split; [exact MATCH|].
        cbn [search_result]. rewrite B. exact RES.
Qed.

Lemma search_zero_bound : forall w, 0 < 2^w.
Proof. intro w. apply N.neq_0_lt_0, pow2_nonzero. Qed.
Theorem search_witness_models : forall m l q sp lr,
  m < 2^(8*2^32) -> l<2^32 -> q<2^32 -> sp<2^32 -> lr<2^32 ->
  models armv6mtypctx (search_entry_witness m l q sp lr).
Proof.
  intros m l q sp lr M L Q SP LR v w T.
  destruct v; cbn [armv6mtypctx] in T; try discriminate; injection T as <-.
  all: lazymatch goal with
  | |- search_entry_witness _ _ _ _ _ V_MEM32 < _ => exact M
  | |- search_entry_witness _ _ _ _ _ R_R0 < _ => exact L
  | |- search_entry_witness _ _ _ _ _ R_R1 < _ => exact Q
  | |- search_entry_witness _ _ _ _ _ R_SP < _ => exact SP
  | |- search_entry_witness _ _ _ _ _ R_LR < _ => exact LR
  | |- search_entry_witness _ _ _ _ _ A_READ < _ => exact (ones_bound (2^32))
  | |- search_entry_witness _ _ _ _ _ A_WRITE < _ => exact (ones_bound (2^32))
  | |- search_entry_witness _ _ _ _ _ A_EXEC < _ => exact (ones_bound (2^32))
  | |- _ < 2^?width => exact (search_zero_bound width)
  end.
Qed.
Theorem search_witness_permissions : forall m l q sp lr nodes,
  search_permissions (search_entry_witness m l q sp lr) nodes.
Proof.
  intros. unfold search_permissions, search_read_range, search_write_range.
  repeat split; try (intros; apply N.ones_spec_low; apply N.mod_lt, pow2_nonzero).
  apply Forall_forall. intros [i o] IN. split; intros j LT;
    apply N.ones_spec_low; apply N.mod_lt, pow2_nonzero.
Qed.
Theorem search_entry_satisfiable : forall m l q sp lr nodes,
  m<2^(8*2^32) -> search_layout m l nodes -> range32 q 16 ->
  20<=sp -> sp<2^32 -> sp mod 8=0 -> search_disjoint l q sp nodes ->
  N.odd lr=true -> lr<0xfffffff0 ->
  exists s, search_precondition s nodes /\ s V_MEM32=m /\ s R_R0=l /\
    s R_R1=q /\ s R_SP=sp /\ s R_LR=lr.
Proof.
  intros m l q sp lr nodes M L Q S SP AL SEP ODD LR.
  exists (search_entry_witness m l q sp lr).
  assert (LB: l<2^32) by exact (proj1 (proj2 (proj2 (proj1 L)))).
  assert (QB: q<2^32) by exact (proj1 Q).
  assert (LRB: lr<2^32) by (clear - LR; lia).
  split.
  - unfold search_precondition. split.
    + apply search_witness_models; assumption.
    + split; [exact L|]. split; [exact Q|]. split; [exact S|].
      split; [exact SP|]. split; [exact AL|]. split; [exact SEP|].
      split; [apply search_witness_permissions|]. split; assumption.
  - repeat split; reflexivity.
Qed.

Theorem search_empty_layout : forall m p,
  object32 p 20 -> search_layout (empty_image m p) p [].
Proof.
  intros m p OBJ.
  pose proof (empty_image_spec m p OBJ) as E.
  destruct E as [_ [[COUNT [INDEX VALUE]] [NEXT PREVIOUS]]].
  split; [exact OBJ|]. split; [exact COUNT|exact NEXT].
Qed.

(* Full-precondition nonvacuity for arbitrary typed background memory: the
   empty list at 256, query at 512, stack ending at 1024, ordinary LR=1. *)
Theorem search_empty_entry_satisfiable : forall m,
  m < 2^(8*2^32) -> exists s, search_precondition s [].
Proof.
  intros m MB.
  assert (OBJ: object32 256 20) by (repeat split; try reflexivity; discriminate).
  assert (LAY: search_layout (empty_image m 256) 256 [])
    by (apply search_empty_layout; exact OBJ).
  assert (TYP: empty_image m 256 < 2^(8*2^32)).
  { apply image20_welltyped. exact MB. }
  assert (SEP: search_disjoint 256 512 1024 []).
  { split.
    - apply ranges32_separate; unfold range32; vm_compute; intuition discriminate.
    - split.
      + apply ranges32_separate; unfold range32; vm_compute; intuition discriminate.
      + constructor. }
  destruct (search_entry_satisfiable (empty_image m 256) 256 512 1024 1 []
    TYP LAY ltac:(split; try reflexivity; discriminate) ltac:(discriminate) ltac:(reflexivity)
    eq_refl SEP eq_refl ltac:(reflexivity)) as [s [PRE _]].
  exists s. exact PRE.
Qed.

(* The execution attempt deliberately uses cuts to avoid unrolling the list or
   the byte loop. Original-memory loads need the stack/input separation facts. *)
Theorem search_correct : forall initial nodes t s' x'
  (PRE: search_precondition initial nodes)
  (ENTRY: startof t (x',s') = (Addr 0x5d0,initial)),
  satisfies_all prvSearchForNameWithinSingleList_armv6m_prog
    (search_invariants initial nodes) search_exit ((x',s')::t).
Proof.
  (* WIP: exact unverified attempt retained in unit notes. *)
Abort.

Corollary search_post_at_pop : forall initial nodes t s'
  (PRE: search_precondition initial nodes)
  (ENTRY: startof t (Addr 0x60e,s') = (Addr 0x5d0,initial))
  (EXEC: exec_prog prvSearchForNameWithinSingleList_armv6m_prog ((Addr 0x60e,s')::t))
  (UT: unterminated search_exit t), search_pop_post initial s' nodes.
Proof.
  (* WIP: exact unverified attempt retained in unit notes. *)
Abort.

(* This statement requires the actual return instruction to take an ordinary
   Thumb step; its premise is the proved loop postcondition, not a callee oracle. *)
Theorem search_return_step : forall initial current nodes,
  search_precondition initial nodes -> search_pop_post initial current nodes ->
  exists final,
    can_step prvSearchForNameWithinSingleList_armv6m_prog
      ((Addr (N.land (initial R_LR) (N.ones 32-1)),final),(Addr 0x60e,current)) /\
    search_postcondition initial final nodes.
Proof.
  (* WIP: exact unverified attempt retained in unit notes. *)
Abort.

Corollary search_caller_result : forall initial nodes t s'
  (PRE: search_precondition initial nodes)
  (ENTRY: startof t (Addr 0x60e,s') = (Addr 0x5d0,initial))
  (EXEC: exec_prog prvSearchForNameWithinSingleList_armv6m_prog ((Addr 0x60e,s')::t))
  (UT: unterminated search_exit t),
  exists final,
    can_step prvSearchForNameWithinSingleList_armv6m_prog
      ((Addr (N.land (initial R_LR) (N.ones 32-1)),final),(Addr 0x60e,s')) /\
    search_postcondition initial final nodes.
Proof.
  (* WIP: exact unverified attempt retained in unit notes. *)
Abort.
