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
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_apply_frame: unavailable; statement aborted. *)
Theorem si_apply_typed : forall writes m,
  m < memsize 32 -> si_apply m writes < memsize 32.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_apply_typed: unavailable; statement aborted. *)
Theorem si_memory_frame : forall s0 L new xs,
  si_frame (s0 V_MEM32) (si_memory s0 L new xs) (si_all_writes s0 L new xs).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_memory_frame: unavailable; statement aborted. *)

Theorem si_split_partition : forall xs value,
  xs=fst (si_split value xs) ++ snd (si_split value xs).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_split_partition: unavailable; statement aborted. *)
Theorem si_cut_partition : forall xs value,
  xs=si_before value xs ++ si_after value xs.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_cut_partition: unavailable; statement aborted. *)
Theorem si_result_length : forall new xs,
  length (si_result new xs)=S (length xs).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_result_length: unavailable; statement aborted. *)
Theorem si_result_membership : forall new xs a,
  In a (si_result new xs) <-> a=new \/ In a xs.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_result_membership: unavailable; statement aborted. *)
Theorem si_max_cut : forall xs,
  si_before list_max_value xs=xs /\ si_after list_max_value xs=[].
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_max_cut: unavailable; statement aborted. *)

Theorem si_split_bounds : forall xs value,
  si_sorted xs ->
  Forall (fun a => si_value a <= value) (fst (si_split value xs)) /\
  Forall (fun a => value < si_value a) (snd (si_split value xs)).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_split_bounds: unavailable; statement aborted. *)

Theorem si_result_sorted : forall new xs,
  si_sorted xs -> si_value new < 2^32 ->
  Forall (fun a => si_value a < 2^32) xs -> si_sorted (si_result new xs).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_result_sorted: unavailable; statement aborted. *)

(* The abstract memory splice is proved separately from machine stepping. *)
Theorem si_memory_refinement : forall s0 L new index xs,
  si_pre s0 L new index xs ->
  si_memory_post s0 L new index xs (update s0 V_MEM32 (si_memory s0 L new xs)).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions si_memory_refinement: unavailable; statement aborted. *)

Theorem sorted_insert_correct : forall s0 t s' x' L new index xs,
  startof t (x',s')=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  satisfies_all vListInsert_armv6m_prog (si_invs s0 L new index xs)
    si_exit ((x',s')::t).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions sorted_insert_correct: unavailable; statement aborted. *)

Theorem sorted_insert_at_pop : forall s0 t s L new index xs,
  startof t (Addr 0x9a,s)=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  exec_prog vListInsert_armv6m_prog ((Addr 0x9a,s)::t) ->
  unterminated si_exit t -> si_at_pop s0 L new index xs s.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions sorted_insert_at_pop: unavailable; statement aborted. *)

Theorem sorted_insert_return_step : forall s0 s L new index xs,
  models armv6mtypctx s0 -> si_pre s0 L new index xs -> si_at_pop s0 L new index xs s ->
  exists sr, can_step vListInsert_armv6m_prog
    ((Addr (N.land (s0 R_LR) 0xfffffffe),sr),(Addr 0x9a,s)) /\
    si_returned s0 L new index xs sr.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions sorted_insert_return_step: unavailable; statement aborted. *)
Theorem sorted_insert_trace_returns : forall s0 t s L new index xs,
  startof t (Addr 0x9a,s)=(Addr 0x72,s0) -> models armv6mtypctx s0 ->
  si_pre s0 L new index xs ->
  exec_prog vListInsert_armv6m_prog ((Addr 0x9a,s)::t) ->
  unterminated si_exit t -> exists sr,
    si_returned s0 L new index xs sr /\
    exec_prog vListInsert_armv6m_prog
      ((Addr (N.land (s0 R_LR) 0xfffffffe),sr)::(Addr 0x9a,s)::t).
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions sorted_insert_trace_returns: unavailable; statement aborted. *)

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
Theorem sorted_insert_nonvacuity : forall xs,
  xs=[] \/ xs=[si_one] \/ xs=[si_one;si_two] ->
  exists s, models armv6mtypctx s /\ si_pre s 4096 si_new 4104 xs.
Proof.
  (* Unchecked one-shot attempt preserved in notes/r05-list-insert/initial-attempt.v.txt. *)
Abort.
(* Print Assumptions sorted_insert_nonvacuity: unavailable; statement aborted. *)
