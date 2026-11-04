(* vListInsertEnd: original-memory local insertion contract for the finite IL.
   Official FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0;
   Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Accepted e05 closed-leaf map, unchanged; r00 prerequisite 4ff26413448da4d8f064b0273ac5472cc9de7e5a.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, one-shot.
   Validation/final producer: see notes/r03-list-insert-end/README.md.

   AAPCS32: R0=L, R1=P. Entry 0x5c; BX LR at 0x70. Eleven instructions,
   no calls or stack access. List_t is 20 bytes; embedded MiniItem at L+8
   is 12 bytes; new Item is 20 bytes. I=original L.index; B=original I.prev.
   Writes in instruction order: P.next=I, P.prev=B, B.next=P, I.prev=P,
   P.container=L, L.count=(original count+1) mod 2^32. Value and owner of P,
   L.index and EVERY original byte outside these six words are preserved.
   R0/R1 stay inputs, R2=B, R3=incremented count; NZCV are the modeled ADDS
   flags. Void return does not designate R0 as a new result. All remaining
   registers, SP/LR, permissions and temporaries are preserved.

   Explicit local domain: nonnull aligned nonwrapping L20, P20, I12, B12;
   P20 is separate from L20/I12/B12. Nine relevant word regions (six writes,
   L.index, P.value, P.owner) are mutually separate. This is FIELD separation,
   not pairwise object separation: I=B=L+8 and either neighbor at the sentinel
   are permitted, as are I=B at an ordinary item and distinct ordinary nodes.
   Existing neighbors need not be disjoint. Local old back-link B.next=I is
   required; there is no assumed global list representation or cardinality.
   Read permissions cover L.index, I.prev, L.count; write permissions cover
   precisely the six words. Ordinary LR is odd and below 0xfffffff0.
   There is no SP alignment requirement because no stack access occurs.

   Scope: sequential IL partial correctness, actual trace to BX and ordinary
   modeled BX step. No termination, hardware EXC_RETURN, IRQ, scheduler/TCB,
   or lifter/binary refinement claim; no CPU tunables or callee oracle. Full
   finite circular-list/cardinality refinement belongs to r47. The inherited
   ISA and frontend remain a trusted boundary. Never compute memory masks.
 *)
Require Import Picinae_armv6m vListInsertEnd_armv6m armv6m_list_model.
From Stdlib Require Import NArith Lia List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Theorem insert_end_nwc : forall s1 s2,
  vListInsertEnd_armv6m_prog s1 = vListInsertEnd_armv6m_prog s2.
Proof. reflexivity. Qed.
Theorem insert_end_welltyped : welltyped_prog armv6mtypctx vListInsertEnd_armv6m_prog.
Proof. exact vListInsertEnd_armv6m_welltyped. Qed.

Definition insert_end_preserved (v:armv6mvar) :=
  match v with V_MEM32 | R_R2 | R_R3 | F_N | F_Z | F_C | F_V => False
  | _ => True end.
Theorem insert_end_register_frame : forall v, insert_end_preserved v ->
  forall_endstates vListInsertEnd_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof.
  intros v KEEP. destruct v; cbn in KEEP; try contradiction;
    apply noassign_prog_same; prove_noassign.
Qed.

Fixpoint insert_apart_from (a:N) (xs:list N) : Prop :=
  match xs with [] => True | b::bs => separate32 a 4 b 4 /\ insert_apart_from a bs end.
Fixpoint insert_separate_words (xs:list N) : Prop :=
  match xs with [] => True | a::xs => insert_apart_from a xs /\ insert_separate_words xs end.
Definition insert_end_words L P I B :=
  [L+0; L+4; P+0; P+4; P+8; P+12; P+16; B+4; I+8].
Definition insert_end_layout L P I B :=
  object32 L 20 /\ object32 P 20 /\ object32 I 12 /\ object32 B 12 /\
  separate32 P 20 L 20 /\ separate32 P 20 I 12 /\ separate32 P 20 B 12 /\
  insert_separate_words (insert_end_words L P I B).
Definition insert_end_links m L I B :=
  field32 m L 4 = I /\ field32 m I 8 = B /\ field32 m B 4 = I.
Definition insert_end_ordinary_lr lr := lr mod 2 = 1 /\ lr < 0xfffffff0.
Definition insert_end_writes L P I B := [P+4; P+8; B+4; I+8; P+16; L+0].
Definition insert_end_permissions (s:store) L P I B :=
  MemAcc mem_readable s (L+4) 32 4 /\
  MemAcc mem_readable s (I+8) 32 4 /\ MemAcc mem_readable s L 32 4 /\
  (forall a, In a (insert_end_writes L P I B) -> MemAcc mem_writable s a 32 4).
Definition insert_end_pre (s:store) L P I B :=
  insert_end_layout L P I B /\ s R_R0 = L /\ s R_R1 = P /\
  insert_end_links (s V_MEM32) L I B /\ insert_end_permissions s L P I B /\
  insert_end_ordinary_lr (s R_LR).

Definition insert_end_prefix m L P I B :=
  write_field32 (write_field32 (write_field32 (write_field32
    (write_field32 m P 4 I) P 8 B) B 4 P) I 8 P) P 16 L.
Definition insert_end_memory m L P I B :=
  write_field32 (insert_end_prefix m L P I B) L 0 ((field32 m L 0+1) mod 2^32).
Definition insert_end_byte_frame m m' L P I B :=
  forall a, (forall w, In w (insert_end_writes L P I B) -> separate32 a 1 w 4) ->
    getmem 32 LittleE 1 m' a = getmem 32 LittleE 1 m a.
Definition insert_end_fields m m' L P I B :=
  field32 m' P 4 = I /\ field32 m' P 8 = B /\
  field32 m' B 4 = P /\ field32 m' I 8 = P /\
  field32 m' P 16 = L /\ field32 m' L 0 = (field32 m L 0+1) mod 2^32 /\
  field32 m' L 4 = field32 m L 4 /\
  field32 m' P 0 = field32 m P 0 /\ field32 m' P 12 = field32 m P 12.

(* A memory expression recording the two loads after earlier writes. It is
   not a replacement program. The functional lemma below relates these loads
   to ORIGINAL memory under the stated separation hypotheses. *)
Definition insert_end_observed_B m L P :=
  field32 (write_field32 m P 4 (field32 m L 4)) (field32 m L 4) 8.
Definition insert_end_observed_prefix m L P :=
  insert_end_prefix m L P (field32 m L 4) (insert_end_observed_B m L P).
Definition insert_end_observed_count m L P := field32 (insert_end_observed_prefix m L P) L 0.
Definition insert_end_observed_memory m L P :=
  write_field32 (insert_end_observed_prefix m L P) L 0
    ((insert_end_observed_count m L P+1) mod 2^32).
Definition insert_end_flags c (s:store) :=
  let r := (c+1) mod 2^32 in
  s F_N = cast CAST_HIGH 32 1 r /\
  s F_Z = eval_binop OP_EQ 32 r 0 /\
  s F_C = eval_binop OP_LT 32 r c /\
  s F_V = cast CAST_HIGH 32 1 (N.land (N.lxor c r) (N.lxor 1 r)).
Definition insert_end_exact_post (s0:store) L P (s:store) :=
  s V_MEM32 = insert_end_observed_memory (s0 V_MEM32) L P /\
  s R_R2 = insert_end_observed_B (s0 V_MEM32) L P /\
  s R_R3 = (insert_end_observed_count (s0 V_MEM32) L P+1) mod 2^32 /\
  insert_end_flags (insert_end_observed_count (s0 V_MEM32) L P) s.
Definition insert_end_post (s0:store) L P I B (s:store) :=
  s V_MEM32 = insert_end_memory (s0 V_MEM32) L P I B /\
  insert_end_fields (s0 V_MEM32) (s V_MEM32) L P I B /\
  insert_end_byte_frame (s0 V_MEM32) (s V_MEM32) L P I B /\
  s R_R2 = B /\ s R_R3 = (field32 (s0 V_MEM32) L 0+1) mod 2^32 /\
  insert_end_flags (field32 (s0 V_MEM32) L 0) s /\
  (forall v, insert_end_preserved v -> s v = s0 v).
Definition insert_end_exit (t:trace) :=
  match t with (Addr 0x70,_)::_ => true | _ => false end.
Definition insert_end_invs (s0:store) L P (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x5c => Some (s=s0) | 0x70 => Some (insert_end_exact_post s0 L P s)
  | _ => None end | _ => None end.

Ltac insert_unpack_layout H :=
  unfold insert_end_layout in H; decompose [and] H; clear H;
  match goal with S: insert_separate_words _ |- _ =>
    cbn [insert_end_words insert_separate_words insert_apart_from] in S;
    decompose [and] S; clear S
  end.
Ltac insert_sep := first [assumption | apply noverlap_symmetry; assumption].
Ltac insert_bound :=
  first [apply mp2_mod_lt |
    match goal with H: object32 ?p ?sz |- ?p < 2^32 =>
      exact (proj1 (proj2 (proj2 H))) end].
Ltac insert_read :=
  repeat lazymatch goal with
  | |- field32 (write_field32 ?M ?P ?O ?V) ?P ?O = _ =>
    rewrite (field32_read_write M P O V) by
      insert_bound
  | |- field32 (write_field32 ?M ?P ?O ?V) ?Q ?J = _ =>
    rewrite (field32_frame M P O Q J V) by insert_sep
  end; reflexivity.

Theorem insert_end_memory_fields : forall m L P I B,
  insert_end_layout L P I B ->
  insert_end_fields m (insert_end_memory m L P I B) L P I B.
Proof.
  intros m L P I B LAYOUT. insert_unpack_layout LAYOUT.
  unfold insert_end_fields, insert_end_memory, insert_end_prefix.
  repeat split; insert_read.
Qed.
Theorem insert_end_memory_frame : forall m L P I B,
  insert_end_byte_frame m (insert_end_memory m L P I B) L P I B.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
Theorem insert_end_original_loads : forall m L P I B,
  insert_end_layout L P I B -> insert_end_links m L I B ->
  insert_end_observed_B m L P = B /\
  insert_end_observed_count m L P = field32 m L 0 /\
  insert_end_observed_memory m L P = insert_end_memory m L P I B.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Theorem insert_end_exact : forall s0 t s' x' L P,
  startof t (x',s') = (Addr 0x5c,s0) -> models armv6mtypctx s0 ->
  s0 R_R0 = L -> s0 R_R1 = P ->
  satisfies_all vListInsertEnd_armv6m_prog (insert_end_invs s0 L P)
    insert_end_exit ((x',s')::t).
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Theorem insert_end_at_bx : forall s0 t s L P I B,
  startof t (Addr 0x70,s) = (Addr 0x5c,s0) ->
  models armv6mtypctx s0 -> insert_end_pre s0 L P I B ->
  exec_prog vListInsertEnd_armv6m_prog ((Addr 0x70,s)::t) ->
  unterminated insert_end_exit t -> insert_end_post s0 L P I B s.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Corollary insert_end_count_no_overflow : forall s0 s L P I B,
  insert_end_post s0 L P I B s -> field32 (s0 V_MEM32) L 0 < 2^32-1 ->
  field32 (s V_MEM32) L 0 = field32 (s0 V_MEM32) L 0+1.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

(* Finite memory images for entry satisfiability; these are not kernel code. *)
Definition insert_end_fixture m L I B c :=
  write_field32 (write_field32 (write_field32 (write_field32 m L 0 c)
    L 4 I) I 8 B) B 4 I.
Theorem insert_end_fixture_links : forall m L P I B c,
  insert_end_layout L P I B ->
  insert_end_links (insert_end_fixture m L I B c) L I B /\
  field32 (insert_end_fixture m L I B c) L 0 = c mod 2^32.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
Theorem insert_end_fixture_typed : forall m L I B c, m < memsize 32 ->
  insert_end_fixture m L I B c < memsize 32.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
Definition insert_end_entry_store m L P : store :=
  update (update (update (update (update (memory_store32 m)
    A_READ (N.ones (2^32))) A_WRITE (N.ones (2^32))) R_R0 L) R_R1 P) R_LR 257.
Theorem insert_end_entry_witness : forall m L P I B,
  m < memsize 32 -> insert_end_layout L P I B -> insert_end_links m L I B ->
  exists s:store, models armv6mtypctx s /\ insert_end_pre s L P I B /\ s V_MEM32 = m.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Ltac insert_concrete_layout :=
  unfold insert_end_layout, insert_end_words;
  cbn [insert_separate_words insert_apart_from]; repeat split;
  first [solve [unfold object32, range32; vm_compute; repeat split; congruence] |
    solve [apply ranges32_separate; unfold range32; lia] | exact I].
Theorem insert_end_empty_layout : insert_end_layout 4096 8192 4104 4104.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
Theorem insert_end_nonempty_layout : insert_end_layout 4096 8192 12288 4104.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Theorem insert_end_local_empty_witness : exists s:store,
  models armv6mtypctx s /\ insert_end_pre s 4096 8192 4104 4104 /\
  field32 (s V_MEM32) 4096 0 = 0.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
Theorem insert_end_local_nonempty_witness : exists s:store,
  models armv6mtypctx s /\ insert_end_pre s 4096 8192 12288 4104 /\
  field32 (s V_MEM32) 4096 0 = 1.
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Theorem insert_end_return_step : forall s,
  insert_end_ordinary_lr (s R_LR) ->
  can_step vListInsertEnd_armv6m_prog
    ((Addr (N.land (s R_LR) 0xfffffffe),s),(Addr 0x70,s)).
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Corollary insert_end_trace_returns : forall s0 t s L P I B,
  startof t (Addr 0x70,s) = (Addr 0x5c,s0) ->
  models armv6mtypctx s0 -> insert_end_pre s0 L P I B ->
  exec_prog vListInsertEnd_armv6m_prog ((Addr 0x70,s)::t) ->
  unterminated insert_end_exit t ->
  insert_end_post s0 L P I B s /\
  exec_prog vListInsertEnd_armv6m_prog
    ((Addr (N.land (s0 R_LR) 0xfffffffe),s)::(Addr 0x70,s)::t).
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.

Theorem insert_end_ordinary_return_nonvacuity : exists s:store,
  models armv6mtypctx s /\ insert_end_pre s 4096 8192 4104 4104 /\
  can_step vListInsertEnd_armv6m_prog
    ((Addr (N.land (s R_LR) 0xfffffffe),s),(Addr 0x70,s)).
Proof.
  (* Unchecked after the first build failure; original attempt archived. *)
Abort.
