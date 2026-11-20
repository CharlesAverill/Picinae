(* FreeRTOS list fields: a small shared memory specification and proof kit.

   PROVENANCE / AUTHOR
   Official FreeRTOS V11.1.0, commit
   dbf70559b27d39c1fdb68dfb9a32140b6a6777a0; Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Compiler-derived layout: Examples/FreeRTOS/abi.json and
   Examples/freertos/cortex-m0/evidence/layout.json, accepted e05 checkpoint
   95da7ab7cee78f09a528aed86c1dfaf29520a9a8. The five list .json manifests
   have no unsupported instructions or call-closure prerequisites.
   Initial theorem/proof author: OpenAI gpt-6-astra, xhigh (one-shot).
   Final proof repair: OpenAI gpt-6.1-sol, xhigh.
   Initial attempt/failure: notes/r00-list-model/.
   Full validation/final proof producer: notes/r00-list-model-fix/.

   ENGLISH SPECIFICATION / ABI BOUNDARY
   AAPCS32 uses r0 for the list/item pointer, r1 for an inserted item, and
   r0 for uxListRemove's count result. These helpers operate on V_MEM32's
   memory value, using the e03 getmem/setmem operations: four-byte words,
   little endian, modulo 2^32 byte addresses. No 64-bit ABI is imported.
   ListItem_t: 20 bytes, value/next/previous/owner/container at 0/4/8/12/16.
   MiniListItem_t: 12 bytes, value/next/previous at 0/4/8.
   List_t: 20 bytes, count/index/end sentinel at 0/4/8 (sentinel links 12/16).
   Owners are opaque 32-bit values: no dereference or TCB/scheduler contract.

   Pure word read/write and frame lemmas allow modular addresses. Arithmetic
   separation lemmas require nonwrapping ranges; object witnesses additionally
   require nonnull, four-byte-aligned pointers. No arbitrary low/high pointer
   exclusion is imposed. Disjointness is byte disjointness modulo 2^32, so
   overlapping fields must be handled explicitly by later function proofs.
   Frames compare every untouched byte to ORIGINAL memory and compose across
   writes. Empty-list existence is constructed from five writes into a typed
   zero memory, using abstract-width bounds (never evaluating memsize 32).

   SCOPE
   This is a memory helper kit, not a replacement program or a correctness
   theorem for any lifted function. There are no execution paths, exit/invariant
   addresses, CPU tunables, interrupt/callee contracts, or termination claims.
   No permission-map satisfiability or hardware refinement is claimed. Later
   function proofs must supply memory permissions, stack/return ABI conditions,
   and their actual generated program's welltyped/nwc/execution/frame proofs.
   The inherited ARM model/lifting provenance remains a trusted boundary.
 *)

Require Import Picinae_armv6m.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition list_item_size : N := 20.
Definition mini_list_item_size : N := 12.
Definition list_size : N := 20.
Definition item_value_offset : N := 0.
Definition item_next_offset : N := 4.
Definition item_previous_offset : N := 8.
Definition item_owner_offset : N := 12.
Definition item_container_offset : N := 16.
Definition list_count_offset : N := 0.
Definition list_index_offset : N := 4.
Definition list_end_offset : N := 8.
Definition list_max_value : N := 4294967295.

Definition range32 (p n:N) := p < 2^32 /\ p+n <= 2^32.
Definition object32 (p n:N) := p <> 0 /\ p mod 4 = 0 /\ range32 p n.
Definition separate32 (p n q k:N) := ~ overlap 32 p n q k.
Definition field32 (m p off:N) := getmem 32 LittleE 4 m (p+off).
Definition write_field32 (m p off v:N) := setmem 32 LittleE 4 m (p+off) v.
Definition fields20 : list N := [0;4;8;12;16].

Definition outside_frame32 (original current p n:N) :=
  forall a, separate32 a 1 p n ->
    getmem 32 LittleE 1 current a = getmem 32 LittleE 1 original a.

Definition item_contents (m p value next previous owner container:N) :=
  field32 m p item_value_offset = value /\
  field32 m p item_next_offset = next /\
  field32 m p item_previous_offset = previous /\
  field32 m p item_owner_offset = owner /\
  field32 m p item_container_offset = container.

Definition mini_contents (m p value next previous:N) :=
  field32 m p 0 = value /\ field32 m p 4 = next /\ field32 m p 8 = previous.

Definition list_header (m p count index:N) :=
  field32 m p list_count_offset = count /\
  field32 m p list_index_offset = index /\
  field32 m p list_end_offset = list_max_value.

Definition empty_list (m p:N) :=
  object32 p list_size /\ list_header m p 0 (p+8) /\
  field32 m p 12 = p+8 /\ field32 m p 16 = p+8.

Theorem field32_bound: forall m p off, field32 m p off < 2^32.
Proof. intros. unfold field32. apply getmem_bound. Qed.

Theorem field32_read_write:
  forall m p off v, v < 2^32 -> field32 (write_field32 m p off v) p off = v.
Proof.
  intros m p off v B. unfold field32, write_field32.
  rewrite getmem_setmem by discriminate. apply N.mod_small. exact B.
Qed.

Theorem field32_frame:
  forall m p off q other v, separate32 (q+other) 4 (p+off) 4 ->
  field32 (write_field32 m p off v) q other = field32 m q other.
Proof. intros. unfold field32, write_field32. apply getmem_noverlap. exact H. Qed.

(* Nonwrapping arithmetic is kept entirely separate from symbolic memory. *)
Theorem ranges32_separate:
  forall p n q k, range32 p n -> range32 q k ->
  (p+n <= q \/ q+k <= p) -> separate32 p n q k.
Proof.
  intros p n q k [P PN] [Q QK] SEP [i [j [I [J EQ]]]].
  rewrite (N.mod_small (p+i) (2^32)) in EQ by lia.
  rewrite (N.mod_small (q+j) (2^32)) in EQ by lia.
  destruct SEP; lia.
Qed.

Theorem field_address32_nowrap:
  forall p n off, range32 p n -> off < n -> (p+off) mod 2^32 = p+off.
Proof. intros p n off [P PN] O. apply N.mod_small. lia. Qed.

Theorem fields20_separate:
  forall p i j, p+20 <= 2^32 -> In i fields20 -> In j fields20 -> i <> j ->
  separate32 (p+i) 4 (p+j) 4.
Proof.
  intros p i j B I J NE.
  unfold fields20 in I, J.
  repeat destruct I as [<-|I]; try contradiction;
  repeat destruct J as [<-|J]; try contradiction;
  apply ranges32_separate; unfold range32; lia.
Qed.

Theorem field32_object_frame:
  forall m p n off v a, off+4 <= n -> separate32 a 1 p n ->
  getmem 32 LittleE 1 (write_field32 m p off v) a = getmem 32 LittleE 1 m a.
Proof.
  intros m p n off v a IN NO. unfold write_field32.
  apply getmem_noverlap. exact (noverlap_index_r 32 a 1 p n off 4 NO IN).
Qed.

Theorem outside_frame32_refl: forall m p n, outside_frame32 m m p n.
Proof. intros m p n a NO. reflexivity. Qed.

Theorem outside_frame32_trans:
  forall m0 m1 m2 p n, outside_frame32 m0 m1 p n ->
  outside_frame32 m1 m2 p n -> outside_frame32 m0 m2 p n.
Proof. intros m0 m1 m2 p n F1 F2 a NO. rewrite (F2 a NO). exact (F1 a NO). Qed.

Theorem outside_frame32_write:
  forall m0 m p n off v, outside_frame32 m0 m p n -> off+4 <= n ->
  outside_frame32 m0 (write_field32 m p off v) p n.
Proof.
  intros m0 m p n off v FR IN a NO.
  rewrite (field32_object_frame m p n off v a IN NO). exact (FR a NO).
Qed.

(* A finite memory-image constructor for witnesses, not a source-level kernel
   implementation. Its frame is relative to arbitrary original memory m. *)
Definition image20 (m p v0 v4 v8 v12 v16:N) :=
  write_field32
    (write_field32
      (write_field32
        (write_field32 (write_field32 m p 0 v0) p 4 v4) p 8 v8)
      p 12 v12)
    p 16 v16.

Theorem image20_fields:
  forall m p v0 v4 v8 v12 v16,
  p+20 <= 2^32 -> v0 < 2^32 -> v4 < 2^32 -> v8 < 2^32 ->
  v12 < 2^32 -> v16 < 2^32 ->
  item_contents (image20 m p v0 v4 v8 v12 v16) p v0 v4 v8 v12 v16.
Proof.
  intros m p v0 v4 v8 v12 v16 B B0 B4 B8 B12 B16.
  unfold item_contents, item_value_offset, item_next_offset,
    item_previous_offset, item_owner_offset, item_container_offset, image20.
  (* Give each rewrite its exact memory and offsets; tauto also reaches the
     fifth member of fields20, beyond the original auto search depth. *)
  repeat split;
    repeat lazymatch goal with
    | |- field32 (write_field32 ?M ?P ?O ?V) ?P ?O = _ =>
        rewrite (field32_read_write M P O V) by assumption
    | |- field32 (write_field32 ?M ?P ?O ?V) ?P ?I = _ =>
        rewrite (field32_frame M P O P I V)
          by (apply (fields20_separate P I O B);
              [simpl; tauto | simpl; tauto | discriminate])
    end;
    reflexivity.
Qed.

Theorem image20_frame:
  forall m p v0 v4 v8 v12 v16,
  outside_frame32 m (image20 m p v0 v4 v8 v12 v16) p 20.
Proof.
  intros. unfold image20.
  repeat (apply outside_frame32_write; [|discriminate]).
  apply outside_frame32_refl.
Qed.

Theorem image20_welltyped:
  forall m p v0 v4 v8 v12 v16, m < memsize 32 ->
  image20 m p v0 v4 v8 v12 v16 < memsize 32.
Proof.
  intros. unfold image20, write_field32.
  repeat apply setmem_welltyped. exact H.
Qed.

Definition empty_image (m p:N) := image20 m p 0 (p+8) list_max_value (p+8) (p+8).

Theorem empty_image_spec:
  forall m p, object32 p list_size -> empty_list (empty_image m p) p.
Proof.
  intros m p OBJ.
  assert (B: p+20 <= 2^32) by exact (proj2 (proj2 (proj2 OBJ))).
  assert (BP: p+8 < 2^32) by (clear - B; lia).
  pose proof (image20_fields m p 0 (p+8) list_max_value (p+8) (p+8)
    B (mp2_gt_0 32) BP ltac:(unfold list_max_value; reflexivity) BP BP) as F.
  destruct F as [F0 [F4 [F8 [F12 F16]]]].
  split; [exact OBJ|]. split; [repeat split|split]; assumption.
Qed.

Theorem empty_image_frame:
  forall m p, outside_frame32 m (empty_image m p) p list_size.
Proof. intros. apply image20_frame. Qed.

Definition memory_store32 (m:N) : store := update (fun _ => 0) V_MEM32 m.

Theorem memory_store32_welltyped:
  forall m, m < memsize 32 -> models armv6mtypctx (memory_store32 m).
Proof.
  intros m B. unfold memory_store32. apply models_update.
  - change (m < 2^(8*2^32)). rewrite N.mul_comm. exact B.
  - intros v w CV. apply mp2_gt_0.
Qed.

Theorem empty_list_witness:
  forall p, object32 p list_size ->
  exists s:store, models armv6mtypctx s /\ empty_list (s V_MEM32) p /\
    outside_frame32 0 (s V_MEM32) p list_size.
Proof.
  intros p OBJ. exists (memory_store32 (empty_image 0 p)).
  split.
  - apply memory_store32_welltyped. unfold empty_image.
    apply image20_welltyped.
    (* Keep the width abstract so conversion never evaluates memsize 32. *)
    assert (Z: forall w, 0 < memsize w).
    { intro w. change (0 < 2^(2^w*8)). apply mp2_gt_0. }
    exact (Z 32).
  - unfold memory_store32. rewrite update_updated. split.
    + apply empty_image_spec. exact OBJ.
    + apply empty_image_frame.
Qed.

(* Nonempty, aligned, disjoint example regions, including an item and a list.
   No computation below ever inspects a memory value or memsize 32. *)
Theorem list_regions_witness:
  object32 4096 list_size /\ object32 8192 list_item_size /\
  separate32 4096 list_size 8192 list_item_size.
Proof.
  assert (L: object32 4096 list_size).
  { unfold object32, range32, list_size. vm_compute. repeat split; congruence. }
  assert (I: object32 8192 list_item_size).
  { unfold object32, range32, list_item_size. vm_compute. repeat split; congruence. }
  split; [exact L|]. split; [exact I|].
  apply ranges32_separate.
  - exact (proj2 (proj2 L)).
  - exact (proj2 (proj2 I)).
  - left. discriminate.
Qed.

Theorem concrete_empty_list_witness:
  exists s:store, models armv6mtypctx s /\ empty_list (s V_MEM32) 4096 /\
    outside_frame32 0 (s V_MEM32) 4096 list_size.
Proof. apply empty_list_witness. exact (proj1 list_regions_witness). Qed.
