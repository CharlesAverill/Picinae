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
Lemma ring_hd_member : forall a xs, hd a xs=a \/ In (hd a xs) xs.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_count_insert : forall (left right:list N) P,
  N.of_nat (length (left++P::right))=N.of_nat (length (left++right))+1.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_count_remove : forall (left right:list N) P,
  0<N.of_nat (length (left++P::right)) /\
  N.of_nat (length (left++right))=N.of_nat (length (left++P::right))-1.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_members_insert : forall (left right:list N) P q,
  In q (left++P::right) <-> q=P \/ In q (left++right).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_members_remove : forall (left right:list N) P q,
  NoDup (left++P::right) ->
  (In q (left++right) <-> In q (left++P::right) /\ q<>P).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_nodup_insert : forall (left right:list N) P,
  NoDup (left++right) -> ~In P (left++right) -> NoDup (left++P::right).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_regions_separate : forall L xs p q,
  ring_geometry L xs -> In p (L::xs) -> In q (L::xs) -> p<>q ->
  separate32 p 20 q 20.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_object_fields_separate : forall L xs p q i j,
  ring_geometry L xs -> In p (L::xs) -> In q (L::xs) ->
  In i fields20 -> In j fields20 -> p<>q \/ i<>j ->
  separate32 (p+i) 4 (q+j) 4.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_fresh_geometry : forall m L left right P V O,
  ring_geometry L (left++right) -> ring_fresh m L (left++right) P V O ->
  ring_geometry L (left++P::right).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

(* A byte-range permission includes each contained word. *)
Lemma ring_permission_word : forall (perm:store->addr->Prop) s p off,
  MemAcc perm s p 32 20 -> off+4<=20 -> MemAcc perm s (p+off) 32 4.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

(* Split-independent topology query. Both sentinel and real cursor cases
   are included; right=[] selects the sentinel. *)
Lemma ring_insert_links : forall m L left right idx V O,
  ring_rep m L (left++right) idx V O -> idx=hd (ring_sentinel L) right ->
  insert_end_links m L idx (ring_last (ring_sentinel L) left).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_remove_original : forall m L left P right idx V O,
  ring_rep m L (left++P::right) idx V O ->
  list_remove_original m P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

(* Geometry-to-local-layout obligations are intentionally separate from
   byte-memory transition lemmas. No local contract is assumed as an oracle. *)
Lemma ring_insert_layout : forall m L left right idx P V O,
  ring_rep m L (left++right) idx V O -> idx=hd (ring_sentinel L) right ->
  ring_fresh m L (left++right) P V O ->
  insert_end_layout L P idx (ring_last (ring_sentinel L) left).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Lemma ring_remove_layout : forall m L left P right idx V O,
  ring_rep m L (left++P::right) idx V O ->
  list_remove_layout P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

Theorem ring_insert_pre : forall s L left right idx P V O,
  ring_rep (s V_MEM32) L (left++right) idx V O ->
  idx=hd (ring_sentinel L) right -> ring_fresh (s V_MEM32) L (left++right) P V O ->
  ring_insert_permissions s L (left++right) P ->
  s R_R0=L -> s R_R1=P -> insert_end_ordinary_lr (s R_LR) ->
  insert_end_pre s L P idx (ring_last (ring_sentinel L) left).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_remove_pre : forall s L left P right idx V O,
  ring_rep (s V_MEM32) L (left++P::right) idx V O ->
  ring_permissions s L (left++P::right) -> s R_R0=P ->
  list_remove_pre P (hd (ring_sentinel L) right)
    (ring_last (ring_sentinel L) left) L (N.of_nat (length (left++P::right))) idx s.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

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
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_remove_frame : forall m P nxt prev L c idx,
  list_remove_byte_frame m (list_remove_mem m P nxt prev L c idx) P nxt prev L idx.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)

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
  unfold ring_geometry; repeat split;
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
Theorem ring_empty_witness :
  ring_rep (empty_image 0 4096) 4096 [] 4104 (fun _=>42) (fun _=>99).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_singleton_witness : forall idx, idx=4104 \/ idx=8192 ->
  ring_rep (ring_singleton_image idx) 4096 [8192] idx (fun _=>42) (fun _=>99).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_multi_witness : forall idx, idx=4104 \/ idx=8192 \/ idx=12288 ->
  ring_rep (ring_multi_image idx) 4096 [8192;12288] idx (fun _=>42) (fun _=>99).
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_empty_insert_witness : exists s,
  models armv6mtypctx s /\
  ring_rep (s V_MEM32) 4096 [] 4104 (fun p=>field32 (s V_MEM32) p 0)
    (fun p=>field32 (s V_MEM32) p 12) /\
  insert_end_pre s 4096 8192 4104 4104.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_singleton_remove_witness : forall equal:bool, exists s,
  models armv6mtypctx s /\
  ring_rep (s V_MEM32) 4096 [8192] (if equal then 8192 else 4104)
    (fun _=>42) (fun _=>99) /\
  list_remove_pre 8192 4104 4104 4096 1 (if equal then 8192 else 4104) s.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
Theorem ring_multi_remove_witness : forall idx,
  idx=4104 \/ idx=8192 \/ idx=12288 -> exists s,
  models armv6mtypctx s /\ ring_rep (s V_MEM32) 4096 [8192;12288] idx
    (fun _=>42) (fun _=>99) /\ list_remove_pre 8192 12288 4104 4096 2 idx s.
Abort. (* PARTIAL: initial proof is preserved verbatim in unit notes. *)
