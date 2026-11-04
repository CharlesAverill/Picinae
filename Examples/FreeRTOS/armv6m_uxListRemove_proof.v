(* uxListRemove: local functional contract for the accepted finite ARMv6-M IL.

   Official FreeRTOS V11.1.0 dbf70559b27d39c1fdb68dfb9a32140b6a6777a0.
   Cortex-M0 ELF SHA256
   5c57b3b3d6c04df91f58a9c14cffdd9cf2ded41ebc0663f0c40a3afb3ba308ca.
   Unchanged e05 map uxListRemove_armv6m_prog, 18 instructions, entry 0xa0,
   BX 0xbc; index-equal fixup 0xbe/0xc0/0xc2. No calls or stack accesses.
   Pure helpers: accepted r00 4ff26413448da4d8f064b0273ac5472cc9de7e5a.
   Initial theorem/proof author: OpenAI gpt-6-astra, xhigh/priority.
   One-shot validation status and exact diagnostics: notes/r04-list-remove/.
   No final proof producer is claimed before successful full .vo checking.

   AAPCS32 INPUT: R0=P; original memory has P.next=N, P.prev=B,
   P.container=L, L.count=C>0 and L.index=I. C has its full 32-bit range.
   P and L are nonnull aligned nonwrapping 20-byte objects; N and B have
   nonnull aligned nonwrapping 12-byte link prefixes. Removed item storage
   is separated from the list and both neighbor prefixes. The ten specified
   field slots are byte-disjoint; this does NOT require distinct neighbors
   or list/sentinel disjointness. In particular B=N=L+8 is legal, as are
   distinct neighbors or B=N at another item. Both I=P and I<>P are covered.
   No assumption of global validity/cardinality or a callee oracle is made.
   Read/write permissions are only for actual access words, index writing
   conditional on I=P. Memory/permissions are typed; no large bitmap is
   evaluated. SP need not be aligned because it is not accessed.

   OUTPUT at BX: N.prev=B, B.next=N, L.index=(if I=P then B else I),
   P.container=0, L.count=C-1, R0=C-1. R1=N, R2=0, R3=L.
   P.value, P.owner, P.next and P.prev are preserved. Exact final memory is
   expressed in actual store order over ORIGINAL memory. Every original
   byte outside the actual four/five word write footprint is preserved;
   any other untouched word is preserved too. NZCV are caller-clobbered,
   not part of the preserved frame. R4-R12, SP, LR, permission variables and
   temporary variables are preserved. Ordinary modeled BX requires odd
   LR<0xfffffff0 and lands at LR & 0xfffffffe; EXC_RETURN is excluded.

   SCOPE: local partial correctness of finite IL traces, not termination,
   circular-list cardinality refinement (r47), scheduler/IRQ/TCB correctness,
   hardware correctness, or a new binary/lifter refinement result. No CPU
   tunable assumption beyond the inherited sequential ARMv6-M IL model.
 *)
Require Import Picinae_armv6m uxListRemove_armv6m armv6m_list_model.
From Stdlib Require Import NArith Lia List FunctionalExtensionality.
Import ListNotations ARMv6MNotations.
Open Scope N.

Theorem list_remove_nwc:
  forall s2 s1, uxListRemove_armv6m_prog s1 = uxListRemove_armv6m_prog s2.
Proof. reflexivity. Qed.

Theorem list_remove_welltyped:
  welltyped_prog armv6mtypctx uxListRemove_armv6m_prog.
Proof. exact uxListRemove_armv6m_welltyped. Qed.

Definition list_remove_preserved (v:armv6mvar) :=
  match v with
  | V_MEM32 | R_R0 | R_R1 | R_R2 | R_R3 | F_N | F_Z | F_C | F_V => False
  | _ => True
  end.

Theorem list_remove_register_frame:
  forall v, list_remove_preserved v ->
  forall_endstates uxListRemove_armv6m_prog (fun _ s _ s' => s v = s' v).
Proof.
  intros v KEEP. destruct v; cbn in KEEP; try contradiction;
    apply noassign_prog_same; prove_noassign.
Qed.

Definition rm_slot (p nxt prev l:N) (i:nat) : N :=
  match i with
  | 0%nat => p | 1%nat => p+4 | 2%nat => p+8 | 3%nat => p+12
  | 4%nat => p+16 | 5%nat => l | 6%nat => l+4 | 7%nat => l+8
  | 8%nat => nxt+8 | _ => prev+4
  end.
Definition rm_separated (p nxt prev l:N) :=
  forall i j, (i<10)%nat -> (j<10)%nat -> i<>j ->
    separate32 (rm_slot p nxt prev l i) 4 (rm_slot p nxt prev l j) 4.
Definition list_remove_layout (p nxt prev l:N) :=
  object32 p 20 /\ object32 l 20 /\ object32 nxt 12 /\ object32 prev 12 /\
  separate32 p 20 l 20 /\ separate32 p 20 nxt 12 /\
  separate32 p 20 prev 12 /\ rm_separated p nxt prev l.

Definition rm_read (m a:N) := getmem 32 LittleE 4 m a.
Definition rm_write (m a v:N) := setmem 32 LittleE 4 m a v.
Definition list_remove_original (m p nxt prev l c idx:N) :=
  rm_read m (p+4)=nxt /\ rm_read m (p+8)=prev /\
  rm_read m (p+16)=l /\ rm_read m l=c /\ rm_read m (l+4)=idx.
Definition list_remove_pre (p nxt prev l c idx:N) (s:store) :=
  list_remove_layout p nxt prev l /\ 0<c /\
  s R_R0=p /\ list_remove_original (s V_MEM32) p nxt prev l c idx /\
  (forall a, In a [p+4;p+8;p+16;l;l+4] -> MemAcc mem_readable s a 32 4) /\
  (forall a, In a [nxt+8;prev+4;p+16;l] -> MemAcc mem_writable s a 32 4) /\
  (idx=p -> MemAcc mem_writable s (l+4) 32 4).

(* Expressions for observed intermediate/final memory, never replacement IL. *)
Definition list_remove_linkmem (m nxt prev:N) :=
  rm_write (rm_write m (nxt+8) prev) (prev+4) nxt.
Definition list_remove_indexmem (m p nxt prev l idx:N) :=
  let m1 := list_remove_linkmem m nxt prev in
  if idx =? p then rm_write m1 (l+4) prev else m1.
Definition list_remove_mem (m p nxt prev l c idx:N) :=
  rm_write (rm_write (list_remove_indexmem m p nxt prev l idx) (p+16) 0)
    l (c-1).
Definition list_remove_writes (p nxt prev l idx:N) : list N :=
  [nxt+8;prev+4;p+16;l] ++ (if idx =? p then [l+4] else []).
Definition list_remove_outside (p nxt prev l idx a len:N) :=
  forall w, In w (list_remove_writes p nxt prev l idx) -> separate32 a len w 4.
Definition list_remove_byte_frame (m m' p nxt prev l idx:N) :=
  forall a, list_remove_outside p nxt prev l idx a 1 ->
    getmem 32 LittleE 1 m' a = getmem 32 LittleE 1 m a.
Definition list_remove_effects (m m' p nxt prev l c idx:N) :=
  rm_read m' (nxt+8)=prev /\ rm_read m' (prev+4)=nxt /\
  rm_read m' (l+4)=(if idx =? p then prev else idx) /\
  rm_read m' (p+16)=0 /\ rm_read m' l=c-1 /\
  rm_read m' p=rm_read m p /\ rm_read m' (p+12)=rm_read m (p+12) /\
  rm_read m' (p+4)=nxt /\ rm_read m' (p+8)=prev /\
  list_remove_byte_frame m m' p nxt prev l idx /\
  (forall a, list_remove_outside p nxt prev l idx a 4 -> rm_read m' a=rm_read m a).
Definition list_remove_post (s0:store) (p nxt prev l c idx:N) (s:store) :=
  s V_MEM32=list_remove_mem (s0 V_MEM32) p nxt prev l c idx /\
  s R_R0=c-1 /\ s R_R1=nxt /\ s R_R2=0 /\ s R_R3=l.
Definition list_remove_exit (t:trace) :=
  match t with (Addr 0xbc,_)::_ => true | _ => false end.
Definition list_remove_invs (s0:store) (p nxt prev l c idx:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    match a with
    | 0xa0 => Some (s=s0)
    | 0xb2 => Some (s V_MEM32=list_remove_indexmem (s0 V_MEM32) p nxt prev l idx /\
                   s R_R0=p /\ s R_R1=nxt /\ s R_R3=l)
    | 0xbc => Some (list_remove_post s0 p nxt prev l c idx s)
    | _ => None end
  | _ => None end.

Lemma rm_read_write:
  forall m a v, v<2^32 -> rm_read (rm_write m a v) a=v.
Proof.
  intros m a v B. unfold rm_read, rm_write.
  rewrite getmem_setmem by discriminate. apply N.mod_small. exact B.
Qed.
Lemma rm_read_frame:
  forall m a v b, separate32 b 4 a 4 -> rm_read (rm_write m a v) b=rm_read m b.
Proof. intros. unfold rm_read, rm_write. apply getmem_noverlap. assumption. Qed.

Theorem list_remove_mem_frame:
  forall m p nxt prev l c idx a len,
  list_remove_outside p nxt prev l idx a len ->
  getmem 32 LittleE len (list_remove_mem m p nxt prev l c idx) a =
  getmem 32 LittleE len m a.
Proof.
  intros m p nxt prev l c idx a len OUT.
  unfold list_remove_outside, list_remove_writes in OUT.
  unfold list_remove_mem, list_remove_indexmem, list_remove_linkmem, rm_write.
  destruct (idx =? p) eqn:E;
    repeat rewrite getmem_noverlap by (apply OUT; cbn; tauto);
    reflexivity.
Qed.

(* Find a field's finite slot without unfolding a memory value. *)
Ltac rm_find_slot p nxt prev l a k :=
  let rec search i :=
    lazymatch i with
    | 10%nat => fail 1 "not a local field slot" a
    | _ => let b := eval cbv [rm_slot] in (rm_slot p nxt prev l i) in
           first [constr_eq a b; k i | let j := eval compute in (S i) in search j]
    end in search 0%nat.
Ltac rm_sep SEP :=
  lazymatch type of SEP with rm_separated ?p ?nxt ?prev ?l =>
    lazymatch goal with |- separate32 ?a 4 ?b 4 =>
      rm_find_slot p nxt prev l a ltac:(fun i =>
        rm_find_slot p nxt prev l b ltac:(fun j =>
          apply (SEP i j); lia))
    end
  end.
Ltac rm_load SEP :=
  repeat lazymatch goal with
  | |- context [rm_read (rm_write ?m ?a ?v) ?b] =>
    first [constr_eq a b; rewrite (rm_read_write m a v) by assumption
          | rewrite (rm_read_frame m a v b) by (rm_sep SEP)]
  end.

Theorem list_remove_mem_effects:
  forall m p nxt prev l c idx,
  list_remove_layout p nxt prev l -> 0<c ->
  list_remove_original m p nxt prev l c idx ->
  list_remove_effects m (list_remove_mem m p nxt prev l c idx) p nxt prev l c idx.
Proof.
  intros m p nxt prev l c idx [PO [LO [NO [BO [PL [PN [PB SEP]]]]]]] POS ORIG.
  destruct ORIG as [RN [RB [RL [RC RI]]]].
  assert (NB: nxt<2^32) by exact (proj1 (proj2 (proj2 NO))).
  assert (BB: prev<2^32) by exact (proj1 (proj2 (proj2 BO))).
  assert (CB: c<2^32) by (rewrite <- RC; apply getmem_bound).
  assert (SUB: c-1<2^32) by (clear - CB; lia).
  assert (ZERO: 0<2^32) by apply mp2_gt_0.
  unfold list_remove_effects. repeat split.
  all: try (unfold list_remove_byte_frame; intros; apply list_remove_mem_frame; assumption).
  all: try (intros a OUT; apply list_remove_mem_frame; exact OUT).
  all: unfold list_remove_mem, list_remove_indexmem, list_remove_linkmem;
    destruct (idx =? p) eqn:E; rm_load SEP; assumption || reflexivity.
Qed.

Theorem list_remove_correct:
  forall s0 t s' x' p nxt prev l c idx
    (ENTRY: startof t (x',s')=(Addr 0xa0,s0))
    (MDL: models armv6mtypctx s0) (INPUT: list_remove_pre p nxt prev l c idx s0),
  satisfies_all uxListRemove_armv6m_prog (list_remove_invs s0 p nxt prev l c idx)
    list_remove_exit ((x',s')::t).
Abort.

Theorem list_remove_at_bx:
  forall s0 t s p nxt prev l c idx,
  startof t (Addr 0xbc,s)=(Addr 0xa0,s0) -> models armv6mtypctx s0 ->
  list_remove_pre p nxt prev l c idx s0 ->
  exec_prog uxListRemove_armv6m_prog ((Addr 0xbc,s)::t) ->
  unterminated list_remove_exit t ->
  list_remove_post s0 p nxt prev l c idx s /\
  list_remove_effects (s0 V_MEM32) (s V_MEM32) p nxt prev l c idx /\
  (forall v, list_remove_preserved v -> s v=s0 v).
Abort.

Definition list_remove_ordinary_lr (lr:N) := lr mod 2=1 /\ lr<0xfffffff0.
Theorem list_remove_return_step:
  forall s, models armv6mtypctx s -> list_remove_ordinary_lr (s R_LR) ->
  can_step uxListRemove_armv6m_prog
    ((Addr (N.land (s R_LR) 0xfffffffe),s),(Addr 0xbc,s)).
Abort.

Definition list_remove_entry_store (m p lr:N) : store :=
  update (update (update (update (memory_store32 m) R_R0 p) R_LR lr)
    A_READ (N.ones (2^32))) A_WRITE (N.ones (2^32)).
Theorem list_remove_entry_witness:
  forall m p nxt prev l c idx lr,
  m<memsize 32 -> list_remove_layout p nxt prev l -> 0<c ->
  list_remove_original m p nxt prev l c idx -> lr<2^32 ->
  exists s, models armv6mtypctx s /\ list_remove_pre p nxt prev l c idx s /\
    s V_MEM32=m /\ s R_LR=lr.
Abort.

(* Singleton at list+8, both legal index cases. Arbitrary original memory,
   item value and owner remain opaque; only the two witness objects are set. *)
Definition list_remove_singleton_image (m value owner:N) (equal:bool) :=
  image20 (image20 m 4096 1 (if equal then 8192 else 4104)
    list_max_value 8192 8192) 8192 value 4104 4104 owner 4096.
Theorem list_remove_singleton_layout:
  list_remove_layout 8192 4104 4104 4096.
Abort.
Theorem list_remove_singleton_witness:
  forall m value owner equal, m<memsize 32 -> value<2^32 -> owner<2^32 ->
  exists s, models armv6mtypctx s /\
    list_remove_pre 8192 4104 4104 4096 1 (if equal then 8192 else 4104) s /\
    s V_MEM32=list_remove_singleton_image m value owner equal /\
    list_remove_ordinary_lr (s R_LR).
Abort.

(* A distinct-neighbor multi-node local entry, with either index branch.
   This is a satisfiability witness, not an assumed finite-list representation. *)
Theorem list_remove_multi_layout:
  list_remove_layout 8192 12288 16384 4096.
Abort.
Theorem list_remove_multi_witness:
  forall equal:bool, exists s, models armv6mtypctx s /\
    list_remove_pre 8192 12288 16384 4096 3 (if equal then 8192 else 16384) s /\
    list_remove_ordinary_lr (s R_LR).
Abort.

Theorem list_remove_returns:
  forall s0 t s p nxt prev l c idx,
  startof t (Addr 0xbc,s)=(Addr 0xa0,s0) -> models armv6mtypctx s0 ->
  list_remove_pre p nxt prev l c idx s0 -> list_remove_ordinary_lr (s0 R_LR) ->
  exec_prog uxListRemove_armv6m_prog ((Addr 0xbc,s)::t) ->
  unterminated list_remove_exit t ->
  can_step uxListRemove_armv6m_prog
    ((Addr (N.land (s0 R_LR) 0xfffffffe),s),(Addr 0xbc,s)) /\
  s R_R0=c-1 /\
  list_remove_effects (s0 V_MEM32) (s V_MEM32) p nxt prev l c idx /\
  (forall v, list_remove_preserved v -> s v=s0 v).
Abort.
