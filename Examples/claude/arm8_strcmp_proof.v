(* strcmp -- Ubuntu AArch64 glibc 2.35-0ubuntu3.15, complete scalar map.

   PROVENANCE: /lib/aarch64-linux-gnu/libc.so.6, SHA256
   79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06;
   image base 0x100000, ELF entry 0x92f80, IL entry 0x192f80,
   77 instructions / 308 bytes. Ghidra 11.4.2, strict scalar replacement
   pcode2coq_scalar.py from reviewed e30 bbad592. The generated map and its
   manifest are unchanged. No verified binary/lifter refinement is assumed.

   AUTHOR: OpenAI gpt-6-astra, xhigh/default; one-shot initial attempt.
   STATUS: PARTIAL. First full build failed at strcmp_correct (open goals).
   Final proof producer: none. Initial source and raw diagnostics are under
   notes/a-strcmp/. The final Abort only packages the failed attempt safely;
   no second build or proof repair was performed by Astra.

   SPEC: int strcmp(const char *p, const char *q).
   X0=p, X1=q, original memory=m. K is the first unsigned-byte difference
   or common NUL. The sign of signed32(W0) agrees with the unsigned comparison
   of m[p+K] and m[q+K]. The bit-granular CLZ/shift exit need not return their
   exact difference. SP, X30, X19..X29, full modeled Z8..Z15, memory and access
   masks are preserved. X30, not the separate modeled R_LR, is used by RET.

   DOMAIN: little-endian AArch64 scalar IL, 64-bit pointers, 32-bit C result;
   no tunable, NEON, CPU-feature, disjointness, or alignment premise.
   Readable envelope (half-open):
     p: [8*(p/8), 8*((p+K)/8)+8)
     q: [8*(q/8), 8*((q+K)/8)+16).
   Both upper endpoints must be strictly below 2^64. These are explicit,
   conservative sufficient padding assumptions, not minimal C-object bounds:
   <=7 prefix bytes each; <=7 suffix bytes for p; <=15 suffix bytes for q.
   The extra q word covers the unequal-alignment lookahead at 0x193060.
   Page-boundary inputs are permitted when this envelope is readable; this
   is not a claim for inaccessible suffix pages. A_READ supplies the actual
   model permission bits. Aliases p=q and overlapping read-only strings are
   allowed. K is unbounded except for the stated address envelope.

   CONTROL FLOW: same-alignment loop 0x192fa0; common misaligned prefix
   0x192ff0; distinct-alignment byte loop 0x193018; aligned-q setup 0x193034;
   lookahead loop 0x193060; terminal partial q word 0x193090. Word paths join
   at REV/CLZ 0x192fc4. There are TWO RET instructions (0x192fe4,0x1930b0),
   not three. Both are exits below; no path is excluded by a False invariant.
   The intended theorem stops before RET: partial correctness, not termination,
   executed caller return, fault freedom, hardware soundness or concurrency.
*)

Require Import Picinae_armv8.
Require Import Picinae.Examples.claude.lifter.scalar_ccmp.e30_strcmp_arm8.
Require Import arm8_common.
From Stdlib Require Import NArith ZArith Lia List.
Import ARM8Notations ListNotations.
Open Scope N.

Definition strcmp_stop (m:memory) p q K :=
  (forall k, k < K ->
     m Ⓑ[p ⊕ k] = m Ⓑ[q ⊕ k] /\ m Ⓑ[p ⊕ k] <> 0) /\
  (m Ⓑ[p ⊕ K] <> m Ⓑ[q ⊕ K] \/ m Ⓑ[p ⊕ K] = 0).

Definition strcmp_down8 (p:N) := 8 * (p / 8).
Definition strcmp_domain (readable p q K:N) :=
  strcmp_down8 (p+K) + 8 < 2^64 /\
  strcmp_down8 (q+K) + 16 < 2^64 /\
  (forall a, strcmp_down8 p <= a < strcmp_down8 (p+K)+8 ->
     N.testbit readable a = true) /\
  (forall a, strcmp_down8 q <= a < strcmp_down8 (q+K)+16 ->
     N.testbit readable a = true).

Definition strcmp_saved :=
  [R_SP; R_X30; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24;
   R_X25; R_X26; R_X27; R_X28; R_X29;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15;
   A_READ; A_WRITE].

Definition strcmp_frame (s0 s:store) :=
  s V_MEM64 = s0 V_MEM64 /\
  forall v, In v strcmp_saved -> s v = s0 v.

Definition strcmp_post (s0:store) (m:memory) p q K (s:store) :=
  Z.compare (toZ 32 (s R_X0)) 0 =
    N.compare (m Ⓑ[p ⊕ K]) (m Ⓑ[q ⊕ K]) /\ strcmp_frame s0 s.

Definition strcmp_exit (t:trace) :=
  match t with
  | (Addr 0x192fe4,_)::_ | (Addr 0x1930b0,_)::_ => true
  | _ => false
  end.

Definition strcmp_byte (x j:N) := (x >> (8*j)) mod 256.

(* At the common word decoder, the local first stop j is related directly
   to ORIGINAL memory, not to a guessed return value. Bytes after j are free. *)
Definition strcmp_pair (m:memory) p q K x y j :=
  (forall i, i < j ->
    strcmp_byte x i = strcmp_byte y i /\ strcmp_byte x i <> 0) /\
  strcmp_byte x j = m Ⓑ[p ⊕ K] /\
  strcmp_byte y j = m Ⓑ[q ⊕ K].

(* A proof must establish this syndrome invariant from SUB/OR/BICS and the
   shifted q mask. It is NOT a hypothesis of the entry theorem. Inclusion of
   all XOR bits prevents CLZ from shifting away the first differing bit. *)
Definition strcmp_syndrome x y r j :=
  r < 2^64 /\ r .| (x .^ y) = r /\
  (forall i, i < j -> strcmp_byte r i = 0) /\ strcmp_byte r j <> 0.

Definition strcmp_live (s0 s:store) :=
  strcmp_frame s0 s /\ s R_X8 = 0x0101010101010101.

Definition strcmp_aligned (s0:store) p q K (s:store) :=
  strcmp_live s0 s /\ p mod 8 = q mod 8 /\
  s R_X10 = msub 64 q p /\
  exists i, i <= K /\ s R_X0 = p+i /\ (p+i) mod 8 = 0.

Definition strcmp_byte_loop (s0:store) p q K (s:store) :=
  strcmp_live s0 s /\ p mod 8 <> q mod 8 /\
  s R_X10 = msub 64 q p /\
  exists i, i <= K /\ s R_X0 = p+i /\ s R_X1 = q+i.

Definition strcmp_lookahead (s0:store) (m:memory) p q K (s:store) :=
  strcmp_live s0 s /\ s R_X10 = msub 64 q p /\
  exists i, i <= K /\ s R_X0 = p+i /\ (p+i) mod 8 = 0 /\
    (q+i) mod 8 <> 0 /\
    s R_X5 = msub 64 (strcmp_down8 (q+i)+8) (p+i) /\
    s R_X9 mod 64 = (64-8*((q+i) mod 8)) mod 64 /\
    (forall j, j < 8-(q+i) mod 8 -> m Ⓑ[(q+i) ⊕ j] <> 0).

Definition strcmp_decode (s0:store) (m:memory) p q K (s:store) :=
  strcmp_frame s0 s /\ exists j, j < 8 /\
    strcmp_pair m p q K (s R_X2) (s R_X3) j /\
    strcmp_syndrome (s R_X2) (s R_X3) (s R_X6) j.

Definition strcmp_invs (s0:store) (m:memory) p q K (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x192f80 => Some (s = s0)
  | 0x192fa0 => Some (strcmp_aligned s0 p q K s)
  | 0x192fc4 => Some (strcmp_decode s0 m p q K s)
  | 0x193018 => Some (strcmp_byte_loop s0 p q K s)
  | 0x193060 => Some (strcmp_lookahead s0 m p q K s)
  | 0x192fe4 | 0x1930b0 => Some (strcmp_post s0 m p q K s)
  | _ => None end | _ => None end.

(* Intended full-entry theorem statement is fixed before the initial proof.
   The proof appears after the elementary facts and nonvacuity witnesses. *)
Definition strcmp_full_contract : Prop :=
  forall s0 t s' x' m p q K
    (ENTRY: startof t (x',s') = (Addr 0x192f80,s0))
    (MDL: models arm8typctx s0)
    (MEM: s0 V_MEM64 = m) (P: s0 R_X0 = p) (Q: s0 R_X1 = q)
    (STOP: strcmp_stop m p q K)
    (READ: strcmp_domain (s0 A_READ) p q K),
  satisfies_all e30_strcmp_arm8 (strcmp_invs s0 m p q K)
    strcmp_exit ((x',s')::t).

Theorem strcmp_nwc: forall s2 s1, e30_strcmp_arm8 s1 = e30_strcmp_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions strcmp_nwc.

Theorem strcmp_welltyped: welltyped_prog arm8typctx e30_strcmp_arm8.
Proof. exact e30_strcmp_arm8.welltyped. Qed.
Print Assumptions strcmp_welltyped.

Theorem strcmp_preserves_memory:
  forall_endstates e30_strcmp_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Print Assumptions strcmp_preserves_memory.

Theorem strcmp_preserves_callee_saved:
  forall v, In v strcmp_saved ->
  forall_endstates e30_strcmp_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same. unfold strcmp_saved in IN.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Print Assumptions strcmp_preserves_callee_saved.

Theorem strcmp_preserves_frame:
  forall_endstates e30_strcmp_arm8 (fun _ s _ s' => strcmp_frame s s').
Proof.
  intros t x s x' s' XP ENTRY. split.
  - symmetry. exact (strcmp_preserves_memory t x s x' s' XP ENTRY).
  - intros v IN. symmetry.
    exact (strcmp_preserves_callee_saved v IN t x s x' s' XP ENTRY).
Qed.
Print Assumptions strcmp_preserves_frame.

Lemma strcmp_byte_bound: forall x j, strcmp_byte x j < 256.
Proof. intros. unfold strcmp_byte. apply N.mod_lt. discriminate. Qed.
Print Assumptions strcmp_byte_bound.

Lemma strcmp_stop_unique: forall m p q K L,
  strcmp_stop m p q K -> strcmp_stop m p q L -> K = L.
Proof.
  intros m p q K L [PK SK] [PL SL].
  destruct (N.lt_trichotomy K L) as [LT|[EQ|GT]].
  - destruct (PL K LT) as [E NZ]. destruct SK; contradiction.
  - exact EQ.
  - destruct (PK L GT) as [E NZ]. destruct SL; contradiction.
Qed.
Print Assumptions strcmp_stop_unique.

Lemma strcmp_domain_ones: forall p q K cap,
  strcmp_down8 (p+K)+8 < 2^64 ->
  strcmp_down8 (q+K)+16 < 2^64 ->
  strcmp_down8 (p+K)+8 <= cap ->
  strcmp_down8 (q+K)+16 <= cap ->
  strcmp_domain (N.ones cap) p q K.
Proof.
  intros p q K cap P Q CP CQ. unfold strcmp_domain.
  split; [exact P|]. split; [exact Q|]. split; intros a [LO HI];
    apply N.ones_spec_low; lia.
Qed.
Print Assumptions strcmp_domain_ones.

(* Concrete input witnesses: equal alias containing a high byte; unequal
   distinct alignments (both signs); either terminates; empty overlapping
   strings; page-end addresses. No execution or result premise is supplied. *)
Definition strcmp_samples : list (memory * N * N * N) :=
  [(128 << 8,1,1,1);
   ((128 << 8) .| (255 << 80),1,10,0);
   ((255 << 24) .| (128 << 136),3,17,0);
   (200 << 128,7,16,0);
   (200 << 128,16,7,0);
   (0,0,1,0);
   (0,4095,8190,0)].

Lemma strcmp_samples_stop: forall m p q K,
  In (m,p,q,K) strcmp_samples -> strcmp_stop m p q K.
Proof.
  intros m p q K IN. unfold strcmp_samples in IN.
  repeat destruct IN as [E|IN]; try contradiction;
    inversion E; subst; clear E; unfold strcmp_stop; split.
  all: try solve [intros k HK; exfalso; lia].
  all: try solve [intros k HK; assert (k=0) by lia; subst k;
                 vm_compute; split; [reflexivity|discriminate]].
  all: vm_compute; intuition discriminate.
Qed.
Print Assumptions strcmp_samples_stop.

Lemma strcmp_samples_readable: forall m p q K,
  In (m,p,q,K) strcmp_samples -> strcmp_domain (N.ones 16384) p q K.
Proof.
  intros m p q K IN. unfold strcmp_samples in IN.
  repeat destruct IN as [E|IN]; try contradiction;
    inversion E; subst; clear E; apply strcmp_domain_ones;
    vm_compute; intuition discriminate.
Qed.
Print Assumptions strcmp_samples_readable.

(* One-shot full-function attempt. Invariant preservation must derive the
   local word-pair/syndrome facts from real instruction execution. Neither
   those facts nor a previous function-correctness theorem is assumed. *)
Theorem strcmp_correct: strcmp_full_contract.
Proof.
  unfold strcmp_full_contract. intros.
  apply prove_invs.
  - simpl. rewrite ENTRY. arm8_step. reflexivity.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply strcmp_welltyped. intro MDL1.
    clear - PRE MDL1 MDL MEM P Q STOP READ.
    rename t1 into t.
    destruct_inv 64 PRE.
    all: try match type of PRE with ?s = ?s0 => subst s end.
    all: repeat arm8_step.
    all: try solve [unfold strcmp_live, strcmp_frame;
                    repeat split; intros; reflexivity].
    all: try solve [assumption].
    all: match goal with |- ?G => idtac "UNRESOLVED STRCMP INVARIANT:" G end.
Abort.
(* strcmp_correct has no declaration: its initial Qed failed. The exact
   original statement, attempt and Print command are preserved verbatim in
   notes/a-strcmp/arm8_strcmp_proof.initial.v.txt. *)
