(* SOL FIXER STATUS: BLOCKED before compiler admission. No new proof is
   certified by a-memset-emag-fix. The restored author candidate and proposed
   script repairs are in notes/a-memset-emag-fix/restored-repair-candidate.v.txt.
   All 22 author statements and original four Qed bodies below are retained;
   remaining statements stay Abort. See the fixer README and gate log. *)

(* PARTIAL HANDOFF: the single full build exited 1 at original line 147,
   unavailable N.pow_pos_nonneg in the inhabited-input witness. No Astra
   repair cycle was run. All declarations from that witness onward are
   aborted, not proved; exact statements and original scripts are retained
   in notes/a-memset-emag/initial-attempt.v.txt. Earlier four Qed commands
   were reached, but no full .vo or new-theorem assumptions certificate was
   produced. This sanitized handoff source has not been rebuilt. *)

(* __memset_emag: the exact scalar AArch64 implementation, all size paths.

   void *memset(void *d, int c, size_t n): write low8(c) to n bytes and
   return d, preserving every byte outside the destination.

   PROVENANCE: Ubuntu AArch64 glibc 2.35-0ubuntu3.15,
   /lib/aarch64-linux-gnu/libc.so.6, SHA256
   79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF symbol __memset_emag at 0x9c300, image base 0x100000; lifted entry
   0x19c300, 56 instructions through RET at 0x19c3dc. The unchanged e08
   artifact and its manifest record Ghidra 11.4.2 raw SLEIGH pcode and the
   e11 strict scalar replacement, staticMemory=False. Lifting is trusted;
   no hardware refinement, permissions, faults, concurrency or timing claim.

   AUTHOR: OpenAI gpt-6-astra, xhigh, default tier, one-shot initial attempt.
   Final proof producer is unset until full .vo and assumptions checks pass.
   Memory-set helpers below adapt the baseline Claude Opus 5.5 fill-set
   method to ARM8; no AMD64 proof module or admitted memset theorem imported.

   AAPCS64: X0=d, low8(X1)=c mod 256, X2=n. Pointers/counts are 64 bits.
   Required: typed state and d+n <= 2^64. The mathematical end may equal
   2^64: X4 then holds zero and tail addresses use modular subtraction.
   No alignment, overlap, source-read, CPU-ZVA, vector or tunable hypothesis.
   No separate source exists; overlapping stores are allowed. For n=0,
   arbitrary d and memory are allowed; there is no destination access.
   The IL models memory as a total bitvector, not an allocated-object heap.
   SP, X30, X19..X29 and modeled Z8..Z15 are preserved (indeed full Z views).
   The functional invariant stops BEFORE each RET. A separate RET lemma
   describes the jump to X30. satisfies_all is partial correctness only:
   it does not prove existence of a terminating execution.
*)

Require Import Picinae_armv8 arm8_common e08___memset_emag_arm8.
From Stdlib Require Import NArith ZArith Lia List.
Import ARM8Notations ListNotations.
Open Scope N.

Definition memset_emag_saved :=
  [R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25; R_X26;
   R_X27; R_X28; R_X29; R_SP; R_X30;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15].
Definition memset_emag_frame (s0 s:store) :=
  forall v, In v memset_emag_saved -> s v = s0 v.
Definition memset_emag_permitted (d n:N) := d < 2^64 /\ n < 2^64 /\ d+n <= 2^64.
Definition memset_emag_pre (s0 s:store) (d c n:N) :=
  s V_MEM64 = s0 V_MEM64 /\ s R_X0 = d /\ s R_X1 = c /\
  s R_X2 = n /\ memset_emag_frame s0 s.
Definition memset_emag_filled (m m':memory) (d c n:N) :=
  (forall i, i < n -> m' Ⓑ[d ⊕ i] = c mod 256) /\
  (forall b, ~ (msub 64 b d < n) -> m' Ⓑ[b] = m Ⓑ[b]).
Definition memset_emag_post (s0:store) (d c n:N) (s:store) :=
  s R_X0 = d /\ memset_emag_frame s0 s /\
  memset_emag_filled (s0 V_MEM64) (s V_MEM64) d c n.
Definition memset_emag_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x19c330 | 0x19c344 | 0x19c358 | 0x19c378 | 0x19c394 | 0x19c3dc => true
  | _ => false end | _ => false end.

(* Partial memory fact: the filled offsets are exactly W, including frame. *)
Definition fil (m m':memory) d c (W:N->Prop) :=
  (forall i, W i -> m' Ⓑ[d ⊕ i] = c) /\
  (forall b, ~ W (msub 64 b d) -> m' Ⓑ[b] = m Ⓑ[b]).
Definition bytes_are (v L c:N) := forall k, k < L -> xbits v (8*k) (8*k+8) = c.
Definition memset_emag_ready (s0:store) (d c n:N) (s:store) :=
  s R_X0 = d /\ s R_X2 = n /\ s R_X4 = d ⊕ n /\
  bytes_are (s R_X1) 8 (c mod 256) /\ memset_emag_frame s0 s.
Definition memset_emag_clean (s0:store) (d c n:N) (s:store) :=
  memset_emag_ready s0 d c n s /\ s V_MEM64 = s0 V_MEM64.

(* q is the aligned cursor, not an offset that could underflow at entry.
   Each iteration writes [q+16,q+80); the first head store covers [d,d+16).
   e=d+n is mathematical, including e=2^64. Count is e-q-81 at the head.
   At tail q is the cursor AFTER writeback and r is the PRE-subtraction
   count, 0<=r<64; X2=msub64 r 64, whose bit 5 is exactly bit 5 of r. *)
Definition memset_emag_loop (s0:store) (d c n:N) (s:store) :=
  exists q, 96 < n /\ q mod 16 = 0 /\ d <= q+16 /\ q+81 <= d+n /\
    s R_X0 = d /\ s R_X3 = q /\ s R_X4 = d ⊕ n /\
    s R_X2 = d+n-q-81 /\ bytes_are (s R_X1) 8 (c mod 256) /\
    memset_emag_frame s0 s /\
    fil (s0 V_MEM64) (s V_MEM64) d (c mod 256)
        (fun i => i < N.max 16 (q+16-d)).
Definition memset_emag_tail (s0:store) (d c n:N) (s:store) :=
  exists q r, 96 < n /\ d <= q /\ r < 64 /\ d+n = q+17+r /\
    s R_X0 = d /\ s R_X3 = q /\ s R_X4 = d ⊕ n /\
    s R_X2 = msub 64 r 64 /\ bytes_are (s R_X1) 8 (c mod 256) /\
    memset_emag_frame s0 s /\
    fil (s0 V_MEM64) (s V_MEM64) d (c mod 256) (fun i => i < q+16-d).

Definition memset_emag_invs (s0:store) (d c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x19c300 => Some (memset_emag_pre s0 s d c n)
  | 0x19c310 => Some (s R_X0 = d /\ s R_X2 = n /\
      bytes_are (s R_X1) 8 (c mod 256) /\ memset_emag_frame s0 s /\
      s V_MEM64 = s0 V_MEM64)
  | 0x19c324 => Some (n < 16 /\ memset_emag_clean s0 d c n s)
  | 0x19c338 => Some (n < 8 /\ memset_emag_clean s0 d c n s)
  | 0x19c348 => Some (n < 4 /\ memset_emag_clean s0 d c n s)
  | 0x19c360 => Some (16 <= n <= 96 /\ memset_emag_clean s0 d c n s)
  | 0x19c380 => Some (64 <= n <= 96 /\ memset_emag_ready s0 d c n s /\
      fil (s0 V_MEM64) (s V_MEM64) d (c mod 256) (fun i => i < 16))
  | 0x19c3a0 => Some (96 < n /\ memset_emag_clean s0 d c n s)
  | 0x19c3b0 => Some (memset_emag_loop s0 d c n s)
  | 0x19c3c8 => Some (memset_emag_tail s0 d c n s)
  | 0x19c330 | 0x19c344 | 0x19c358 | 0x19c378 | 0x19c394 | 0x19c3dc =>
      Some (memset_emag_post s0 d c n s)
  | _ => None end | _ => None end.

(* Full intended contract, declared before any proof attempt. No conclusion
   or callee contract appears among the hypotheses. *)
Definition memset_emag_contract : Prop :=
  forall s t s' x' d c n,
    startof t (x',s') = (Addr 0x19c300,s) -> models arm8typctx s ->
    s R_X0 = d -> s R_X1 = c -> s R_X2 = n ->
    memset_emag_permitted d n ->
    satisfies_all e08___memset_emag_arm8 (memset_emag_invs s d c n)
      memset_emag_exit ((x',s')::t).

Theorem memset_emag_nwc: forall s2 s1,
  e08___memset_emag_arm8 s1 = e08___memset_emag_arm8 s2.
Proof. reflexivity. Qed.
Theorem memset_emag_welltyped: welltyped_prog arm8typctx e08___memset_emag_arm8.
Proof. exact e08___memset_emag_arm8.welltyped. Qed.
Theorem memset_emag_preserves_callee_saved:
  forall v, In v memset_emag_saved ->
  forall_endstates e08___memset_emag_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same. unfold memset_emag_saved in IN.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Theorem memset_emag_preserves_result:
  forall_endstates e08___memset_emag_arm8 (fun _ s _ s' => s R_X0 = s' R_X0).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition memset_emag_witness (d c n sp lr:N) : store := fun v =>
  match v with R_X0 => d | R_X1 => c | R_X2 => n | R_SP => sp | R_X30 => lr | _ => 0 end.
Theorem memset_emag_inputs_inhabited:
  forall d c n sp lr,
    memset_emag_permitted d n -> c < 2^64 -> sp < 2^64 -> lr < 2^64 ->
    exists s, models arm8typctx s /\ memset_emag_pre s s d c n /\
      s R_SP = sp /\ s R_X30 = lr /\ s V_MEM64 = 0.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.
Theorem memset_emag_zero_spec: forall m d c, memset_emag_filled m m d c 0.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

(* Pure range obligations cover every actual branch without restricting n
   to small sizes. The tail ranges overlap the head/loop ranges as needed. *)
Lemma memset_emag_short_cover: forall n L i,
  0 < L -> L <= n <= 2*L ->
  (i < L \/ n-L <= i < n) <-> i < n.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.
Lemma memset_emag_medium_cover: forall n i,
  64 <= n <= 96 -> (i < 64 \/ n-32 <= i < n) <-> i < n.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.
Lemma memset_emag_loop_advance: forall d n q,
  96 < n -> d <= q+16 -> q+81 <= d+n ->
  (forall i, (i < N.max 16 (q+16-d) \/ q+16-d <= i < q+80-d)
       <-> i < q+80-d) /\
  (64 <= d+n-q-81 -> (q+64)+81 <= d+n) /\
  (d+n-q-81 < 64 -> d+n = (q+64)+17+(d+n-q-81)).
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.
Lemma memset_emag_tail_cover: forall d n q r i,
  d <= q -> d+n = q+17+r -> r < 64 ->
  (i < q+16-d \/ (32 <= r /\ q+16-d <= i < q+48-d) \/ n-32 <= i < n)
    <-> i < n.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma byte_setmem_cases:
  forall (m:memory) a L v b, 0 < L -> L <= 2^64 ->
  (setmem 64 LittleE L m a v) Ⓑ[b] =
  if msub 64 b a <? L then xbits v (8 * msub 64 b a) (8 * msub 64 b a + 8) else m Ⓑ[b].
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma msub_off:
  forall d i o a, i < 2^64 -> o < 2^64 -> a mod 2^64 = (d + o) mod 2^64 ->
  msub 64 (d ⊕ i) a = if o <=? i then i - o else 2^64 + i - o.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma fil_empty: forall m d c, fil m m d c (fun _ => False).
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma fil_equiv:
  forall m m' d c (W W':N->Prop), (forall i, W i <-> W' i) -> fil m m' d c W -> fil m m' d c W'.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma fil_store:
  forall m m' d c (W:N->Prop) o L a v,
  fil m m' d c W -> (forall i, W i -> i < 2^64) -> 0 < L -> o + L <= 2^64 ->
  a mod 2^64 = (d + o) mod 2^64 -> bytes_are v L c ->
  fil m (setmem 64 LittleE L m' a v) d c (fun i => W i \/ o <= i < o + L).
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

(* A value whose bytes are all c keeps that property in its low part. *)
Lemma bytes_are_mod: forall v L L' c, L' <= L -> bytes_are v L c -> bytes_are (v mod 2^(8*L')) L' c.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.


Lemma memset_emag_tail_address: forall d n L,
  L <= n -> L < 2^64 ->
  (d ⊕ n + (2^64-L)) mod 2^64 = (d+(n-L)) mod 2^64.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma memset_emag_align16: forall d, d < 2^64 ->
  d .& 0xfffffffffffffff0 = d-d mod 16.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma memset_emag_tail_bit: forall r, r < 64 ->
  N.testbit (msub 64 r 64) 5 = N.testbit r 5.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

Lemma memset_emag_ret_map: forall s a,
  In a [0x19c330; 0x19c344; 0x19c358; 0x19c378; 0x19c394; 0x19c3dc] ->
  e08___memset_emag_arm8 s a = Some (4, Move R_PC (Var R_X30) $; Jmp (Var R_PC)).
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.
Theorem memset_emag_ret_correct: forall s c' s' x,
  exec_stmt arm8typctx s (Move R_PC (Var R_X30) $; Jmp (Var R_PC)) c' s' x ->
  x = Some (Addr (s R_X30)) /\ s' = update s R_PC (s R_X30).
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

(* Initial Ltac script preserved in initial-attempt.v.txt. *)

Theorem memset_emag_correct: memset_emag_contract.
Proof.
  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)
Abort.

