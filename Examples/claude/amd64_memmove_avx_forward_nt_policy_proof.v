(* Forward overlap above the starting NT-policy threshold.
   Initial author: OpenAI gpt-6-astra, xhigh/default.
   Status: PARTIAL; validation stopped on Charles's wrap-up order.
   Final proof producer: none; unvalidated repair bodies archived separately.
   Binary: /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
   __memmove_avx_unaligned_erms: Ghidra 0x2a0840, image base 0x100000.
   Inherited Ghidra 11.4.2/pcode2coq provenance, not revalidated here.
   Generated memmove_avx_amd64.v remains unchanged.

   English specification: memmove(d,s,n) copies the ORIGINAL source bytes
   to destination and returns d, preserving all bytes outside destination.
   System V AMD64 entry: RDI=d, RSI=s, RDX=n, RSP=rsp, V_MEM64=m.
   At the cut before RET 493: RAX=d, RSP=rsp, original-memory copy and
   outside frame; RBX/RBP/R12-R15 retain their initial values.

   Exact domain: 256<n<2^63, d<s<d+n, s+n<=2^64 (so d+n<2^64),
   n<=m[0x31a3f8] and m[0x3215a8]<n, both little-endian quadwords.
   Equality with the starting REP threshold is included. All positive gaps
   below n are allowed. No d lower bound, gap heuristic, additional tunable,
   CPU-bit or DF assumption. No threshold separation from either data region
   is required: both actual reads precede any destination writes.

   Dispatch 309/324/331 selects 813. NEG makes RCX=s-d; CMP/JA 816/819
   therefore goes to 363, before any NT store. The other branch at 825 is
   impossible for genuine forward overlap. This proves the actual fallback,
   not the nonoverlap NT theorem from x02. Entry REP selection is excluded
   only by the assigned domain; n>REP belongs to x07.

   The saved original head/tail and unread-source row reasoning reuse x03
   helpers. The ordinary-loop proof below is adapted from the accepted x03
   Astra/Sol proof (and its attributed Claude Opus 5.5 arithmetic scaffolding).
   No assumed helper/callee contracts are introduced.

   Sequential IL partial correctness only: no termination, execution of RET,
   caller continuation, hardware availability/fault/cache/timing/concurrency
   claim or binary/lifter refinement. Inherited functional extensionality is
   subject to the transitive Print Assumptions audit.
 *)
Require Import Picinae_amd64 memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_overlap_forward_proof.
Import ListNotations.
Open Scope N.

Definition ofnt_path (m d s n:N) :=
  256 < n /\ n < 2^63 /\ d < s /\ s < d+n /\ s+n <= 2^64 /\
  n <= m Ⓠ[0x31a3f8] /\ m Ⓠ[0x3215a8] < n.

Definition ofnt_postcondition (m d s n rsp:N) (st:store) :=
  st R_RAX = d /\ st R_RSP = rsp /\ copied m (st V_MEM64) d s n.
Definition ofnt_frame (st st':store) :=
  forall v, In v [R_RBX;R_RBP;R_R12;R_R13;R_R14;R_R15] -> st' v = st v.
Definition ofnt_exit (t:trace) :=
  match t with (Addr 493,_)::_ => true | _ => false end.
Definition ofnt_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\ st R_RSP=rsp)
  | 309 | 363 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\
                 st R_RSP=rsp /\ st R_RAX=d /\ st R_YMM0=m Ⓨ[s])
  | 416 => Some (exists k, a0 d <= k < n-128 /\
      cpy m (st V_MEM64) d s (fun i => a0 d <= i < k) /\
      st R_RDI=d+k /\ st R_RSI=s ⊕ k /\ st R_RDX=d+n-128 /\ st R_RCX=d /\
      st R_RAX=d /\ st R_RSP=rsp /\ st R_YMM0=m Ⓨ[s] /\
      st R_YMM5=m Ⓨ[s ⊕ (n-32)] /\ st R_YMM6=m Ⓨ[s ⊕ (n-64)] /\
      st R_YMM7=m Ⓨ[s ⊕ (n-96)] /\ st R_YMM8=m Ⓨ[s ⊕ (n-128)])
  | 813 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\
      st R_RSP=rsp /\ st R_RAX=d /\ st R_YMM0=m Ⓨ[s] /\ st R_RCX=d ⊖ s)
  | 493 => Some (ofnt_postcondition m d s n rsp st)
  | 337 | 496 | 501 | 704 | 825 => Some False
  | _ => None end | _ => None end.

Theorem ofnt_welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. exact memmove_avx_welltyped. Qed.
Theorem ofnt_nwc: forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. reflexivity. Qed.
Theorem ofnt_preserves_callee_saved:
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => ofnt_frame st st').
Proof.
  intros t x st x' st' XP ENTRY v IN. symmetry.
  exact (memmove_avx_preserves_callee_saved v IN t x st x' st' XP ENTRY).
Qed.

Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true | _ => false end).

Lemma ofnt_reverse_gap:
  forall d s, d < s -> s < 2^64 -> s ⊖ d = s-d.
Proof.
  intros d s DS SB. rewrite msub_sub by lia. apply N.mod_small. lia.
Qed.

Lemma ofnt_negative_gap:
  forall d s, d < s -> s < 2^64 -> msub 64 0 (d ⊖ s) = s-d.
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.

Theorem memmove_avx_correct_forward_nt_policy:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (BIG: 256 < n) (DS: d < s) (OV: s < d+n) (SN: s+n <= 2^64) (NS: n < 2^63)
         (THR1: n <= m Ⓠ[0x31a3f8]) (THR2: m Ⓠ[0x3215a8] < n),
  satisfies_all memmove_avx_amd64 (ofnt_invs m d s n rsp) ofnt_exit ((x',s')::t).
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.

Theorem memmove_avx_forward_nt_policy_at_ret:
  forall st t st' m d s n rsp,
  startof t (Addr 493,st') = (Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n -> st R_RSP=rsp ->
  ofnt_path m d s n -> exec_prog memmove_avx_amd64 ((Addr 493,st')::t) ->
  unterminated ofnt_exit t ->
  ofnt_postcondition m d s n rsp st' /\ ofnt_frame st st'.
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.

(* Nonvacuity: a typed entry for EVERY positive distance below 512, including
   1,31,32,127. This constructs entry memory/ABI values, not an execution or
   a termination witness. Thresholds are concrete writable global values. *)
Definition ofnt_witness_memory :=
  setmem 64 LittleE 8 (setmem 64 LittleE 8 0 0x31a3f8 512) 0x3215a8 511.
Definition ofnt_witness_store (gap:N) : store := fun v =>
  match v with
  | V_MEM64 => ofnt_witness_memory
  | R_RDI => 4096 | R_RSI => 4096+gap | R_RDX => 512 | R_RSP => 8192
  | _ => 0 end.

Lemma ofnt_witness_thresholds:
  ofnt_witness_memory Ⓠ[0x31a3f8] = 512 /\
  ofnt_witness_memory Ⓠ[0x3215a8] = 511.
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.

Theorem ofnt_entry_satisfiable:
  forall gap, 0 < gap < 512 -> exists st m,
    models x64typctx st /\ ofnt_path m 4096 (4096+gap) 512 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=512 /\ st R_RSP=8192.
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.

Corollary ofnt_critical_distances:
  forall gap, In gap [1;31;32;127] -> exists st m,
    models x64typctx st /\ ofnt_path m 4096 (4096+gap) 512 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=512 /\ st R_RSP=8192.
Proof.
  (* WIP: repair archived in notes/x10-avx-forward-nt-policy-fix/stopped-repair.v.txt;
     validation stopped on Charles's order before the full target completed. *)
Abort.
