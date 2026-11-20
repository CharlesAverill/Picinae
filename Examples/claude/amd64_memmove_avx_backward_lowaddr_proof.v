(* AVX memmove backward overlap, the missing low-destination domain.

   Inherited provenance, not independently validated:
   Ubuntu amd64 glibc 2.35-0ubuntu3.12 /lib/x86_64-linux-gnu/libc.so.6,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
   __memmove_avx_unaligned_erms; Ghidra 0x2a0840, image base 0x100000,
   normalized entry 0; Ghidra 11.4.2 + pcode2coq amd64-fixes.
   The generated map and accepted x04 source remain unchanged.

   Initial author: OpenAI gpt-6-astra, xhigh/default, one-shot attempt.
   Final proof producer: not certified; see notes/x08-avx-backward-lowaddr.
   Based on the accepted x04 Astra statements / Sol proofs and the baseline
   Claude Opus 5.5 symbolic-execution and byte-copy helpers.

   English spec: for 256<n, 0<d<128, s<d<s+n, d+n<=2^64,
   s+n<=2^64, copy original source[0,n) to destination[0,n), with every
   byte outside destination unchanged. SysV AMD64 entry RDI=d, RSI=s,
   RDX=n, RSP=rsp; at RET 623 RAX=d and RSP=rsp. After executing RET,
   RSP=rsp+8 modulo 2^64, and the target is the final memory's stack
   quadword. No stack-disjointness premise: if destination overlaps the
   saved return address, it is the copied memory's value that is loaded.
   RBX/RBP/R12-R15 are preserved across the whole real execution.
   No alignment, high-address, minimum-gap, CPU, DF or tunable restriction.
   All geometrically possible gaps 1<=d-s<=d<128 are included.

   The modular cursor has two cases. A live suffix/unread-source case
   retains original memory and saved head/tail vectors. If c<128 and d<c,
   decrementing c wraps and preserves a residue c mod 128>d. This residue
   excludes the unsigned exit forever; the second invariant therefore
   permits arbitrary memory. It does NOT assert destination framing on
   such nonreturning prefixes. No termination, fault freedom, physical
   accessibility, ISA availability, or binary/lifter refinement is claimed.
   Permission witnesses are nonzero and include source, destination,
   threshold and return-stack bytes; no assumed callee contracts occur.
 *)

Require Import Picinae_amd64 memmove_avx_amd64.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_overlap_backward_proof.
From Stdlib Require Import NArith ZArith Lia List.
Import X64Notations ListNotations.
Open Scope N.

Definition low_domain d s n :=
  256<n /\ s<d<s+n /\ 0<d<128 /\ d+n<=2^64 /\ s+n<=2^64.

Theorem memmove_avx_backward_lowaddr_nwc:
  forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. exact memmove_avx_nwc. Qed.
Theorem memmove_avx_backward_lowaddr_welltyped:
  welltyped_prog x64typctx memmove_avx_amd64.
Proof. exact memmove_avx_welltyped. Qed.
Theorem memmove_avx_backward_lowaddr_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => st v=st' v).
Proof. exact memmove_avx_preserves_callee_saved. Qed.

Lemma low_domain_all_gaps:
  forall d gap n, 0<d<128 -> 0<gap<=d -> 256<n -> d+n<=2^64 ->
    low_domain d (d-gap) n.
Proof. intros. unfold low_domain. lia. Qed.

Lemma low_initial_memory:
  forall m d s n, cpy m m d s (fun _ => False) /\ bw_unread m m s n.
Proof. exact bw_initial_memory_satisfiable. Qed.

(* Unlike x04's rcx_c0, no lower bound on d is needed for initialization. *)
Lemma low_rcx_c0:
  forall d n, 256<n -> d+n<=2^64 ->
  (d ⊖ 129 + n) .& 18446744073709551584 = c0 d n.
Proof.
  intros d n BIG NW.
  rewrite <- (land_mod_pow2 (d ⊖ 129 + n) 64) by reflexivity.
  rewrite (addr_tail_w d 129 n) by (clear - BIG; lia).
  rewrite N.mod_small by (clear - BIG NW; lia).
  rewrite land_align32 by (clear - BIG NW; lia).
  unfold c0. replace (d+(n-129)) with (d+n-129) by (clear - BIG; lia).
  reflexivity.
Qed.

Lemma low_cursor_nowrap:
  forall c, 128<=c -> c<2^64 -> c ⊖ 128 = c-128.
Proof.
  intros c LO HI. rewrite msub_sub by lia.
  apply N.mod_small. lia.
Qed.

Lemma low_cursor_wrap:
  forall c, c<128 -> c ⊖ 128 = c+(2^64-128).
Proof.
  intros c LO. unfold msub. change (128 mod 2^64) with 128.
  apply N.mod_small. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma low_cursor_residue:
  forall c, c<2^64 -> (c ⊖ 128) mod 128 = c mod 128.
Proof.
  intros c HI. destruct (N.le_gt_cases 128 c) as [LO|LO].
  - rewrite low_cursor_nowrap by assumption.
    replace c with ((c-128)+1*128) at 2 by lia.
    rewrite N.mod_add by discriminate. reflexivity.
  - rewrite low_cursor_wrap by assumption.
    replace (2^64-128) with (144115188075855871*128) by reflexivity.
    rewrite N.mod_add by discriminate. reflexivity.
Qed.

Lemma low_wrapped_no_exit:
  forall d c, c<2^64 -> d<c mod 128 -> d<c ⊖ 128.
Proof.
  intros d c HI R.
  pose proof (N.mod_le (c ⊖ 128) 128 ltac:(discriminate)) as LE.
  rewrite low_cursor_residue in LE by exact HI. lia.
Qed.

Definition low_postcondition := bw_postcondition.
Definition low_exit := bw_exit.
Definition low_live m d s n rsp (st:store) :=
  exists c, d<c /\ c+128<=d+n /\ c<=c0 d n /\
    cpy m (st V_MEM64) d s (fun i => c-d+128<=i<c0 d n-d+128) /\
    st R_RCX=c /\ st R_RSI=s ⊕ (c-d) /\ st R_RDI=d /\ st R_RDX=n /\
    st R_RAX=d /\ st R_RSP=rsp /\
    st R_YMM0=m Ⓨ[s] /\ st R_YMM5=m Ⓨ[s ⊕ 32] /\
    st R_YMM6=m Ⓨ[s ⊕ 64] /\ st R_YMM7=m Ⓨ[s ⊕ 96] /\
    st R_YMM8=m Ⓨ[s ⊕ (n-32)].
Definition low_wrapped d (st:store) :=
  exists c, c<2^64 /\ d<c mod 128 /\ st R_RCX=c /\ st R_RDI=d.
Definition low_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\
               st R_RDX=n /\ st R_RSP=rsp)
  | 309 | 704 => Some (bw_dispatch m d s n rsp st)
  | 496 => Some (bw_dispatch m d s n rsp st /\ st R_RCX=d-s)
  | 544 => Some (low_live m d s n rsp st \/ low_wrapped d st)
  | 623 => Some (low_postcondition m d s n rsp st)
  | 27 | 48 | 214 | 324 | 490 | 719 => Some False
  | _ => None end | _ => None end.

Lemma low_live_unread:
  forall m d s n rsp st,
  low_domain d s n -> low_live m d s n rsp st ->
  exists c, st R_RCX=c /\ bw_unread m (st V_MEM64) s (c-d+128).
Proof.
  intros m d s n rsp st [BIG [OV [DLO [NW SW]]]]
    [c [C1 [C2 [C3 [C [RCX REST]]]]]].
  exists c. split; [exact RCX|].
  pose proof (c0_bounds d n ltac:(clear - BIG; lia)) as CB.
  eapply (bw_suffix_unread m (st V_MEM64) d s n (c-d+128)); [exact C|..].
  - intros i I. clear - I CB BIG. lia.
  - clear - OV. lia.
  - exact NW.
  - clear - C1 C2. lia.
Qed.

Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true | _ => false end).

Theorem memmove_avx_correct_backward_lowaddr:
  forall st t st' x' m d s n rsp
    (ENTRY: startof t (x',st') = (Addr 0,st))
    (MDL: models x64typctx st)
    (MEM: st V_MEM64=m) (D: st R_RDI=d) (S: st R_RSI=s)
    (Nn: st R_RDX=n) (RSP: st R_RSP=rsp)
    (DOM: low_domain d s n),
  satisfies_all memmove_avx_amd64 (low_invs m d s n rsp) low_exit ((x',st')::t).
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

(* A concrete exec_prog trace ending at the actual RET instruction. *)
Corollary memmove_avx_backward_lowaddr_at_ret:
  forall st t st' m d s n rsp,
  startof t (Addr 623,st')=(Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n ->
  st R_RSP=rsp -> low_domain d s n ->
  exec_prog memmove_avx_amd64 ((Addr 623,st')::t) ->
  unterminated low_exit t ->
  low_postcondition m d s n rsp st' /\
  (forall v, In v [R_RBX;R_RBP;R_R12;R_R13;R_R14;R_R15] -> st v=st' v).
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

(* RET is actually executed; its stack load observes the final copy memory. *)
Lemma low_ret_step:
  forall st st' x,
  can_step memmove_avx_amd64 ((x,st'),(Addr 623,st)) ->
  x=Addr (st V_MEM64 Ⓠ[st R_RSP]) /\
  st' R_RSP=st R_RSP ⊕ 8 /\ st' V_MEM64=st V_MEM64 /\
  st' R_RAX=st R_RAX.
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

Theorem memmove_avx_backward_lowaddr_after_ret:
  forall st t retst out x m d s n rsp,
  startof t (Addr 623,retst)=(Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n ->
  st R_RSP=rsp -> low_domain d s n ->
  exec_prog memmove_avx_amd64 ((x,out)::(Addr 623,retst)::t) ->
  unterminated low_exit t ->
  out R_RAX=d /\ out R_RSP=rsp ⊕ 8 /\ copied m (out V_MEM64) d s n /\
  x=Addr (out V_MEM64 Ⓠ[rsp]) /\
  (forall v, In v [R_RBX;R_RBP;R_R12;R_R13;R_R14;R_R15] -> st v=out v).
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

(* Finite permissions, not the zero-permission witness used by x04. *)
Definition low_witness_store (d s:N) : store := fun v => match v with
  | R_RDI => d | R_RSI => s | R_RDX => 257 | R_RSP => 4096
  | A_READ | A_WRITE => N.ones 4194304 | _ => 0 end.

Lemma low_witness_typed:
  forall d s, s<d -> 0<d<128 -> models x64typctx (low_witness_store d s).
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

Lemma low_witness_permissions:
  forall d s a L, a+L<=4194304 ->
    MemAcc mem_readable (low_witness_store d s) a 64 L /\
    MemAcc mem_writable (low_witness_store d s) a 64 L.
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

Theorem low_accessible_entry_witness:
  forall d gap, 0<d<128 -> 0<gap<=d -> exists st,
  models x64typctx st /\ st V_MEM64=0 /\ st R_RDI=d /\
  st R_RSI=d-gap /\ st R_RDX=257 /\ st R_RSP=4096 /\
  low_domain d (d-gap) 257 /\
  MemAcc mem_readable st (d-gap) 64 257 /\
  MemAcc mem_writable st d 64 257 /\
  MemAcc mem_readable st 0x31a3f8 64 8 /\
  MemAcc mem_readable st 4096 64 8 /\
  exists st1, can_step memmove_avx_amd64 ((Addr 4,st1),(Addr 0,st)).
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.

(* Both live and wrap-prone cursor classes have actual typed permitted stores.
   This is entry/permission nonvacuity, not a promise of a complete execution. *)
Lemma low_cursor_examples:
  low_domain 1 0 257 /\ c0 1 257=128 /\
  low_domain 1 0 289 /\ c0 1 289=160 /\
  (32 ⊖ 128) mod 128=32.
Proof.
  (* Uncertified initial script is preserved in notes/x08-avx-backward-lowaddr/initial-attempt.v.txt. *)
Abort.
