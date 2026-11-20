(* High-size forward overlap in the unchanged AVX memmove IL.
   Initial author: OpenAI gpt-6-astra, xhigh/default. One-shot initial proof.
   Final proof producer: pending kernel check; see notes/x09-avx-forward-high-size.
   Binary provenance inherited from x03: Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   /lib/x86_64-linux-gnu/libc.so.6, SHA256
   9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
   Ghidra 0x2a0840, image base 0x100000, normalized entry 0;
   Ghidra 11.4.2 + pcode2coq. No new binary/lifter validation.

   English spec: copy ORIGINAL source bytes to destination, frame all bytes
   outside destination, RAX=d and RSP=rsp at the cut BEFORE RET 493, and
   preserve RBX/RBP/R12-R15. ABI: 64-bit System V RDI=d, RSI=s, RDX=n.
   Domain: 2^63<=n, d<s<d+n, s+n<=2^64, n no larger than both INITIAL
   threshold quadwords 0x31a3f8 and 0x3215a8. The ordinary-loop result is
   conditioned on the EXACT NONZERO DISPATCH EXPRESSION at 357, not n<2^63.
   This is an actual branch-domain predicate, not a copy-result assumption.
   No DF/CPU-bit premise is used in this selected sequential IL path.
   No new callee contracts; use x03's original-memory unread-source invariant,
   row helper, saved head/tails, and memory frame, unchanged.

   The omitted high-size region is NOT automatically forward-loop code:
   d=4096,s=8192,n=2^63+4096 gives dispatch expression zero and selects 501.
   The numerical and encoded-branch facts below do NOT alone establish a
   final-output counterexample: a backward-path corruption/return argument
   is still required for that stronger claim. REP and NT remain x07/x10.
   Partial correctness only; no termination, executed RET, accessibility,
   hardware canonical-address, cache, fault, concurrency, or all-size claim.
 *)
Require Import Picinae_amd64 memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_overlap_forward_proof.
Import ListNotations.
Open Scope N.

Definition high_dispatch (d s n:N) :=
  (((d ⊖ s) .& 3840) + (((d ⊖ s ⊕ n) .^ (d ⊖ s)) >> 63)) mod 2^32.
Definition high_path (m d s n:N) :=
  2^63 <= n /\ d < s /\ s < d+n /\ s+n <= 2^64 /\
  n <= m Ⓠ[0x31a3f8] /\ n <= m Ⓠ[0x3215a8] /\ high_dispatch d s n <> 0.
Definition high_postcondition := ofw_postcondition.
Definition high_exit := ofw_exit.
Definition high_invs := ofw_invs.
Definition high_frame := ofw_frame.

Theorem high_welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. exact ofw_welltyped. Qed.
Theorem high_nwc: forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. reflexivity. Qed.
Theorem high_preserves_callee_saved:
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => high_frame st st').
Proof. exact ofw_preserves_callee_saved. Qed.

Lemma high_no_unsigned_backward:
  forall d s n, d<s -> s<d+n -> s+n<=2^64 -> n <= d ⊖ s.
Proof.
  intros d s n DS OV SN.
  assert (DB:d<2^64) by lia.
  assert (SB:s<2^64) by lia.
  unfold msub. rewrite (N.mod_small s) by exact SB.
  rewrite N.mod_small by (clear - DS SN; lia).
  clear - DS OV SN. lia.
Qed.

(* Exact sign classification, not an arbitrary signed-size restriction. *)
Lemma high_sign_classification:
  forall d s n, 2^63<=n -> d<s -> s<d+n -> s+n<=2^64 ->
  (((d ⊖ s ⊕ n) .^ (d ⊖ s)) >>63) =
    if d+n-s <? 2^63 then 1 else 0.
Proof.
  intros d s n HI DS OV SN.
  assert (SB:s<2^64) by lia.
  assert (SUB:d ⊖ s = 2^64+d-s).
  { unfold msub. rewrite (N.mod_small s) by exact SB.
    rewrite N.mod_small by (clear - DS SN; lia). lia. }
  assert (ADD:d ⊖ s ⊕ n = d+n-s).
  { rewrite SUB. replace (2^64+d-s+n) with (d+n-s+1*2^64) by lia.
    rewrite N.mod_add by discriminate. apply N.mod_small. lia. }
  rewrite ADD, SUB, N.shiftr_lxor.
  rewrite !shiftr63 by lia.
  assert (B: (2^64+d-s <? 2^63)=false).
  { apply N.ltb_ge. change (2^64) with 18446744073709551616 in *.
    change (2^63) with 9223372036854775808 in *. lia. }
  rewrite B. destruct (d+n-s <? 2^63); reflexivity.
Qed.

(* Satisfiable arithmetic domain refutes automatic sign-flip at high sizes. *)
Theorem high_zero_dispatch_example:
  let n := 9223372036854779904 in
  2^63 <= n /\ 4096 < 8192 /\ 8192 < 4096+n /\ 8192+n <= 2^64 /\
  n <= 4096 ⊖ 8192 /\ high_dispatch 4096 8192 n = 0 /\
  (((4096 ⊖ 8192 ⊕ n) .^ (4096 ⊖ 8192)) >>63) = 0.
Proof. vm_compute. repeat split; discriminate. Qed.

(* The actual encoded JZ destination, not a handwritten substitute program. *)
Theorem high_encoded_zero_branch:
  forall st, memmove_avx_amd64 st 357 =
    Some (6, If (Var R_ZF) (Jmp (Word 501 64)) Nop).
Proof. reflexivity. Qed.

Theorem memmove_avx_correct_forward_high_size:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (BIG: 256 < n) (DS: d < s) (OV: s < d+n) (SN: s+n <= 2^64) (HI: 2^63 <= n) (DISPATCH: high_dispatch d s n <> 0)
         (THR1: n <= m Ⓠ[0x31a3f8]) (THR2: n <= m Ⓠ[0x3215a8]),
  satisfies_all memmove_avx_amd64 (high_invs m d s n rsp) high_exit ((x',s')::t).
Proof.
  (* Uncertified one-shot attempt is preserved verbatim in unit notes. *)
Abort.

Theorem memmove_avx_forward_high_size_at_ret:
  forall st t st' m d s n rsp,
  startof t (Addr 493,st') = (Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n -> st R_RSP=rsp ->
  high_path m d s n -> exec_prog memmove_avx_amd64 ((Addr 493,st')::t) ->
  unterminated high_exit t ->
  high_postcondition m d s n rsp st' /\ high_frame st st'.
Proof.
  (* Uncertified one-shot attempt is preserved verbatim in unit notes. *)
Abort.

Definition high_witness_memory :=
  setmem 64 LittleE 8 (setmem 64 LittleE 8 0 0x31a3f8 9223372036854775808) 0x3215a8 9223372036854775808.
Definition high_witness_store : store := fun v =>
  match v with
  | V_MEM64 => high_witness_memory
  | R_RDI => 4096 | R_RSI => 4097 | R_RDX => 9223372036854775808 | R_RSP => 8192
  | _ => 0 end.

Lemma high_witness_thresholds:
  high_witness_memory Ⓠ[0x31a3f8] = 9223372036854775808 /\
  high_witness_memory Ⓠ[0x3215a8] = 9223372036854775808.
Proof.
  (* Uncertified one-shot attempt is preserved verbatim in unit notes. *)
Abort.

Theorem high_entry_satisfiable:
  exists st m,
    models x64typctx st /\ high_path m 4096 4097 9223372036854775808 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4097 /\
    st R_RDX=9223372036854775808 /\ st R_RSP=8192.
Proof.
  (* Uncertified one-shot attempt is preserved verbatim in unit notes. *)
Abort.

