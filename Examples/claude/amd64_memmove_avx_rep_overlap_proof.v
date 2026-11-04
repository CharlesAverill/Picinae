(* PARTIAL: initial full-target build failed. All nine proof attempts
   are archived verbatim in notes/x07-avx-rep-overlap/initial-attempt.v.txt.
   Statements below are retained with Abort, not exported as theorems.
   No post-failure Astra repair or second compiler run was performed. *)
(* Forward-overlapping REP MOVSB and its actual policy fallbacks.
   Unit x07-avx-rep-overlap. Initial author: OpenAI gpt-6-astra,
   reasoningEffort=xhigh, serviceTier=default (assigned settings).
   Initial one-shot attempt; final proof producer is unset pending validation.

   Provenance inherited, not independently validated here:
   /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
   __memmove_avx_unaligned_erms at Ghidra 0x2a0840, image base 0x100000,
   normalized entry 0, Ghidra 11.4.2/pcode2coq. Generated map unchanged.

   English specification: copy ORIGINAL source bytes [s,s+n) to [d,d+n),
   preserve all bytes outside destination, return d in RAX, preserve RSP
   and System V AMD64 RBX/RBP/R12-R15 at the selected pre-RET cut.
   Entry RDI=d, RSI=s, RDX=n, RSP=rsp, DF=0, typed 64-bit pointers.
   Domain: 256<n<2^63, d<s<d+n, s+n<=2^64, and n greater than the
   original-memory REP threshold at 0x31a3f8. No NOV, minimum gap, lower
   heap address, or additional size bound. No upper stop/NT threshold bound.

   Actual dispatch: 192/199 selects 704; 710/713 excludes backward copy.
   At 722/729, n < m[0x3215a0] reaches policy load 731; otherwise 800/807
   rereads the original REP threshold and reaches 813. There NEG RCX yields
   s-d, and 816/819 sends genuine forward overlap directly to 363.
   Thus NO NT store is selected anywhere in this domain. 0x3215a8 is never
   read here. For n below/equal REP but above initial NT threshold, x10
   remains separate; n>=2^63 remains x09. These are scope boundaries, not
   assertions that those overlap inputs actually execute NT stores.

   Below stop, policy bit 0 at 0x321598 clear chooses 640, then source
   alignment A iff ((d-s) mod 2^32)&0xe00=0, otherwise destination B.
   Bit set sends low32(d-s)>0xffffffc0 to 363 (including gaps 1..63);
   all other distances use B. Both policy values and every gap are allowed.
   All threshold/policy loads above precede stores, even if globals overlap
   destination. No unchanged-global claim after stores is used.

   REP invariant copies [a,a+k), frames its complement and obtains every
   next byte through ofw_load's unread ORIGINAL source rule. RCX=n-a-k,
   RSI=s+a+k, RDI=d+a+k, DF=0. RCX=0 discharges the loop and saved head
   stores at offsets 0 then 32; vector fallback loads each row before its
   four stores via ofw_store4, then stores tail n-32,n-64,n-96,n-128,head 0.
   Overlapping writes use cpy_store, not a disjoint-store assumption.

   Total-memory sequential IL partial correctness only; CPU feature checks
   and hardware page permissions are absent in this model, not extra silent
   hypotheses. No termination/executed RET/caller continuation/fault/timing/
   hardware/lifter correctness claim. Existing inherited functional
   extensionality must be disclosed by transitive Print Assumptions.
   Tactic scaffolding adapted from Claude Opus 5.5's baseline REP proof and
   the accepted x03 Astra/Sol loop proof, with no NOV-based load use.
 *)
Require Import Picinae_amd64 memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_rep_proof.
Require Import amd64_memmove_avx_overlap_forward_proof.
Import ListNotations.
Open Scope N.

Definition orp_path (m d s n:N) :=
  256 < n /\ n < 2^63 /\ d < s /\ s < d+n /\ s+n <= 2^64 /\
  m Ⓠ[0x31a3f8] < n.
Definition orp_postcondition := ofw_postcondition.
Definition orp_frame := ofw_frame.
Definition orp_exit := rp_exit.

Definition orp_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
               st R_RSP = rsp /\ st R_DF = 0)
  (* the n > __x86_rep_movsb_threshold dispatch *)
  | 704 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                 st R_RSP = rsp /\ st R_RAX = d /\ st R_DF = 0 /\ st R_YMM0 = m Ⓨ[s])
  (* forward loop head, as in amd64_memmove_avx_loops_proof.v *)
  | 416 => Some (exists k, a0 d <= k < n - 128 /\ cpy m (st V_MEM64) d s (fun i => a0 d <= i < k) /\
                 st R_RDI = d + k /\ st R_RSI = s ⊕ k /\ st R_RDX = d + n - 128 /\ st R_RCX = d /\
                 st R_RAX = d /\ st R_RSP = rsp /\
                 st R_YMM0 = m Ⓨ[s] /\ st R_YMM5 = m Ⓨ[s ⊕ (n-32)] /\
                 st R_YMM6 = m Ⓨ[s ⊕ (n-64)] /\ st R_YMM7 = m Ⓨ[s ⊕ (n-96)] /\
                 st R_YMM8 = m Ⓨ[s ⊕ (n-128)])
  (* REP MOVSB with the source aligned: k bytes copied from offset aA s *)
  | 676 => Some (exists k, k <= n - aA s /\ st R_RCX = n - aA s - k /\
                 st R_RDI = d ⊕ (aA s + k) /\ st R_RSI = s ⊕ (aA s + k) /\
                 st R_R8 = d /\ st R_RAX = d /\ st R_DF = 0 /\ st R_RSP = rsp /\
                 st R_YMM0 = m Ⓨ[s] /\ st R_YMM1 = m Ⓨ[s ⊕ 32] /\
                 cpy m (st V_MEM64) d s (fun i => aA s <= i < aA s + k))
  (* REP MOVSB with the destination aligned: k bytes copied from offset aB d *)
  | 778 => Some (exists k, k <= n - aB d /\ st R_RCX = n - aB d - k /\
                 st R_RDI = d ⊕ (aB d + k) /\ st R_RSI = s ⊕ (aB d + k) /\
                 st R_R8 = d /\ st R_RAX = d /\ st R_DF = 0 /\ st R_RSP = rsp /\
                 st R_YMM0 = m Ⓨ[s] /\ st R_YMM1 = m Ⓨ[s ⊕ 32] /\
                 cpy m (st V_MEM64) d s (fun i => aB d <= i < aB d + k))
  | 493 | 692 | 794 => Some (orp_postcondition m d s n rsp st)
  (* Stop-policy path arrives before any store, with the wrapped d-s. *)
  | 813 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\
      st R_RSP=rsp /\ st R_RAX=d /\ st R_YMM0=m Ⓨ[s] /\ st R_RCX=d ⊖ s)
  | 309 | 496 | 825 => Some False
  | _ => None
  end | _ => None end.

Theorem orp_welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. Abort.
Theorem orp_nwc: forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. Abort.
Theorem orp_preserves_callee_saved:
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => orp_frame st st').
Proof. Abort.

Lemma orp_neg_distance: forall d s, d < s -> s < 2^64 ->
  (2^64 - (d ⊖ s)) mod 2^64 = s-d.
Proof. Abort.

Ltac orp_iter a k n C DS SN NB BIG K BC A1 :=
  apply N.eqb_neq in BC;
  exists (k + 1);
  split; [clear - K BC BIG; lia|];
  split; [unfold msub; clear - K BC NB BIG; fin_mod|]; 
  split; [clear - K BC A1 NB BIG; aside|];
  split; [clear - K BC A1 NB BIG; aside|];
  repeat (split; [first [sassumption | sreflexivity |
                        match goal with H: ?r = _ |- ?r = _ =>
                          rewrite H; apply getmem_addr; rewrite ?N.mod_mod by discriminate; f_equal; clear; lia end]|]);
  match goal with |- cpy _ (setmem _ _ _ ?M ?ad (getmem _ _ 1 ?M ?b)) _ _ _ =>
    rewrite (ofw_load _ M _ _ n (a + k) _ (a + k) 1 b C) by
      (first [ exact DS | exact SN | sassumption
             | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; clear - Hi K BC BIG; lia
             | clear - K BC BIG; lia
             | clear - K BC A1 NB BIG; aside
])
  end;
  match goal with |- cpy ?m (setmem _ _ 1 ?M ?ad (getmem _ _ 1 ?m ?sa)) ?d ?s _ =>
    match type of C with cpy _ _ _ _ ?W =>
      refine (cpy_equiv m _ d s _ _ _ (cpy_store m M d s W (a + k) 1 ad sa C _ _ _ _ _))
    end
  end;
  [ let i := fresh "i" in let H := fresh "H" in
    intro i; clear - K BC BIG; cbv beta; split; intro H; [destruct H as [H|H]; lia | lia]
  | .. ];
  clear - K BC A1 NB BIG; aside.

Theorem memmove_avx_correct_rep_overlap:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (DF: st R_DF = 0)
         (DS: d < s) (OV: s < d+n) (SW: s+n <= 2^64) (NS: n < 2^63)
         (BIG: 256 < n) (THR1: m Ⓠ[0x31a3f8] < n),
  satisfies_all memmove_avx_amd64 (orp_invs m d s n rsp) orp_exit ((x',s')::t).
Proof. Abort.

Theorem memmove_avx_rep_overlap_at_ret:
  forall st t st' a m d s n rsp,
  In a [493;692;794] ->
  startof t (Addr a,st') = (Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n -> st R_RSP=rsp ->
  st R_DF=0 -> orp_path m d s n ->
  exec_prog memmove_avx_amd64 ((Addr a,st')::t) -> unterminated orp_exit t ->
  orp_postcondition m d s n rsp st' /\ orp_frame st st'.
Proof. Abort.

(* Typed entries for every gap 1..8191, both policy values, and either
   stop-threshold direction. No oracle/callee contract is introduced. *)
Definition orp_witness_memory (policy stop:N) :=
  setmem 64 LittleE 4
    (setmem 64 LittleE 8 (setmem 64 LittleE 8 0 0x31a3f8 256)
      0x3215a0 stop) 0x321598 policy.
Definition orp_witness_store (gap policy stop:N) : store := fun v =>
  match v with
  | V_MEM64 => orp_witness_memory policy stop
  | R_RDI => 4096 | R_RSI => 4096+gap | R_RDX => 8192 | R_RSP => 32768
  | _ => 0 end.
Lemma orp_witness_globals: forall policy stop,
  policy < 2^32 -> stop < 2^64 ->
  orp_witness_memory policy stop Ⓠ[0x31a3f8] = 256 /\
  orp_witness_memory policy stop Ⓠ[0x3215a0] = stop /\
  getmem 64 LittleE 4 (orp_witness_memory policy stop) 0x321598 = policy.
Proof. Abort.
Theorem orp_entry_satisfiable:
  forall gap policy stop, 0 < gap < 8192 -> policy < 2^32 -> stop < 2^64 ->
  exists st m, models x64typctx st /\ orp_path m 4096 (4096+gap) 8192 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=8192 /\ st R_RSP=32768 /\ st R_DF=0 /\
    m Ⓠ[0x3215a0]=stop /\ getmem 64 LittleE 4 m 0x321598=policy.
Proof. Abort.
Corollary orp_critical_distances:
  forall gap policy stop,
  In gap [1;31;32;63;127;4096] -> In policy [0;1] -> In stop [0;16384] ->
  exists st m, models x64typctx st /\ orp_path m 4096 (4096+gap) 8192 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=8192 /\ st R_RSP=32768 /\ st R_DF=0 /\
    m Ⓠ[0x3215a0]=stop /\ getmem 64 LittleE 4 m 0x321598=policy.
Proof. Abort.
