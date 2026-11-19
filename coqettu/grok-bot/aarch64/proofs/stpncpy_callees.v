(* stpncpy callee lemmas and shared definitions: stp_prog = stpncpy + memset lifts, frame/precondition/postcondition definitions, the shared invariant family (stpncpy id 1, memset id 0) and memset_correct_in_stpncpy -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Part of the stpncpy proof (0x15e9c0 in Ghidra, 0x5e9c0 ELF vaddr), split
   into a definitions/callee file, a VC file and a main file (see
   ../../VCEffectsOnMemOverhead.md).  Full header (SEMANTICS, manual
   SPECIFICATION, PROVENANCE, I/O specification) is in stpncpy_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require stpncpy_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokBits GrokStep GrokStr GrokFrame GrokFill GrokMem.
From Grok.proofs Require Import memset_proof memset_full_defs memset_full_proof.
Import ARM8Notations.
Open Scope N.

Definition stp_prog : program := updateall2 stpncpy_armv8.stpncpy_armv8 memset_armv8.memset_armv8.

Theorem stp_prog_welltyped: welltyped_prog arm8typctx stp_prog.
Proof.
  intros s a. unfold stp_prog, updateall2, updateall.
  destruct (memset_armv8.memset_armv8 s a) as [[sz q]|] eqn:T0.
    pose proof (memset_proof.memset_welltyped s a) as WT. rewrite T0 in WT. exact WT.
    apply stpncpy_armv8.welltyped.
Qed.

Lemma stp_prog_mono: ∀ prog, stpncpy_armv8.stpncpy_armv8 ⊆2 prog -> memset_armv8.memset_armv8 ⊆2 prog -> stp_prog ⊆2 prog.
Proof.
  intros prog P1 P0. unfold stp_prog.
  rewrite <- (updateall2_subset _ _ P0). apply updateall2_mono. exact P1.
Qed.

(* the caller's memory after the prologue (stp x29,x30,[sp,#-32]!; str x19,[sp,#16]) *)
Definition stp_frame (sp mem raddr x19 x29 : N) :=
  mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 16 := x19].

(* K = number of non-NUL bytes copied = strnlen(q, n) *)
Definition stp_pre (sp mem d q n K : N) :=
  nilfree mem q K /\ K <= n /\ (K < n -> mem Ⓑ[q + K] = 0) /\ n - K < 160 /\ 4096 <= d /\
  32 <= sp /\ sp < 2^64 /\ d + n + 32 <= sp /\ q + n + 32 <= sp /\ (q + n <= d \/ d + n <= q).

Definition stp_post (sp mem raddr d q n x19 x29 K : N) (s:store) :=
  s R_X0 = d + K /\ s R_SP = sp /\ s R_X19 = x19 /\ s R_X29 = x29 /\ s R_X30 = raddr /\
  (∀ i, i < K -> s V_MEM64 Ⓑ[d + i] = mem Ⓑ[q + i]) /\
  (∀ i, K <= i -> i < n -> s V_MEM64 Ⓑ[d + i] = 0) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = stp_frame sp mem raddr x19 x29 Ⓑ[a]).

Section Invariants.
  Variables (sp mem raddr d q n x19 x29 K mm md cc mn : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e9c0 => Inv 1 (s R_X0 = d /\ s R_X1 = q /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X29 = x29)
    | 0x15e9ec => Inv 1 (∃ k, k <= K /\ msub 64 q d mod 8 = 0 /\ s R_X0 = d + k /\ s R_X1 = q + k /\ s R_X2 = n - k /\
                         s V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat k) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ea0c => Inv 1 (∃ k j, k <= K /\ k < n /\ (j = k \/ (j = k + 1 /\ k = K)) /\ msub 64 q d mod 8 = 0 /\
                         s R_X0 = d + k /\ s R_X1 = q + k /\ s R_X2 = n - k /\
                         s V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat j) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ea38 => Inv 1 (∃ k m, k <= K /\ k <= m /\ m <= n /\ (m - k) mod 8 = 0 /\ msub 64 q d mod 8 = 0 /\
                         s R_X0 = d + k /\ s R_X1 = q + k /\ s R_X5 = q + m /\ s R_X6 = q + n /\ s R_X7 = 0xfefefefefefefeff /\
                         s V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat k) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ea64 => Inv 1 (∃ k, k <= K /\ s R_X19 = d + k /\ s R_X1 = q + k /\ s R_X2 = n - k /\
                         s V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat k) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ea78 => Inv 1 (∃ j, (j = K \/ (j = K + 1 /\ K < n)) /\ s R_X19 = d + K /\ s R_X2 = n - K /\
                         s V_MEM64 = bcp (stp_frame sp mem raddr x19 x29) d q (N.to_nat j) /\ s R_SP = sp ⊖ 32 /\ s R_X29 = sp ⊖ 32)
    | 0x15ea90 => Post 1 (stp_post sp mem raddr d q n x19 x29 K s)
    (* memset(md, cc, mn) on memory mm (at the call: md = d + K, cc = 0, mn = n - K), carrying x19 = md *)
    | _ => memset_full_defs.mf_invs mm md cc mn (sp ⊖ 32) 0x15ea84 T
             (fun i P => Inv i (P /\ s R_X19 = md)) (fun i P => Post i (P /\ s R_X19 = md)) NoInv s a
    end.
  Definition exits0 := make_exits 0 stp_prog invs.
  Definition invs0 := make_invs 0 stp_prog invs.
  Definition exits1 := make_exits 1 stp_prog invs.
  Definition invs1 := make_invs 1 stp_prog invs.
End Invariants.

Theorem memset_correct_in_stpncpy:
  ∀ prog s t xs'
    (P: stp_prog ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    sp mem raddr d q n x19 x29 K
    (SP: s R_SP = sp ⊖ 32) (X30: s R_X30 = 0x15ea84) (X19: s R_X19 = s R_X0)
    (SIDE: mf_side (s R_X1) (s R_X2)) (LOW: 4096 <= s R_X0) (NW: s R_X0 + s R_X2 < 2^64),
  satisfies_all prog (invs0 sp mem raddr d q n x19 x29 K (s V_MEM64) (s R_X0) (s R_X1) (s R_X2))
                     (exits0 sp mem raddr d q n x19 x29 K (s V_MEM64) (s R_X0) (s R_X1) (s R_X2)) (xs'::t).
Proof.
  intros.
  set (mm := s V_MEM64). assert (MEM: s V_MEM64 = mm) by reflexivity. set (c := s R_X1). assert (X1: s R_X1 = c) by reflexivity.
  set (md := s R_X0) in *. assert (X0: s R_X0 = md) by reflexivity. set (mn := s R_X2) in *. assert (X2: s R_X2 = mn) by reflexivity.
  clearbody mm c md mn.
  eapply satisfies_all_pmono with (p1:=stp_prog). exact P.
    intros a s1 t1 EXIT NOCODE. unfold invs0, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    try rewrite X1 in SIDE.
    clear - MDL X0 X1 X2 MEM SP X30 X19 SIDE LOW NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply stp_prog_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  all: unfold mf_loop, mfb, fbase in *; repeat match goal with H: _ /\ _ |- _ => destruct H end.
  all: try match goal with H: False |- _ => destruct H end.
  1: (arm8_step; splits; try reflexivity; try assumption; match goal with |- context[?s R_Z0] => solve_splat c (s R_Z0) end).
  (* 0x118404 *)
  (* old small-path cases 0x118404 .. 0x118470 *)
  2-6: (repeat grok_step; memset_prep;
    try (unfold memset_post); unfold mfb, fbase; try simpl_stores; splits; try reflexivity; try assumption; try lia;
    try (intros i I; memset_addr; repeat rd1; first [match goal with ZS: splat_bytes _ _ _ |- _ => memset_byte ZS end | lia | reflexivity]);
    try (intros x A O; memset_addr; repeat rd1; first [reflexivity | lia]);
    try (intros; match goal with H: _ V_MEM64 = _ |- _ => rewrite H end; reflexivity)).
  (* 0x118404 *)
  1: (repeat grok_step; memset_prep; unfold mfb, fbase; try simpl_stores; splits; try reflexivity; try assumption; memset_addr; try lia).
  (* 0x118480 *)
  1: { repeat grok_step. all: memset_prep.
       all: try (exfalso; unfold mf_side in *; lia).
       all: rewrite !land_m16 by lia.
       all: assert (DM: md mod 16 < 16) by (apply N.mod_lt; discriminate).
       all: assert (DL: md mod 16 <= md) by (apply N.Div0.mod_le).
       all: try unfold memset_post; unfold mf_loop, fbase; try simpl_stores; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: first
         [ intros i I1 I2; rd1; [ mf_byte | exfalso; lia | exfalso; lia ]
         | intros x A O; rd1; [ exfalso; lia | reflexivity | reflexivity ] ]. }
  (* 0x1184e8 *)
  1: { repeat grok_step. all: memset_prep.
       all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
       all: try unfold memset_post; unfold mf_loop, fbase; try simpl_stores; splits; try reflexivity; try assumption; memset_addr; try lia.
       all: match goal with
         | |- ∀ i, i < _ -> _ => intros i I; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ i, _ <= i -> _ => intros i I1 I2; repeat rd2; first [ mf_byte | mf_ih ]
         | |- ∀ a, a < _ -> _ => intros x A O; repeat rd2; first [ exfalso; lia | mf_out ]
         end. }
Qed.
