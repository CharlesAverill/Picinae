(* memcpy, the loop paths (128 < n <= the non-temporal threshold)

   This file continues amd64_memcpy_proof.v (see its header for the
   function, the man page text and the provenance).  For 128 < n,
   glibc's SSE2 memcpy (memcpy@GLIBC_2.2.5 entry) loads the first 16 and
   last 64 source bytes into XMM registers, then copies 64 bytes per
   iteration with aligned stores, forward or backward depending on a
   4 KiB-aliasing test, and finally stores the saved head and tail.  For n
   above __x86_shared_non_temporal_threshold it takes a non-temporal path
   instead; that path is outside this theorem (its entry is a False cut,
   refuted by the precondition n <= threshold).

   PRECONDITIONS (beyond n > 128)
   * nov d s n: the areas [d, d+n) and [s, s+n) do not overlap (the man
     page's requirement).
   * d + n <= 2^64: the destination does not wrap around the address space
     (the loops compare raw pointers).
   * n <= m[0x3215a8] (the threshold global, read before any store).
   * 64 <= d: the backward loop (taken when d and s alias modulo 4 KiB)
     steps its store pointer c down by 64 and exits on c - 64 <= d; for
     d < 64 the subtraction can wrap around zero.  No real buffer starts in
     the first 64 bytes of the address space (page 0 is never mapped).

   OUTPUT: at the RET, RAX = d, RSP is unchanged, and copied m m' d s n
   (dest[0,n) = src[0,n), all other bytes unchanged).

   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.
 *)

Require Import Picinae_amd64.
Require Import memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Require Import amd64_memcpy_proof.
Open Scope N.

(* The lifter splits a 16-byte load from memory that was just stored to into
   4-, 8-, 12- and 16-byte pieces; they reassemble to the 16-byte load. *)
Lemma pack16:
  forall (M:memory) a,
  M Ⓧ[a] >> 96 << 96 .| (getmem 64 LittleE 12 M a >> 64 << 64 .| (M Ⓠ[a] >> 32 << 32 .| M Ⓓ[a])) = M Ⓧ[a].
Proof.
  intros M a.
  replace (getmem 64 LittleE 12 M a) with (M Ⓧ[a] mod 2^(12*8)) by (rewrite getmem_mod; reflexivity).
  replace (M Ⓠ[a]) with (M Ⓧ[a] mod 2^(8*8)) by (rewrite getmem_mod; reflexivity).
  replace (M Ⓓ[a]) with (M Ⓧ[a] mod 2^(4*8)) by (rewrite getmem_mod; reflexivity).
  generalize (M Ⓧ[a]). intro X. apply N.bits_inj. intro i.
  rewrite !N.lor_spec.
  destruct (N.ltb_spec i 32) as [I1|I1];
  [| destruct (N.ltb_spec i 64) as [I2|I2];
     [| destruct (N.ltb_spec i 96) as [I3|I3]]].
  - rewrite !N.shiftl_spec_low by lia. rewrite N.mod_pow2_bits_low by (cbn; lia). reflexivity.
  - rewrite !N.shiftl_spec_low by lia. rewrite (N.mod_pow2_bits_high X (4*8)) by (cbn; lia).
    rewrite N.shiftl_spec_high, N.shiftr_spec by lia. replace (i - 32 + 32) with i by lia.
    rewrite N.mod_pow2_bits_low by (cbn; lia). rewrite !Bool.orb_false_r. reflexivity.
  - rewrite N.shiftl_spec_low by lia. rewrite (N.shiftl_spec_high _ 64) by lia.
    rewrite N.shiftr_spec by lia. replace (i - 64 + 64) with i by lia.
    rewrite (N.mod_pow2_bits_low X (12*8)) by (cbn; lia).
    rewrite (N.shiftl_spec_high _ 32) by lia. rewrite N.shiftr_spec by lia. replace (i - 32 + 32) with i by lia.
    rewrite (N.mod_pow2_bits_high X (8*8)) by (cbn; lia). rewrite (N.mod_pow2_bits_high X (4*8)) by (cbn; lia).
    rewrite !Bool.orb_false_r. reflexivity.
  - rewrite (N.shiftl_spec_high _ 96) by lia. rewrite N.shiftr_spec by lia. replace (i - 96 + 96) with i by lia.
    rewrite (N.shiftl_spec_high _ 64) by lia. rewrite N.shiftr_spec by lia. replace (i - 64 + 64) with i by lia.
    rewrite (N.shiftl_spec_high _ 32) by lia. rewrite N.shiftr_spec by lia. replace (i - 32 + 32) with i by lia.
    rewrite (N.mod_pow2_bits_high X (12*8)) by (cbn; lia). rewrite (N.mod_pow2_bits_high X (8*8)) by (cbn; lia).
    rewrite (N.mod_pow2_bits_high X (4*8)) by (cbn; lia).
    rewrite !Bool.orb_false_r. reflexivity.
Qed.

(* Four 16-byte stores of source pieces read from the current memory M:
   when the buffers don't overlap, each piece is the original source. *)
Lemma cpy_store4:
  forall m M d s n (W:N->Prop) o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4,
  cpy m M d s W -> (forall i, W i -> i < n) -> nov d s n -> n < 2^64 ->
  o1 + 16 <= n -> o2 + 16 <= n -> o3 + 16 <= n -> o4 + 16 <= n ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 ->
  a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 ->
  b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 ->
  cpy m (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 M
          a1 (M Ⓧ[b1])) a2 (M Ⓧ[b2])) a3 (M Ⓧ[b3])) a4 (M Ⓧ[b4])) d s
      (fun i => W i \/ o1 <= i < o1 + 16 \/ o2 <= i < o2 + 16 \/ o3 <= i < o3 + 16 \/ o4 <= i < o4 + 16).
Proof.
  intros m M d s n W o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4 C WN NOV NB O1 O2 O3 O4 A1 A2 A3 A4 B1 B2 B3 B4.
  rewrite (cpy_load m M d s W n o1 16 b1 C WN NOV O1 B1).
  rewrite (cpy_load m M d s W n o2 16 b2 C WN NOV O2 B2).
  rewrite (cpy_load m M d s W n o3 16 b3 C WN NOV O3 B3).
  rewrite (cpy_load m M d s W n o4 16 b4 C WN NOV O4 B4).
  assert (C4: cpy m (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 (setmem 64 LittleE 16 M
          a1 (getmem 64 LittleE 16 m b1)) a2 (getmem 64 LittleE 16 m b2)) a3 (getmem 64 LittleE 16 m b3))
          a4 (getmem 64 LittleE 16 m b4)) d s
      (fun i => (((W i \/ o1 <= i < o1 + 16) \/ o2 <= i < o2 + 16) \/ o3 <= i < o3 + 16) \/ o4 <= i < o4 + 16)).
  { apply cpy_store; [apply cpy_store; [apply cpy_store; [apply cpy_store; [exact C|..]|..]|..]|..].
    all: try assumption.
    all: try (intros i Hi; clear - Hi WN NB O1 O2 O3 O4; change (2^64) with 18446744073709551616 in *;
              repeat destruct Hi as [Hi|Hi]; try apply WN in Hi; lia).
    all: try (clear; lia).
    all: clear - NB O1 O2 O3 O4; change (2^64) with 18446744073709551616 in *; lia. }
  eapply cpy_equiv; [|exact C4]. intro i. tauto.
Qed.

(* Offset of the first aligned store of the forward loop, and the first
   (highest) aligned store address of the backward loop. *)
Definition a0 (d:N) := 16 - d mod 16.
Definition c0 (d n:N) := (d + n - 65) - (d + n - 65) mod 16.

Definition xmm_ok (st:store) (r:var) (m:memory) (a:N) := st r mod 2^128 = m Ⓧ[a].

Definition loops_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 | 1854063 | 1854222 | 1854336 => true
  | _ => false
  end | _ => false end.

Definition loops_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1853552 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                     st R_RSP = rsp)
  (* 0x1c4a70: the n > 128 dispatch *)
  | 1854064 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                     st R_RSP = rsp /\ st R_RAX = d /\ xmm_ok st R_YMM0 m s)
  (* forward loop head: [a0, k) copied *)
  | 1854160 => Some (exists k, a0 d <= k < n - 64 /\ cpy m (st V_MEM64) d s (fun i => a0 d <= i < k) /\
                     st R_RDI = d + k /\ st R_RSI = s ⊕ k /\ st R_RDX = d + n - 64 /\ st R_RCX = d /\
                     st R_RAX = d /\ st R_RSP = rsp /\
                     xmm_ok st R_YMM0 m s /\ xmm_ok st R_YMM5 m (s ⊕ (n-16)) /\
                     xmm_ok st R_YMM6 m (s ⊕ (n-32)) /\ xmm_ok st R_YMM7 m (s ⊕ (n-48)) /\
                     xmm_ok st R_YMM8 m (s ⊕ (n-64)))
  (* backward loop head: c is the next (aligned) store address, [c-d+64, top) copied *)
  | 1854272 => Some (exists c, d < c /\ c + 64 <= d + n /\ c <= c0 d n /\
                     cpy m (st V_MEM64) d s (fun i => c - d + 64 <= i < c0 d n - d + 64) /\
                     st R_RCX = c /\ st R_RSI = s ⊕ (c - d) /\ st R_RDI = d /\ st R_RDX = n /\
                     st R_RAX = d /\ st R_RSP = rsp /\
                     xmm_ok st R_YMM0 m s /\ xmm_ok st R_YMM5 m (s ⊕ 16) /\
                     xmm_ok st R_YMM6 m (s ⊕ 32) /\ xmm_ok st R_YMM7 m (s ⊕ 48) /\
                     xmm_ok st R_YMM8 m (s ⊕ (n-16)))
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 | 1854063 | 1854222 | 1854336 =>
      Some (postcondition m d s n rsp st)
  (* the non-temporal path: n > threshold *)
  | 1854381 => Some False
  | _ => None
  end | _ => None end.


(* Step one instruction, then drop the path if its branch conditions are
   contradictory.  Pruning early keeps the symbolic state small. *)
Ltac bc_norm :=
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  end;
  repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                       | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
  repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                       | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.
Ltac step_prune := x64_step; try (bc_norm; first [discriminate | exfalso; lia]).

(* These paths branch only on CF and ZF, so abstract away the other flags;
   their full expressions (PF includes a popcount) would otherwise be carried
   through every step. *)
Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true
| _ => false end).

(* lia on just the arithmetic: drop memory, store and copy facts first. *)
Ltac alia :=
  repeat match goal with
  | H: cpy _ _ _ _ _ |- _ => clear H | H: xmm_ok _ _ _ _ |- _ => clear H
  | H: MemAcc _ _ _ _ _ |- _ => clear H | H: models _ _ |- _ => clear H
  | H: nov _ _ _ |- _ => clear H | H: _ = _ :> store |- _ => clear H
  | H: _ R_RSP = _ |- _ => clear H | H: _ R_RAX = _ |- _ => clear H | H: _ R_RCX = _ |- _ => clear H
  | H: _ R_RDX = _ |- _ => clear H | H: _ R_RSI = _ |- _ => clear H | H: _ R_RDI = _ |- _ => clear H
  end; lia.

(* The JA (CF=0 and ZF=0) branch condition as lifted. *)
Lemma ja_not_taken: forall a b:bool,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = 0 -> a = true \/ b = true.
Proof. intros [|] [|]; cbn; intro H; first [discriminate | tauto]. Qed.

Lemma ja_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = N.pos p -> a = false /\ b = false.
Proof. intros [|] [|] p; cbn; intro H; first [discriminate | tauto]. Qed.

(* An arithmetic side condition, in a context already cleared down to the
   arithmetic facts (lia is hopeless next to the symbolic memory terms). *)
Ltac aside :=
  lazymatch goal with
  | |- 0 < 16 => reflexivity
  | |- forall i, _ -> _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; cbv beta in Hi; repeat destruct Hi as [Hi|Hi];
      change (2^64) with 18446744073709551616 in *; lia
  | |- (?x mod 2^64) mod 2^64 = ?x mod 2^64 => apply N.mod_mod; discriminate
  | |- _ mod 2^64 = _ mod 2^64 => f_equal; change (2^64) with 18446744073709551616 in *; lia
  | |- _ => change (2^64) with 18446744073709551616 in *; lia
  end.

(* A loop-carried XMM fact: the register is unchanged, only the address
   expression differs (s ⊕ x vs s + x, or operand order). *)
Ltac xmm_tac :=
  lazymatch goal with |- ?a mod 2^128 = _ =>
    match goal with H: a mod 2^128 = _ |- _ => rewrite H end end;
  rewrite ?getmem_mod_l; try (f_equal; clear; lia).

Lemma c0_bounds: forall d n, 80 <= d + n -> d + n - 80 <= c0 d n <= d + n - 65.
Proof. intros d n H. unfold c0. pose proof (N.mod_lt (d + n - 65) 16 ltac:(discriminate)). lia. Qed.

(* RCX on entry to the backward loop: (d + n - 65) rounded down to 16. *)
Lemma rcx_c0: forall d n, 64 <= d -> 128 < n -> d + n <= 2^64 ->
  (d ⊖ 65 + n) .& 18446744073709551600 = c0 d n.
Proof.
  intros d n D N W. rewrite <- (land_mod_pow2 (d ⊖ 65 + n) 64) by reflexivity.
  replace ((d ⊖ 65 + n) mod 2^64) with (d + n - 65).
  - rewrite land_align16 by (change (2^64) with 18446744073709551616 in *; lia). reflexivity.
  - unfold msub. rewrite N.add_mod_idemp_l by discriminate.
    change (2^64) with 18446744073709551616 in *. change (65 mod 18446744073709551616) with 65.
    replace (d + (18446744073709551616 - 65) + n) with (d + n - 65 + 1 * 18446744073709551616) by lia.
    rewrite N.mod_add by discriminate. rewrite N.mod_small by lia. reflexivity.
Qed.

Lemma rsi_c: forall s d c, d <= c -> d < 2^64 -> s ⊖ d ⊕ c = s ⊕ (c - d).
Proof.
  intros s d c DC DB. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small d) by exact DB. change (2^64) with 18446744073709551616 in *.
  replace (s + (18446744073709551616 - d) + c) with (s + (c - d) + 1 * 18446744073709551616) by lia.
  apply N.mod_add. discriminate.
Qed.

(* An XMM register loaded from s - k + n, as the invariants state it. *)
Ltac xmm_tail s n k BIG :=
  pack_xmm; rewrite <- getmem_mod_l;
  rewrite (rsi_c s k n) by (clear - BIG; change (2^64) with 18446744073709551616; lia);
  rewrite ?getmem_mod_l; reflexivity.

Lemma bwd_rsi: forall s x, 64 <= x -> s ⊖ 64 ⊕ x = s ⊕ (x - 64).
Proof.
  intros s x X. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  change (64 mod 2^64) with 64.
  replace (s + (2^64 - 64) + x) with (s + (x - 64) + 1 * 2^64) by (change (2^64) with 18446744073709551616; lia).
  apply N.mod_add. discriminate.
Qed.

(* One side condition of cpy_store / cpy_store4, chosen by its shape. *)
Ltac cside :=
  lazymatch goal with
  | |- nov _ _ _ => assumption
  | |- cpy _ _ _ _ _ => assumption
  | |- ?n < 2^64 => assumption
  | |- 0 < 16 => reflexivity
  | |- forall i, _ -> i < _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; repeat destruct Hi as [Hi|Hi]; change (2^64) with 18446744073709551616 in *; alia
  | |- _ + 16 <= _ => change (2^64) with 18446744073709551616 in *; alia
  | |- _ mod 2^64 = (_ + _) mod 2^64 => rewrite ?N.mod_mod by discriminate; f_equal; alia
  end.

Lemma a0_bounds: forall d, 1 <= a0 d <= 16.
Proof. intro d. unfold a0. pose proof (N.mod_lt d 16 ltac:(discriminate)). lia. Qed.

(* Side conditions of cpy_store / cpy_store4: offset sets, bounds, and
   address congruences. *)
Ltac mside :=
  first [ assumption
        | (intros ? Hi; repeat destruct Hi as [Hi|Hi]; change (2^64) with 18446744073709551616 in *; alia)
        | (change (2^64) with 18446744073709551616 in *; alia)
        | reflexivity
        | (rewrite ?N.mod_mod by discriminate; f_equal; alia)
        | (rewrite ?N.mod_mod by discriminate; rewrite N.add_0_r; reflexivity) ].

Theorem memcpy_correct_loops:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 1853552, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (BIG: 128 < n) (NOV: nov d s n) (NW: d + n <= 2^64)
         (THR: n <= m Ⓠ[0x3215a8]) (DLO: 64 <= d),
  satisfies_all memcpy_amd64 (loops_invs m d s n rsp) loops_exit ((x',s')::t).
Proof.
  intros.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  assert (N0: 0 < n) by (eapply N.lt_trans; [|exact BIG]; reflexivity).
  assert (DSN: n <= msub 64 d s) by (apply nov_ds; [exact NOV | exact N0]).
  assert (SDN: n <= msub 64 s d) by (apply nov_sd; [exact NOV | exact N0]).
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1 BIG NOV NW THR DSN SDN NB DLO. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [D [S [Nn RSP]]]].
    clear NOV NW THR DSN SDN.
    repeat step_prune.
    repeat split; try reflexivity; try assumption.
    unfold xmm_ok. psimpl. pack_xmm. reflexivity.
  - (* dispatch *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX X0]]]]]].
    clear NOV.
    Time repeat x64_step.
    all: set (T := m Ⓠ[0x3215a8]) in *; clearbody T.
    + (* d - s < n and d = s: impossible without overlap *)
      exfalso. apply N.ltb_lt in BC. clear - BC DSN. lia.
    + (* d - s < n: impossible without overlap *)
      exfalso. apply N.ltb_lt in BC. clear - BC DSN. lia.
    + (* 4K aliasing between d and s: the backward loop *)
      clear THR BC0 T BC BC1 DSN SDN.
      assert (DB: d < 2^64) by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
      exists (c0 d n).
      rewrite (rcx_c0 d n DLO BIG NW).
      pose proof (c0_bounds d n ltac:(clear - BIG; lia)) as CB.
      split. clear - CB BIG; lia.
      split. clear - CB BIG; lia.
      split. reflexivity.
      split. { eapply cpy_equiv; [|apply cpy_empty]. intro i. clear. split; [intros []|intro H; lia]. }
      split. reflexivity.
      split. { apply rsi_c; [clear - CB BIG; lia | exact DB]. }
      do 3 (split; [reflexivity|]).
      split. assumption.
      split. exact X0.
      split. unfold xmm_ok. psimpl. pack_xmm. reflexivity.
      split. unfold xmm_ok. psimpl. pack_xmm. reflexivity.
      split. unfold xmm_ok. psimpl. pack_xmm. reflexivity.
      unfold xmm_ok. psimpl. xmm_tail s n 16 BIG.
    + (* the forward loop: k = a0 d, the first 16-aligned store offset *)
      clear THR BC0 T BC BC1 DSN SDN.
      assert (DB: d + 16 < 2^64) by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
      pose proof (a0_bounds d) as A0.
      assert (L15: d .| 15 = d + a0 d - 1).
      { rewrite lor15. unfold a0. pose proof (N.mod_lt d 16 ltac:(discriminate)). lia. }
      exists (a0 d).
      split. clear - A0 BIG; lia.
      split. { eapply cpy_equiv; [|apply cpy_empty]. intro i. clear. split; [intros []|intro H; lia]. }
      split. { rewrite L15, N.mod_small; [lia|]. clear - DB A0. change (2^64) with 18446744073709551616 in *. lia. }
      split. { rewrite rsi_c by (try rewrite L15; clear - DB A0; change (2^64) with 18446744073709551616 in *; lia).
               rewrite L15. f_equal. clear - A0; lia. }
      split. { rewrite rsi_c by (clear - BIG NW; change (2^64) with 18446744073709551616 in *; lia).
               rewrite N.mod_small; [clear - BIG; lia|]. clear - BIG NW. change (2^64) with 18446744073709551616 in *. lia. }
      split. reflexivity.
      split. assumption. split. assumption.
      split. exact X0.
      split. unfold xmm_ok. psimpl. xmm_tail s n 16 BIG.
      split. unfold xmm_ok. psimpl. xmm_tail s n 32 BIG.
      split. unfold xmm_ok. psimpl. xmm_tail s n 48 BIG.
      unfold xmm_ok. psimpl. xmm_tail s n 64 BIG.
    + (* above the non-temporal threshold: excluded by THR *)
      exfalso. clear - BC0 THR.
      destruct (N.ltb_spec n T), (N.eqb_spec n T); cbn in BC0; try discriminate; lia.
  - (* forward loop body *)
    destruct PRE as [k [K [C [RDI [RSI [RDX [RCX [RAX [RSP [X0 [X5 [X6 [X7 X8]]]]]]]]]]]]].
    clear THR.
    repeat x64_step.
    all: assert (E1: 64 + d ⊕ k = d + k + 64) by (clear - K NW BIG; rewrite N.mod_small by lia; lia).
    all: assert (E2: d + n - 64 ⊖ 64 ⊖ d = n - 128) by
           (clear - BIG NW; rewrite (msub_sub 64 (d + n - 64) 64) by lia;
            rewrite (N.mod_small (d + n - 64 - 64)) by lia;
            rewrite (msub_sub 64 (d + n - 64 - 64) d) by lia; rewrite N.mod_small by lia; lia).
    all: rewrite E1, E2, (N.mod_small k) in BC by (clear - K NW BIG; lia).
    all: pose proof (a0_bounds d) as A0.
    all: unfold xmm_ok in X0, X5, X6, X7, X8.
    all: rewrite ?pack16.
    + (* loop exit (JA not taken): store the saved tail and head, then return *)
      apply ja_not_taken in BC.
      assert (EX: n <= k + 128).
      { clear - BC K BIG NW. destruct BC as [B|B]; [apply N.ltb_lt in B | apply N.eqb_eq in B]; lia. }
      split; [assumption|]. split; [assumption|].
      rewrite <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM0)), <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM5)),
              <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM6)), <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM7)),
              <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM8)).
      change (2^(16*8)) with (2^128). rewrite X0, X5, X6, X7, X8.
      eapply cpy_copied; cycle 1.
      { eapply (cpy_store _ _ _ _ _ 0); [eapply (cpy_store _ _ _ _ _ (n - 64));
          [eapply (cpy_store _ _ _ _ _ (n - 48)); [eapply (cpy_store _ _ _ _ _ (n - 32));
           [eapply (cpy_store _ _ _ _ _ (n - 16)); [eapply (cpy_store4 _ _ _ _ n _ k (k+16) (k+32) (k+48)); [exact C|..]|..]|..]|..]|..]|..].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - K EX BIG NW NB A0; aside
             end. }
      intro i. clear - A0 K EX BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
    + (* next iteration (JA taken) *)
      apply ja_taken in BC. destruct BC as [B1 B2]. apply N.ltb_ge in B1. apply N.eqb_neq in B2.
      assert (CT: k + 128 < n) by (clear - B1 B2 K BIG NW; lia).
      exists (k + 64). split. clear - K CT A0; lia. split.
      { eapply cpy_equiv; [|eapply (cpy_store4 _ _ _ _ n _ k (k+16) (k+32) (k+48)); [exact C|..]].
        intro i. clear - A0 K CT. split; intro H; [repeat destruct H as [H|H]; lia | lia].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - K CT BIG NW NB A0; aside
             end. }
      split. rewrite E1. clear; lia. split. f_equal. clear; lia. split. reflexivity.
      do 3 (split; [assumption|]).
      unfold xmm_ok. psimpl.
      repeat split; try assumption.
      all: xmm_tac.
  - (* backward loop body *)
    destruct PRE as [c [C1 [C2 [CC [C [RCX [RSI [RDI [RDX [RAX [RSP [X0 [X5 [X6 [X7 X8]]]]]]]]]]]]]]].
    clear THR.
    Time repeat x64_step.
    all: assert (C64: 64 < c) by (clear - C1 DLO; lia).
    all: assert (E: c ⊖ 64 = c - 64) by
           (clear - C64 C2 NW; rewrite msub_nowrap; rewrite ?N.mod_small; change (2^64) with 18446744073709551616 in *; lia).
    all: pose proof (c0_bounds d n ltac:(clear - BIG; lia)) as CB.
    all: rewrite ?E in *.
    all: unfold xmm_ok in X0, X5, X6, X7, X8.
    all: rewrite ?pack16.
    all: repeat match goal with
         | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
         | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
         end.
    + (* next iteration (JC taken): d < c - 64 *)
      exists (c - 64).
      split. { clear - BC; lia. }
      split. { clear - C2 C64; lia. }
      split. { clear - CC; lia. }
      split.
      { eapply cpy_equiv; [|eapply (cpy_store4 _ _ _ _ n _ (c-d+48) (c-d+32) (c-d+16) (c-d)); [exact C|..]].
        { intro i. clear - BC CC C1. split; intro H; [repeat destruct H as [H|H]; lia | lia]. }
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - BC C1 C2 CC CB BIG NW NB DLO;
                       aside
             end. }
      split. reflexivity.
      split. { rewrite bwd_rsi by (clear - BC; lia). f_equal. clear; lia. }
      split. reflexivity.
      do 3 (split; [assumption|]).
      unfold xmm_ok. psimpl.
      repeat split.
      all: xmm_tac.
    + (* loop exit (JC not taken): c - 64 <= d; store the saved head and tail *)
      split; [assumption|]. split; [assumption|].
      rewrite <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM0)), <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM5)),
              <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM6)), <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM7)),
              <- (setmem_mod_r 64 LittleE 16 _ _ (s1 R_YMM8)).
      change (2^(16*8)) with (2^128). rewrite X0, X5, X6, X7, X8.
      eapply cpy_copied; cycle 1.
      { eapply (cpy_store _ _ _ _ _ (n - 16)); [eapply (cpy_store _ _ _ _ _ 48);
          [eapply (cpy_store _ _ _ _ _ 32); [eapply (cpy_store _ _ _ _ _ 16);
           [eapply (cpy_store _ _ _ _ _ 0); [eapply (cpy_store4 _ _ _ _ n _ (c-d+48) (c-d+32) (c-d+16) (c-d)); [exact C|..]|..]|..]|..]|..]|..].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - BC C1 C2 CC CB BIG NW NB DLO;
                       aside
             end. }
      intro i. clear - BC C1 C2 CC CB BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
Time Qed.
