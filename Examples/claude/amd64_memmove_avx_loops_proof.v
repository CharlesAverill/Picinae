(* memcpy via __memmove_avx_unaligned_erms, the loop paths
   (256 < n <= __x86_rep_movsb_threshold)

   This file continues amd64_memmove_avx_proof.v (see its header for the
   function, the man page text and the provenance).  For 256 < n, the
   function compares n with __x86_rep_movsb_threshold (the quadword at
   0x31a3f8) and takes the REP MOVSB path above it.  Otherwise it checks
   whether d - s < n (dest overlaps the source from above: copy backward),
   compares n with __x86_shared_non_temporal_threshold (0x3215a8), and
   tests for 4 KiB aliasing between dest and src.  The forward loop loads
   the last 128 source bytes into YMM5-YMM8, then copies 128 bytes per
   iteration with 32-byte-aligned stores, and finally stores the saved tail
   and the head (YMM0).  When dest and src alias modulo 4 KiB it runs the
   same loop backward instead.

   This theorem is about memcpy's contract: the areas do not overlap, so
   the overlapping-backward entry is unreachable.  The REP MOVSB and
   non-temporal entries are excluded by the threshold preconditions.

   PRECONDITIONS (beyond 256 < n)
   * nov d s n: [d, d+n) and [s, s+n) do not overlap (the man page's
     requirement for memcpy).
   * d + n <= 2^64: the destination does not wrap around the address space
     (the loops compare raw pointers).
   * n <= m[0x31a3f8] and n <= m[0x3215a8]: the REP MOVSB and non-temporal
     thresholds, read before any store.
   * 128 <= d: the backward loop steps its store pointer down by 128 and
     exits when it is no longer above d; for d < 128 the subtraction can wrap
     around zero.  No real buffer starts in the first 128 bytes of the address
     space (page 0 is never mapped).

   OUTPUT: at the RET, RAX = d, RSP is unchanged, and copied m m' d s n
   (dest[0,n) = src[0,n), all other bytes unchanged).

   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.
 *)

Require Import Picinae_amd64.
Require Import memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Require Import amd64_memmove_avx_proof.
Open Scope N.

(* Four 32-byte stores of source pieces read from the current memory M:
   when the buffers don't overlap, each piece is the original source. *)
Lemma cpy_store4w:
  forall m M d s n (W:N->Prop) o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4,
  cpy m M d s W -> (forall i, W i -> i < n) -> nov d s n -> n < 2^64 ->
  o1 + 32 <= n -> o2 + 32 <= n -> o3 + 32 <= n -> o4 + 32 <= n ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 ->
  a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 ->
  b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (M Ⓨ[b1])) a2 (M Ⓨ[b2])) a3 (M Ⓨ[b3])) a4 (M Ⓨ[b4])) d s
      (fun i => W i \/ o1 <= i < o1 + 32 \/ o2 <= i < o2 + 32 \/ o3 <= i < o3 + 32 \/ o4 <= i < o4 + 32).
Proof.
  intros m M d s n W o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4 C WN NOV NB O1 O2 O3 O4 A1 A2 A3 A4 B1 B2 B3 B4.
  rewrite (cpy_load m M d s W n o1 32 b1 C WN NOV O1 B1).
  rewrite (cpy_load m M d s W n o2 32 b2 C WN NOV O2 B2).
  rewrite (cpy_load m M d s W n o3 32 b3 C WN NOV O3 B3).
  rewrite (cpy_load m M d s W n o4 32 b4 C WN NOV O4 B4).
  assert (C4: cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (getmem 64 LittleE 32 m b1)) a2 (getmem 64 LittleE 32 m b2)) a3 (getmem 64 LittleE 32 m b3))
          a4 (getmem 64 LittleE 32 m b4)) d s
      (fun i => (((W i \/ o1 <= i < o1 + 32) \/ o2 <= i < o2 + 32) \/ o3 <= i < o3 + 32) \/ o4 <= i < o4 + 32)).
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
Definition a0 (d:N) := 32 - d mod 32.
Definition c0 (d n:N) := (d + n - 129) - (d + n - 129) mod 32.

Definition lp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 493 | 623 => true
  | _ => false
  end | _ => false end.

Definition lp_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
               st R_RSP = rsp)
  (* the n > 256 dispatch *)
  | 309 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                 st R_RSP = rsp /\ st R_RAX = d /\ st R_YMM0 = m Ⓨ[s])
  (* forward loop head: [a0, k) copied *)
  | 416 => Some (exists k, a0 d <= k < n - 128 /\ cpy m (st V_MEM64) d s (fun i => a0 d <= i < k) /\
                 st R_RDI = d + k /\ st R_RSI = s ⊕ k /\ st R_RDX = d + n - 128 /\ st R_RCX = d /\
                 st R_RAX = d /\ st R_RSP = rsp /\
                 st R_YMM0 = m Ⓨ[s] /\ st R_YMM5 = m Ⓨ[s ⊕ (n-32)] /\
                 st R_YMM6 = m Ⓨ[s ⊕ (n-64)] /\ st R_YMM7 = m Ⓨ[s ⊕ (n-96)] /\
                 st R_YMM8 = m Ⓨ[s ⊕ (n-128)])
  (* backward loop head: c is the next (aligned) store address,
     [c-d+128, c0-d+128) copied *)
  | 544 => Some (exists c, d < c /\ c + 128 <= d + n /\ c <= c0 d n /\
                 cpy m (st V_MEM64) d s (fun i => c - d + 128 <= i < c0 d n - d + 128) /\
                 st R_RCX = c /\ st R_RSI = s ⊕ (c - d) /\ st R_RDI = d /\ st R_RDX = n /\
                 st R_RAX = d /\ st R_RSP = rsp /\
                 st R_YMM0 = m Ⓨ[s] /\ st R_YMM5 = m Ⓨ[s ⊕ 32] /\
                 st R_YMM6 = m Ⓨ[s ⊕ 64] /\ st R_YMM7 = m Ⓨ[s ⊕ 96] /\
                 st R_YMM8 = m Ⓨ[s ⊕ (n-32)])
  | 493 | 623 => Some (postcondition m d s n rsp st)
  (* overlapping backward copy, REP MOVSB, non-temporal: unreachable *)
  | 496 | 704 | 813 => Some False
  | _ => None
  end | _ => None end.

(* These paths branch only on CF and ZF, so abstract away the other flags. *)
Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true
| _ => false end).

(* Alignment arithmetic for 32-byte vectors. *)
Lemma lor31: forall d, d .| 31 = d - d mod 32 + 31.
Proof.
  intro d.
  assert (E: d - d mod 32 = d >> 5 << 5).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^5) with 32.
    rewrite (N.div_mod d 32) at 1 by discriminate. lia. }
  assert (B: d .| 31 = (d >> 5 << 5) .| 31).
  { apply N.bits_inj. intro i. rewrite !N.lor_spec. destruct (N.ltb_spec i 5).
    - assert (T: N.testbit 31 i = true) by
        (assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia;
         repeat destruct Hc as [E0|Hc]; subst; reflexivity).
      rewrite T, !Bool.orb_true_r. reflexivity.
    - rewrite N.shiftl_spec_high by lia. rewrite N.shiftr_spec by lia.
      replace (i - 5 + 5) with i by lia. reflexivity. }
  rewrite B, E. apply lor_plus.
  apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0. destruct (N.ltb_spec i 5).
  - rewrite N.shiftl_spec_low by lia. reflexivity.
  - replace (N.testbit 31 i) with false. apply Bool.andb_false_r.
    symmetry. apply N.bits_above_log2. change (N.log2 31) with 4. lia.
Qed.

Lemma land_align32: forall x, x < 2^64 -> x .& 18446744073709551584 = x - x mod 32.
Proof.
  intros x X.
  assert (E: x - x mod 32 = x >> 5 << 5).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^5) with 32.
    rewrite (N.div_mod x 32) at 1 by discriminate. lia. }
  rewrite E. change 18446744073709551584 with (N.ldiff (N.ones 64) (N.ones 5)).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i 5).
  - rewrite (N.ones_spec_low 5 i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high 5 i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - 5 + 5) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct x as [|p]. apply N.bits_0.
      apply N.bits_above_log2. apply N.lt_le_trans with 64; [|lia].
      apply N.log2_lt_pow2; [reflexivity|exact X].
Qed.

Lemma a0_bounds: forall d, 1 <= a0 d <= 32.
Proof. intro d. unfold a0. pose proof (N.mod_lt d 32 ltac:(discriminate)). lia. Qed.

Lemma c0_bounds: forall d n, 160 <= d + n -> d + n - 160 <= c0 d n <= d + n - 129.
Proof. intros d n H. unfold c0. pose proof (N.mod_lt (d + n - 129) 32 ltac:(discriminate)). lia. Qed.

(* RCX on entry to the backward loop: (d + n - 129) rounded down to 32. *)
Lemma rcx_c0: forall d n, 128 <= d -> 256 < n -> d + n <= 2^64 ->
  (d ⊖ 129 + n) .& 18446744073709551584 = c0 d n.
Proof.
  intros d n D N W. rewrite <- (land_mod_pow2 (d ⊖ 129 + n) 64) by reflexivity.
  replace ((d ⊖ 129 + n) mod 2^64) with (d + n - 129).
  - rewrite land_align32 by (change (2^64) with 18446744073709551616 in *; lia). reflexivity.
  - unfold msub. rewrite N.add_mod_idemp_l by discriminate.
    change (2^64) with 18446744073709551616 in *. change (129 mod 18446744073709551616) with 129.
    replace (d + (18446744073709551616 - 129) + n) with (d + n - 129 + 1 * 18446744073709551616) by lia.
    rewrite N.mod_add by discriminate. rewrite N.mod_small by lia. reflexivity.
Qed.

Lemma rsi_c: forall s d c, d <= c -> d < 2^64 -> s ⊖ d ⊕ c = s ⊕ (c - d).
Proof.
  intros s d c DC DB. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small d) by exact DB. change (2^64) with 18446744073709551616 in *.
  replace (s + (18446744073709551616 - d) + c) with (s + (c - d) + 1 * 18446744073709551616) by lia.
  apply N.mod_add. discriminate.
Qed.

(* Equal addresses mod 2^64 give equal loads. *)
Lemma getmem_addr: forall w e len (m:memory) a b, a mod 2^w = b mod 2^w -> getmem w e len m a = getmem w e len m b.
Proof. intros. rewrite <- getmem_mod_l, H, getmem_mod_l. reflexivity. Qed.

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

(* lia on just the arithmetic: drop memory, store and copy facts first. *)
Ltac alia :=
  repeat match goal with H: ?T |- _ =>
    lazymatch T with
    | context [setmem] => clear H
    | context [MemAcc] => clear H
    | cpy _ _ _ _ _ => clear H
    | nov _ _ _ => clear H
    | models _ _ => clear H
    | _ = _ :> store => clear H
    | context [V_MEM64] => clear H
    | context [getmem _ _ 32 _ _] => clear H
    end
  end; change (2^64) with 18446744073709551616 in *; lia.

(* Refute a path from one branch condition plus the size/threshold facts.
   lia must never see a getmem term: its preprocessing unfolds the load and
   runs out of memory. *)
Ltac refute B :=
  exfalso;
  match goal with H: ?T |- _ =>
    lazymatch T with context [getmem] => fail | context [V_MEM64] => fail | _ => idtac end;
    lazymatch T with _ < _ => idtac | _ <= _ => idtac | _ = _ :> N => idtac | _ <> _ => idtac end;
    clear - H B; lia
  end.

(* Keep only order/equality facts between numbers, then lia. *)
Ltac nlia :=
  repeat match goal with H: ?T |- _ =>
    lazymatch type of T with
    | Prop =>
        lazymatch T with
        | context [getmem] => clear H | context [V_MEM64] => clear H
        | _ < _ => fail | _ <= _ => fail | _ <> _ :> N => fail
        | _ = _ :> N => fail
        | _ => clear H
        end
    | _ => fail
    end
  end; lia.

Ltac step_prune := x64_step; try (bc_norm; first [discriminate | exfalso; alia]).

(* The JA (CF=0 and ZF=0) branch condition as lifted. *)
Lemma ja_not_taken: forall a b:bool,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = 0 -> a = true \/ b = true.
Proof. intros [|] [|]; cbn; intro H; first [discriminate | tauto]. Qed.

Lemma ja_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = N.pos p -> a = false /\ b = false.
Proof. intros [|] [|] p; cbn; intro H; first [discriminate | tauto]. Qed.

Lemma msub_add_mod: forall a b c, b <= a -> a < 2^64 -> (msub 64 a b + c) mod 2^64 = (c + (a - b)) mod 2^64.
Proof.
  intros a b c BA AB. assert (BB: b < 2^64) by lia.
  rewrite msub_nowrap by (rewrite (N.mod_small a), (N.mod_small b) by assumption; exact BA).
  rewrite (N.mod_small a), (N.mod_small b) by assumption. f_equal. lia.
Qed.

Lemma bwd_rsi: forall s x, 128 <= x -> s ⊖ 128 ⊕ x = s ⊕ (x - 128).
Proof.
  intros s x X. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  change (128 mod 2^64) with 128.
  replace (s + (2^64 - 128) + x) with (s + (x - 128) + 1 * 2^64) by (change (2^64) with 18446744073709551616; lia).
  apply N.mod_add. discriminate.
Qed.

(* An arithmetic side condition, in a context already cleared down to the
   arithmetic facts. *)
Ltac aside :=
  lazymatch goal with
  | |- 0 < 32 => reflexivity
  | |- forall i, _ -> _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; cbv beta in Hi; repeat destruct Hi as [Hi|Hi];
      change (2^64) with 18446744073709551616 in *; lia
  | |- (?x mod 2^64) mod 2^64 = ?x mod 2^64 => apply N.mod_mod; discriminate
  | |- (msub 64 _ _ + _) mod 2^64 = _ mod 2^64 =>
      rewrite msub_add_mod by (change (2^64) with 18446744073709551616 in *; lia);
      f_equal; change (2^64) with 18446744073709551616 in *; lia
  | |- _ mod 2^64 = _ mod 2^64 => f_equal; change (2^64) with 18446744073709551616 in *; lia
  | |- _ => change (2^64) with 18446744073709551616 in *; lia
  end.

Theorem memmove_avx_correct_loops:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (BIG: 256 < n) (NOV: nov d s n) (NW: d + n <= 2^64)
         (THR1: n <= m Ⓠ[0x31a3f8]) (THR2: n <= m Ⓠ[0x3215a8]) (DLO: 128 <= d),
  satisfies_all memmove_avx_amd64 (lp_invs m d s n rsp) lp_exit ((x',s')::t).
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
  eapply models_at_invariant; try eassumption. apply memmove_avx_welltyped. intro MDL1.
  clear - PRE MDL1 BIG NOV NW THR1 THR2 DSN SDN NB DLO. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [D [S [Nn RSP]]]].
    clear NOV NW DSN SDN DLO.
    repeat x64_step.
    all: try (set (T := m Ⓠ[0x31a3f8]) in *; clearbody T).
    all: try (match goal with |- False => idtac | |- nextinv _ _ _ _ _ => idtac end; bc_norm; refute BIG).
    all: try (match goal with |- False => idtac end;
              bc_norm; first [discriminate | refute THR1 | exfalso; nlia]).
    all: repeat split; reflexivity || assumption.
  - (* dispatch *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX Y0]]]]]].
    clear NOV.
    repeat x64_step.
    all: set (T := m Ⓠ[0x3215a8]) in *; clearbody T.
    all: try (match goal with |- False => idtac end; bc_norm; first [discriminate | exfalso; nlia]).
    all: change (2^7) with 128.
    all: assert (DB: d + 32 < 2^64) by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
    all: pose proof (N.mod_lt d 32 ltac:(discriminate)) as DM; pose proof (N.mod_le d 32 ltac:(discriminate)) as DL.
    + (* 4K aliasing between d and s: the backward loop *)
      clear THR2 THR1 DSN SDN.
      exists (c0 d n).
      rewrite (rcx_c0 d n DLO BIG NW).
      pose proof (c0_bounds d n ltac:(clear - BIG; lia)) as CB.
      split. clear - CB BIG; lia.
      split. clear - CB BIG; lia.
      split. apply N.le_refl.
      split. { eapply cpy_equiv; [|apply cpy_empty]. intro i. clear. split; [intros []|intro H; lia]. }
      split. reflexivity.
      split. { apply rsi_c; [clear - CB BIG; lia | clear - DB; lia]. }
      do 2 (split; [reflexivity|]).
      do 3 (split; [assumption|]).
      do 3 (split; [reflexivity|]).
      apply getmem_addr. apply addr_tail_w; clear - BIG; lia.
    + (* the forward loop: k = a0 d, the first 32-aligned store offset *)
      clear THR2 THR1 DSN SDN.
      pose proof (a0_bounds d) as A0.
      exists (a0 d).
      split. clear - A0 BIG; lia.
      split. { eapply cpy_equiv; [|apply cpy_empty]. intro i. clear. split; [intros []|intro H; lia]. }
      split. { rewrite lor31, N.mod_small; [unfold a0; clear - DM DL; lia|].
               clear - DB DM DL. change (2^64) with 18446744073709551616 in *. lia. }
      split. { unfold msub. rewrite lor31. rewrite ?N.add_mod_idemp_l, ?N.add_mod_idemp_r by discriminate.
               rewrite (N.mod_small d) by (clear - DB; lia).
               match goal with |- ?a mod _ = ?b mod _ =>
                 replace a with (b + 1 * 2^64) by (unfold a0; clear - DB DM DL; change (2^64) with 18446744073709551616 in *; lia) end.
               apply N.mod_add. discriminate. }
      split. { unfold msub. rewrite N.add_mod_idemp_l by discriminate.
               change (128 mod 2^64) with 128.
               replace (d + (2^64 - 128) + n) with (d + n - 128 + 1 * 2^64)
                 by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
               rewrite N.mod_add by discriminate. apply N.mod_small. clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia. }
      do 2 (split; [reflexivity|]).
      do 2 (split; [assumption|]).
      repeat split; apply getmem_addr; apply addr_tail_w; clear - BIG; lia.
  - (* forward loop body *)
    destruct PRE as [k [K [C [RDI [RSI [RDX [RCX [RAX [RSP [Y0 [Y5 [Y6 [Y7 Y8]]]]]]]]]]]]].
    clear THR1 THR2.
    repeat x64_step.
    all: change (2^7) with 128 in *.
    all: assert (E1: 128 + d ⊕ k = d + k + 128) by (clear - K NW BIG; rewrite N.mod_small by lia; lia).
    all: assert (E2: d + n - 128 ⊖ 128 ⊖ d = n - 256) by
           (clear - BIG NW; rewrite (msub_sub 64 (d + n - 128) 128) by lia;
            rewrite (N.mod_small (d + n - 128 - 128)) by lia;
            rewrite (msub_sub 64 (d + n - 128 - 128) d) by lia; rewrite N.mod_small by lia; lia).
    all: rewrite E1, E2, (N.mod_small k) in BC by (clear - K NW BIG; lia).
    all: pose proof (a0_bounds d) as A0.
    + (* loop exit (JA not taken): store the saved tail and head, then return *)
      apply ja_not_taken in BC.
      assert (EX: n <= k + 256).
      { clear - BC K BIG NW. destruct BC as [B|B]; [apply N.ltb_lt in B | apply N.eqb_eq in B]; lia. }
      split; [assumption|]. split; [assumption|].
      eapply cpy_copied; cycle 1.
      { eapply (cpy_store _ _ _ _ _ 0); [eapply (cpy_store _ _ _ _ _ (n - 128));
          [eapply (cpy_store _ _ _ _ _ (n - 96)); [eapply (cpy_store _ _ _ _ _ (n - 64));
           [eapply (cpy_store _ _ _ _ _ (n - 32)); [eapply (cpy_store4w _ _ _ _ n _ k (k+32) (k+64) (k+96)); [exact C|..]|..]|..]|..]|..]|..].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - K EX BIG NW NB A0; aside
             end. }
      intro i. clear - A0 K EX BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
    + (* next iteration (JA taken) *)
      apply ja_taken in BC. destruct BC as [B1 B2]. apply N.ltb_ge in B1. apply N.eqb_neq in B2.
      assert (CT: k + 256 < n) by (clear - B1 B2 K BIG NW; lia).
      exists (k + 128). split. clear - K CT A0; lia. split.
      { eapply cpy_equiv; [|eapply (cpy_store4w _ _ _ _ n _ k (k+32) (k+64) (k+96)); [exact C|..]].
        intro i. clear - A0 K CT. split; intro H; [repeat destruct H as [H|H]; lia | lia].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - K CT BIG NW NB A0; aside
             end. }
      split. rewrite E1. clear; lia. split. f_equal. clear; lia. split. reflexivity.
      repeat split; try assumption.
      all: match goal with H: ?r = _ |- ?r = _ => rewrite H; apply getmem_mod_l end.
  - (* backward loop body *)
    destruct PRE as [c [C1 [C2 [C3 [C [RCX [RSI [RDI [RDX [RAX [RSP [Y0 [Y5 [Y6 [Y7 Y8]]]]]]]]]]]]]]].
    clear THR1 THR2.
    repeat x64_step.
    all: change (2^7) with 128 in *.
    all: assert (E: c ⊖ 128 = c - 128) by
           (clear - C1 C2 NW DLO; rewrite msub_sub by lia; apply N.mod_small;
            change (2^64) with 18446744073709551616 in *; lia).
    all: rewrite E in BC.
    all: pose proof (c0_bounds d n ltac:(clear - BIG; lia)) as CB.
    + (* next iteration (JC taken) *)
      apply N.ltb_lt in BC.
      exists (c - 128).
      split. clear - BC; lia. split. clear - C2 BC; lia. split. clear - C3 BC; lia.
      split.
      { eapply cpy_equiv; [|eapply (cpy_store4w _ _ _ _ n _ (c-d+96) (c-d+64) (c-d+32) (c-d)); [exact C|..]].
        intro i. clear - BC C1 C2 C3 CB. split; intro H; [repeat destruct H as [H|H]; lia | lia].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - BC C1 C2 C3 CB BIG NW NB DLO; aside
             end. }
      split. exact E.
      split. { rewrite bwd_rsi by (clear - BC; lia). f_equal. clear - BC; lia. }
      repeat split; try assumption.
      all: match goal with H: ?r = _ |- ?r = _ =>
             rewrite H; apply getmem_addr; rewrite ?N.mod_mod by discriminate; f_equal; clear; lia end.
    + (* loop exit (JC not taken): store the saved head and tail, then return *)
      apply N.ltb_ge in BC.
      split; [assumption|]. split; [assumption|].
      eapply cpy_copied; cycle 1.
      { eapply (cpy_store _ _ _ _ _ (n - 32)); [eapply (cpy_store _ _ _ _ _ 96);
          [eapply (cpy_store _ _ _ _ _ 64); [eapply (cpy_store _ _ _ _ _ 32);
           [eapply (cpy_store _ _ _ _ _ 0); [eapply (cpy_store4w _ _ _ _ n _ (c-d+96) (c-d+64) (c-d+32) (c-d)); [exact C|..]|..]|..]|..]|..]|..].
        all: lazymatch goal with
             | |- cpy _ _ _ _ _ => assumption | |- nov _ _ _ => assumption
             | |- _ => clear - BC C1 C2 C3 CB BIG NW NB DLO; aside
             end. }
      intro i. clear - BC C1 C2 C3 CB BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
Time Qed.

