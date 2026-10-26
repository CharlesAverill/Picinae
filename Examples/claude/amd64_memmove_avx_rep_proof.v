(* memcpy via __memmove_avx_unaligned_erms, the REP MOVSB paths
   (__x86_rep_movsb_threshold < n < __x86_rep_movsb_stop_threshold)

   This file continues amd64_memmove_avx_proof.v and
   amd64_memmove_avx_loops_proof.v.  Above the REP MOVSB threshold (the
   quadword at 0x31a3f8, 2048 by default) and below the stop threshold
   (0x3215a0, the non-temporal threshold by default), the function:
   * copies backward with the 128-byte loop when dest overlaps the source
     from above (d - s < n), unreachable here;
   * otherwise, if bit 0 of the 4-byte flag word at 0x321598 is clear
     (no "avoid short distance REP MOVSB" preference), copies with REP MOVSB
     after aligning the source to 64 bytes (when (d - s) & 0xe00 = 0) or the
     destination to 64 bytes (otherwise);
   * if the bit is set and (d - s) mod 2^32 > 2^32 - 64 (a short distance),
     falls back to the forward 128-byte loop;
   * otherwise aligns the destination to 64 bytes and uses REP MOVSB.
   Every REP MOVSB path saves the first 64 source bytes in YMM0/YMM1 first
   and stores them after the REP MOVSB.

   PRECONDITIONS (memcpy's contract and the sizes)
   * nov d s n: [d, d+n) and [s, s+n) do not overlap.
   * d + n <= 2^64 and s + n <= 2^64: neither area wraps around the address
     space.
   * m[0x31a3f8] < n < m[0x3215a0]: the two thresholds (8 bytes each), read
     before any store, and 256 < n (glibc never sets the REP MOVSB threshold
     below 256 for AVX, so this follows in a running process).
   * DF = 0, as the ABI requires on function entry.
   * 128 <= d, as in amd64_memmove_avx_loops_proof.v.

   OUTPUT: at the RET, RAX = d, RSP is unchanged, and copied m m' d s n.

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
Require Import amd64_memmove_avx_loops_proof.
Open Scope N.

(* First REP MOVSB offset when the source is aligned to 64 bytes (site A)
   and when the destination is (site B). *)
Definition aA (s:N) := 64 - s mod 64.
Definition aB (d:N) := (64 - d mod 64) mod 64.

Definition rp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 493 | 692 | 794 => true
  | _ => false
  end | _ => false end.

Definition rp_invs (m d s n rsp:N) (t:trace) :=
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
  | 493 | 692 | 794 => Some (postcondition m d s n rsp st)
  (* the n <= __x86_rep_movsb_threshold paths, overlapping backward copy,
     at or above the stop threshold: unreachable *)
  | 309 | 496 | 800 => Some False
  | _ => None
  end | _ => None end.

Lemma land_align64: forall x, x < 2^64 -> x .& 18446744073709551552 = x - x mod 64.
Proof.
  intros x X.
  assert (E: x - x mod 64 = x >> 6 << 6).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^6) with 64.
    rewrite (N.div_mod x 64) at 1 by discriminate. lia. }
  rewrite E. change 18446744073709551552 with (N.ldiff (N.ones 64) (N.ones 6)).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i 6).
  - rewrite (N.ones_spec_low 6 i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high 6 i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - 6 + 6) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct x as [|p]. apply N.bits_0.
      apply N.bits_above_log2. apply N.lt_le_trans with 64; [|lia].
      apply N.log2_lt_pow2; [reflexivity|exact X].
Qed.

Lemma lor63: forall d, d .| 63 = d - d mod 64 + 63.
Proof.
  intro d.
  assert (E: d - d mod 64 = d >> 6 << 6).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^6) with 64.
    rewrite (N.div_mod d 64) at 1 by discriminate. lia. }
  assert (B: d .| 63 = (d >> 6 << 6) .| 63).
  { apply N.bits_inj. intro i. rewrite !N.lor_spec. destruct (N.ltb_spec i 6).
    - assert (T: N.testbit 63 i = true) by
        (assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5) by lia;
         repeat destruct Hc as [E0|Hc]; subst; reflexivity).
      rewrite T, !Bool.orb_true_r. reflexivity.
    - rewrite N.shiftl_spec_high by lia. rewrite N.shiftr_spec by lia.
      replace (i - 6 + 6) with i by lia. reflexivity. }
  rewrite B, E. apply lor_plus.
  apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0. destruct (N.ltb_spec i 6).
  - rewrite N.shiftl_spec_low by lia. reflexivity.
  - replace (N.testbit 63 i) with false. apply Bool.andb_false_r.
    symmetry. apply N.bits_above_log2. change (N.log2 63) with 5. lia.
Qed.

(* Rounding d up to a multiple of 64. *)
Lemma alignup64: forall d, (63 + d) - (63 + d) mod 64 = d + aB d.
Proof.
  intro d. unfold aB.
  assert (E: d = d mod 64 + d / 64 * 64) by (rewrite (N.div_mod d 64) at 1 by discriminate; lia).
  assert (R: d mod 64 < 64) by (apply N.mod_lt; discriminate).
  remember (d mod 64) as r. remember (d / 64) as q. clear Heqr Heqq.
  rewrite E. replace (63 + (r + q * 64)) with ((63 + r) + q * 64) by lia.
  rewrite N.mod_add by discriminate.
  destruct (N.eq_dec r 0) as [->|R0].
  - change ((63 + 0) mod 64) with 63. change ((64 - 0) mod 64) with 0. lia.
  - rewrite (N.mod_small (64 - r)) by lia. replace (63 + r) with ((r - 1) + 1 * 64) by lia.
    rewrite N.mod_add, N.mod_small by lia. lia.
Qed.

Lemma aA_bounds: forall s, 1 <= aA s <= 64.
Proof. intro s. unfold aA. pose proof (N.mod_lt s 64 ltac:(discriminate)). lia. Qed.

Lemma aB_bounds: forall d, aB d < 64.
Proof. intro d. unfold aB. apply N.mod_lt. discriminate. Qed.

(* Close an equation between sums taken mod 2^64 (msub unfolded), by
   dropping inner reductions that are in range and matching multiples of
   2^64. *)
Ltac fin_mod :=
  change (2^64) with 18446744073709551616 in *;
  rewrite ?N.add_mod_idemp_l, ?N.add_mod_idemp_r by discriminate;
  repeat match goal with |- context [?x mod 18446744073709551616] =>
    rewrite (N.mod_small x) by lia end;
  first
  [ lia
  | match goal with
    | |- ?a mod ?M = ?b mod ?M =>
        first [ f_equal; lia
              | replace a with (b + 1 * M) by lia; apply N.mod_add; discriminate
              | replace a with (b + 2 * M) by lia; apply N.mod_add; discriminate
              | replace b with (a + 1 * M) by lia; symmetry; apply N.mod_add; discriminate ]
    | |- ?a mod ?M = ?b =>
        first [ rewrite (N.mod_small a) by lia; lia
              | replace a with (b + 1 * M) by lia; rewrite N.mod_add by discriminate; apply N.mod_small; lia
              | replace a with (b + 2 * M) by lia; rewrite N.mod_add by discriminate; apply N.mod_small; lia ]
    | |- ?b = ?a mod ?M =>
        first [ rewrite (N.mod_small a) by lia; lia
              | replace a with (b + 1 * M) by lia; rewrite N.mod_add by discriminate; symmetry; apply N.mod_small; lia ]
    end ].

(* An address/count conjunct of the REP MOVSB entry invariants. *)
Ltac rep_arith NW SW NB BIG AA AB DM DL SM SL AU :=
  first
  [ unfold msub; rewrite ?lor63;
    rewrite ?land_align64 by (change (2^64) with 18446744073709551616 in *; clear - NW SW BIG; lia);
    rewrite ?AU; clear - NW SW NB BIG AB DM DL AU; fin_mod
  | unfold msub; rewrite ?lor63; unfold aA in *; clear - NW SW NB BIG AA DM DL SM SL; fin_mod ].

(* assumption and reflexivity without conversion (which would unfold loads). *)
Ltac sassumption := match goal with H: ?T |- ?G => constr_eq T G; exact H end.
Ltac sreflexivity := match goal with |- ?a = ?b => constr_eq a b; reflexivity end.

(* One step of REP MOVSB from offset a with k bytes done (K: k <= n - a):
   either RCX = 0 and the saved 64-byte head is stored (exit), or one more
   byte is copied (iteration).  The goals are in the order step_stmt leaves
   them: RCX = 0 first. *)
Ltac rep_exit C NOV NB BIG K BC A1 :=
  apply N.eqb_eq in BC;
  split; [assumption|]; split; [assumption|];
  eapply cpy_copied; cycle 1;
  [ eapply (cpy_store _ _ _ _ _ 32); [eapply (cpy_store _ _ _ _ _ 0); [exact C|..]|..];
    lazymatch goal with
    | |- cpy _ _ _ _ _ => sassumption
    | |- _ => clear - K BC A1 NB BIG; aside
    end
  | let i := fresh "i" in let H := fresh "H" in
    intro i; clear - K BC A1 BIG; split; intro H; [repeat destruct H as [H|H]; lia | lia] ].

Ltac rep_iter a k n C NOV NB BIG K BC A1 :=
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
    rewrite (cpy_load _ M _ _ _ n (a + k) 1 b C) by
      (first [ sassumption
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

Theorem memmove_avx_correct_rep:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (DF: st R_DF = 0)
         (NOV: nov d s n) (NW: d + n <= 2^64) (SW: s + n <= 2^64)
         (BIG: 256 < n) (THR1: m Ⓠ[0x31a3f8] < n) (THR3: n < m Ⓠ[0x3215a0]) (DLO: 128 <= d),
  satisfies_all memmove_avx_amd64 (rp_invs m d s n rsp) rp_exit ((x',s')::t).
Proof.
  intros.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memmove_avx_welltyped. intro MDL1.
  clear - PRE MDL1 NOV NW SW BIG THR1 THR3 NB DLO. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [D [S [Nn [RSP DF]]]]].
    clear NOV NW SW DLO.
    repeat x64_step.
    all: try (set (T := m Ⓠ[0x31a3f8]) in *; clearbody T).
    all: try (match goal with |- False => idtac | |- nextinv _ _ _ _ _ => idtac end; bc_norm; refute BIG).
    all: try (match goal with |- False => idtac end;
              bc_norm; first [discriminate | refute THR1 | exfalso; nlia]).
    all: repeat split; reflexivity || assumption.
  - (* forward loop body *)
    destruct PRE as [k [K [C [RDI [RSI [RDX [RCX [RAX [RSP [Y0 [Y5 [Y6 [Y7 Y8]]]]]]]]]]]]].
    clear THR1 THR3.
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
  - (* REP MOVSB, site A *)
    destruct PRE as [k [K [RCX [RDI [RSI [R8 [RAX [DF [RSP [Y0 [Y1 C]]]]]]]]]]].
    eapply NIStep; [reflexivity|reflexivity|]. intros c0 s0 x XS. step_stmt XS.
    destruct (n - aA s - k =? 0) eqn:BC.
    all: destruct XS as [XS _].
    all: repeat (ISA_step_and_simplify XS).
    all: destruct XS as [XS ?]; subst x; rewrite XS; clear XS; try clear s0; try rewrite exitof_some.
    all: repeat x64_step.
    all: pose proof (aA_bounds s) as A1.
    + rep_exit C NOV NB BIG K BC A1.
    + rep_iter (aA s) k n C NOV NB BIG K BC A1.
  - (* dispatch *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX [DF Y0]]]]]]].
    assert (DSN: n <= msub 64 d s) by (apply nov_ds; [exact NOV | clear - BIG; lia]).
    clear NOV.
    repeat x64_step.
    all: set (T := m Ⓠ[0x3215a0]) in *; clearbody T.
    all: try (match goal with |- False => idtac end; bc_norm; first [refute DSN | refute THR3]).
    all: change (2^7) with 128.
    all: pose proof (N.mod_lt d 64 ltac:(discriminate)) as DM; pose proof (N.mod_le d 64 ltac:(discriminate)) as DL.
    all: pose proof (N.mod_lt s 64 ltac:(discriminate)) as SM; pose proof (N.mod_le s 64 ltac:(discriminate)) as SL.
    all: pose proof (aA_bounds s) as AA; pose proof (aB_bounds d) as AB; pose proof (alignup64 d) as AU.
    all: try (exists 0;
      split; [clear - AA AB BIG; lia|];
      split; [rep_arith NW SW NB BIG AA AB DM DL SM SL AU|];
      split; [rep_arith NW SW NB BIG AA AB DM DL SM SL AU|];
      split; [rep_arith NW SW NB BIG AA AB DM DL SM SL AU|];
      do 4 (split; [assumption || reflexivity|]);
      split; [assumption|]; split; [reflexivity|];
      eapply cpy_equiv; [|apply cpy_empty]; intro i; clear; split; [intros []|intro H; lia]).
    (* the short-distance fallback: the forward loop, k = a0 d *)
    assert (DB: d + 32 < 2^64) by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
    pose proof (N.mod_lt d 32 ltac:(discriminate)) as DM32; pose proof (N.mod_le d 32 ltac:(discriminate)) as DL32.
    pose proof (a0_bounds d) as A0.
    exists (a0 d).
    split. clear - A0 BIG; lia.
    split. { eapply cpy_equiv; [|apply cpy_empty]. intro i. clear. split; [intros []|intro H; lia]. }
    split. { rewrite lor31, N.mod_small; [unfold a0; clear - DM32 DL32; lia|].
             clear - DB DM32 DL32. change (2^64) with 18446744073709551616 in *. lia. }
    split. { unfold msub. rewrite lor31. rewrite ?N.add_mod_idemp_l, ?N.add_mod_idemp_r by discriminate.
             rewrite (N.mod_small d) by (clear - DB; lia).
             match goal with |- ?a mod _ = ?b mod _ =>
               replace a with (b + 1 * 2^64) by (unfold a0; clear - DB DM32 DL32; change (2^64) with 18446744073709551616 in *; lia) end.
             apply N.mod_add. discriminate. }
    split. { unfold msub. rewrite N.add_mod_idemp_l by discriminate.
             change (128 mod 2^64) with 128.
             replace (d + (2^64 - 128) + n) with (d + n - 128 + 1 * 2^64)
               by (clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia).
             rewrite N.mod_add by discriminate. apply N.mod_small. clear - NW BIG; change (2^64) with 18446744073709551616 in *; lia. }
    do 2 (split; [reflexivity|]).
    do 2 (split; [assumption|]).
    repeat split; apply getmem_addr; apply addr_tail_w; clear - BIG; lia.
  - (* REP MOVSB, site B *)
    destruct PRE as [k [K [RCX [RDI [RSI [R8 [RAX [DF [RSP [Y0 [Y1 C]]]]]]]]]]].
    eapply NIStep; [reflexivity|reflexivity|]. intros c0 s0 x XS. step_stmt XS.
    destruct (n - aB d - k =? 0) eqn:BC.
    all: destruct XS as [XS _].
    all: repeat (ISA_step_and_simplify XS).
    all: destruct XS as [XS ?]; subst x; rewrite XS; clear XS; try clear s0; try rewrite exitof_some.
    all: repeat x64_step.
    all: pose proof (aB_bounds d) as A1.
    + rep_exit C NOV NB BIG K BC A1.
    + rep_iter (aB d) k n C NOV NB BIG K BC A1.
Time Qed.
