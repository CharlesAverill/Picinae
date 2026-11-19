(* ldiv lldiv imaxdiv -- integer division with remainder (musl x86_64, C)

   SEMANTICS
   ---------
   musl (src/stdlib/div.c etc.):  div_t div(int num, int den)
   { return (div_t){ num/den, num%den }; }  and likewise for long, long long
   and intmax_t.  ldiv/lldiv/imaxdiv compile to MOV RAX,RDI; CQO; IDIV RSI;
   RET (quotient in RAX, remainder in RDX).  (div, the int version, packs
   both ints into RAX after CDQ; IDIV ESI; its proof script works but the
   kernel check of the symbolic IDIV/SHL steps does not finish in 40 min,
   see ROADMAP.)

   SPECIFICATION (man 3 div, Linux man-pages 6.9.1, paraphrased)
   ------------------------------------------------------------
     div_t div(int numerator, int denominator);
     The div() function computes the value numerator/denominator and returns
     the quotient and remainder in a structure; the quotient is rounded
     toward zero (C99), and quot * denominator + rem = numerator.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            imaxdiv at 0x64ff6, ldiv at 0x6500a, lldiv at 0x6501e (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/{ldiv,lldiv,imaxdiv}_amd64.v.
            IDIV is lifted as 128-bit SDIVIDE/SMOD, i.e.
            Z.quot/Z.rem; the #DE fault (den = 0 or quotient overflow) is not
            modeled, so the results below are meaningful under C's
            precondition den <> 0 and no overflow (num = MIN, den = -1).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = num, RSI = den (the low 32 bits for div).
   Output:  At the RET: ldiv/lldiv/imaxdiv: RAX = Z.quot num den and RDX =
            Z.rem num den as 64-bit two's complement values (toZ 64).
            RSP and RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.ldiv_amd64
               CoqEtTu.programs.lldiv_amd64 CoqEtTu.programs.imaxdiv_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Lemma lor_shl: forall a n k, n < 2^k -> N.lor (N.shiftl a k) n = a * 2^k + n.
Proof.
  intros a n k NB. rewrite <- N.lxor_lor, <- N.add_nocarry_lxor, N.shiftl_mul_pow2; [reflexivity| |].
  all: apply N.bits_inj_0; intro i; rewrite N.land_spec;
       destruct (N.lt_ge_cases i k) as [I|I];
       [ rewrite N.shiftl_spec_low by exact I; reflexivity
       | destruct (N.eq_dec n 0) as [->|NZ]; [rewrite N.bits_0; apply Bool.andb_false_r|];
         rewrite (N.bits_above_log2 n i); [apply Bool.andb_false_r|];
         apply (N.log2_lt_pow2 n i); [lia|]; apply (N.lt_le_trans _ _ _ NB); apply N.pow_le_mono_r; lia ].
Qed.

Lemma ofZ_hi_lo: forall w z, ofZ (w + w) z mod 2^w = ofZ w z.
Proof.
  intros w z. unfold ofZ.
  replace (2^w) with (Z.to_N (2^Z.of_N w)) by (rewrite Z2N.inj_pow by lia; rewrite N2Z.id; reflexivity).
  rewrite <- Z2N.inj_mod by (try apply Z.mod_pos_bound; lia).
  f_equal. apply Z.mod_mod_divide. rewrite N2Z.inj_add, Z.pow_add_r by lia. exists (2^Z.of_N w)%Z. reflexivity.
Qed.

Lemma toZ_scast_up: forall w w' n, w <= w' -> toZ w' (scast w w' n) = toZ w n.
Proof.
  intros w w' n LE. unfold scast. rewrite (toZ_ofZ_canonicalZ w' w') by lia.
  apply (canonicalZ_id w). rewrite N2Z.id. exact LE.
  apply canonicalZ_bounds.
Qed.

Lemma scast_64_128: forall n, n < 2^64 -> scast 64 128 n = if n <? 2^63 then n else n + (2^128 - 2^64).
Proof.
  intros n NB. unfold scast, toZ, ofZ, canonicalZ. change (Z.pred (Z.of_N 64)) with 63%Z.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (2 ^ 63)%Z with 9223372036854775808%Z.
  change (2 ^ Z.of_N 128)%Z with 340282366920938463463374607431768211456%Z.
  change (2^64) with 18446744073709551616 in *. change (2^63) with 9223372036854775808.
  change (2^128) with 340282366920938463463374607431768211456.
  destruct (N.ltb_spec n 9223372036854775808) as [H|H].
  - rewrite (Z.mod_small (Z.of_N n + 9223372036854775808)) by lia.
    replace (Z.of_N n + 9223372036854775808 - 9223372036854775808)%Z with (Z.of_N n) by lia.
    rewrite Z.mod_small by lia. apply N2Z.id.
  - rewrite <- (Z.mod_unique (Z.of_N n + 9223372036854775808) 18446744073709551616 1
              (Z.of_N n + 9223372036854775808 - 18446744073709551616)) by lia.
    rewrite <- (Z.mod_unique (Z.of_N n + 9223372036854775808 - 18446744073709551616 - 9223372036854775808)
              340282366920938463463374607431768211456 (-1)
              (Z.of_N n + 340282366920938463463374607431768211456 - 18446744073709551616)) by lia.
    lia.
Qed.

Lemma cqo_join: forall n, n < 2^64 ->
  N.lor (((N.shiftr (scast 64 128 n) 64) mod 2^64 << 64) mod 2^128) n = scast 64 128 n.
Proof.
  intros n NB. rewrite (scast_64_128 n NB). destruct (n <? 2^63).
  - rewrite N.shiftr_div_pow2, N.div_small by exact NB. reflexivity.
  - rewrite N.shiftr_div_pow2.
    replace (n + (2^128 - 2^64)) with (n + (2^64 - 1) * 2^64) by reflexivity.
    rewrite N.div_add by discriminate. rewrite N.div_small by exact NB.
    change ((0 + (2^64 - 1)) mod 2^64) with (2^64 - 1).
    rewrite (N.mod_small (N.shiftl _ 64)) by (rewrite N.shiftl_mul_pow2; reflexivity).
    rewrite lor_shl by exact NB. lia.
Qed.

Lemma ofZ_lt: forall w z, ofZ w z < 2^w.
Proof.
  intros. unfold ofZ. apply N2Z.inj_lt. rewrite Z2N.id by (apply Z.mod_pos_bound; lia).
  rewrite N2Z.inj_pow. apply Z.mod_pos_bound. lia.
Qed.

Definition div_exit (a:N) (t:trace) :=
  match t with (Addr a',_)::_ => a' =? a | _ => false end.

Definition div64_invs (e x:N) (s0:store) (n d:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s R_RDI = n /\ s R_RSI = d /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if a =? x then Some (s R_RAX = ofZ 64 (Z.quot (toZ 64 n) (toZ 64 d)) /\
                              s R_RDX = ofZ 64 (Z.rem (toZ 64 n) (toZ 64 d)) /\
                              s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Ltac div_tac prog_lemma :=
  intros;
  match goal with ENTRY: startof _ _ = _, MDL: models _ ?s, Nn: ?s R_RDI = ?n, D: ?s R_RSI = ?d |- _ =>
    assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDI 64); reflexivity);
    assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RSI 64); reflexivity)
  end;
  eapply satisfies_all_pmono; [eassumption| |];
  [ intros a s1 t1 EXIT NOCODE; unfold div64_invs, div_exit in *;
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]
  | ];
  match goal with ENTRY: startof _ _ = _ |- _ =>
    intros [x1 s1] t1 START; rewrite ENTRY in START end;
  apply prove_invs;
  [ simpl; match goal with START: startof _ _ = _ |- _ => rewrite START end;
    x64_step; conj_tac; apply callee_saved_eq_refl
  | intros tt1 aa1 ss1 tt2 UT SPL PRE;
    match goal with START: startof _ _ = _ |- _ => erewrite startof_prefix in START; try eassumption end;
    eapply models_at_invariant; try eassumption; [exact prog_lemma|]; intro MDL1;
    match goal with H: true_inv (get_precondition _ _ _ _ _ _) |- _ => destruct_inv 64 H; rename H into PRE end ].

Theorem ldiv_correct:
  forall prog s t s' x' n d (P: ldiv_amd64.ldiv_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x16500a, s)) (MDL: models x64typctx s)
         (Nn: s R_RDI = n) (D: s R_RSI = d),
  satisfies_all prog (div64_invs 0x16500a 0x165012 s n d) (div_exit 0x165012) ((x',s')::t).
Proof.
  div_tac ldiv_amd64.welltyped.
  destruct PRE as [Nn' [D' [RSP CS]]]. repeat x64_step.
  rewrite cqo_join by exact NB. unfold sbop2. rewrite !toZ_scast_up by discriminate.
  split. apply (ofZ_hi_lo 64). split. apply (ofZ_hi_lo 64). conj_tac.
Qed.

Theorem lldiv_correct:
  forall prog s t s' x' n d (P: lldiv_amd64.lldiv_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x16501e, s)) (MDL: models x64typctx s)
         (Nn: s R_RDI = n) (D: s R_RSI = d),
  satisfies_all prog (div64_invs 0x16501e 0x165026 s n d) (div_exit 0x165026) ((x',s')::t).
Proof.
  div_tac lldiv_amd64.welltyped.
  destruct PRE as [Nn' [D' [RSP CS]]]. repeat x64_step.
  rewrite cqo_join by exact NB. unfold sbop2. rewrite !toZ_scast_up by discriminate.
  split. apply (ofZ_hi_lo 64). split. apply (ofZ_hi_lo 64). conj_tac.
Qed.

Theorem imaxdiv_correct:
  forall prog s t s' x' n d (P: imaxdiv_amd64.imaxdiv_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x164ff6, s)) (MDL: models x64typctx s)
         (Nn: s R_RDI = n) (D: s R_RSI = d),
  satisfies_all prog (div64_invs 0x164ff6 0x164ffe s n d) (div_exit 0x164ffe) ((x',s')::t).
Proof.
  div_tac imaxdiv_amd64.welltyped.
  destruct PRE as [Nn' [D' [RSP CS]]]. repeat x64_step.
  rewrite cqo_join by exact NB. unfold sbop2. rewrite !toZ_scast_up by discriminate.
  split. apply (ofZ_hi_lo 64). split. apply (ofZ_hi_lo 64). conj_tac.
Qed.
