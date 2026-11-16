(* srand, rand, rand_r -- pseudo-random number generators (musl x86_64, C)

   SEMANTICS
   ---------
   musl's src/prng/rand.c and rand_r.c are

       static uint64_t seed;
       void srand(unsigned s) { seed = s-1; }
       int rand(void)
       {
           seed = 6364136223846793005ULL*seed + 1;
           return seed>>33;
       }

       static unsigned temper(unsigned x)
       {
           x ^= x>>11;
           x ^= x<<7 & 0x9D2C5680;
           x ^= x<<15 & 0xEFC60000;
           x ^= x>>18;
           return x;
       }
       int rand_r(unsigned *seed)
       {
           return temper( *seed = *seed * 1103515245 + 12345)/2;
       }

   The static seed is the quadword at 0x1a6e78 (Ghidra address).

   SPECIFICATION (man 3 rand, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     int rand(void);  int rand_r(unsigned int *seedp);  void srand(unsigned int seed);
     rand returns a pseudo-random integer in [0, RAND_MAX]; srand sets the
     seed for a new sequence.  rand_r keeps its state in the unsigned int
     *seedp supplied by the caller.  (musl: RAND_MAX = 0x7fffffff.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            srand at 0x5c26e, rand at 0x5c279, rand_r at 0x5c29b (Ghidra
            image base 0x100000: 0x15c26e, 0x15c279, 0x15c29b)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/{srand,rand,rand_r}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   srand:   Input RDI = s (ESI's low 32 bits are the unsigned argument).
            Output at the RET: memory = m with the quadword at 0x1a6e78 set
            to (s - 1) mod 2^32 (s read mod 2^32); RSP and RBX, RBP, R12-R15
            unchanged.
   rand:    Output at the RET: with x = m[0x1a6e78] (64-bit) and
            x' = (6364136223846793005 * x + 1) mod 2^64, memory = m with the
            seed set to x', and RAX = x' >> 33 (< 2^31 = RAND_MAX + 1).
   rand_r:  Input RDI = p.  Output at the RET: with x = (m[p] (32-bit) *
            1103515245 + 12345) mod 2^32, memory = m with the 32-bit word at p
            set to x, and RAX = temper(x) / 2 (< 2^31).
   No preconditions; none of them touches the stack.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.srand_amd64 CoqEtTu.programs.rand_amd64 CoqEtTu.programs.rand_r_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List Btauto.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_signed.
Open Scope N.

Definition seed_addr := 0x1a6e78.

Definition lcg32 (x:N) := (x * 1103515245 + 12345) mod 2^32.

Definition temper (x:N) :=
  let x := N.lxor x (x >> 11) in
  let x := N.lxor x (N.land ((x << 7) mod 2^32) 0x9D2C5680) in
  let x := N.lxor x (N.land ((x << 15) mod 2^32) 0xEFC60000) in
  N.lxor x (x >> 18).

Lemma msub_mod_l: forall w x y, msub w (x mod 2^w) y = msub w x y.
Proof. intros. unfold msub. apply N.add_mod_idemp_l, N.pow_nonzero. discriminate. Qed.

(* IMUL's sign extensions do not change the low 32 bits *)
Lemma scast32_low: forall x, x < 2^32 -> scast 32 64 x mod 2^32 = x.
Proof.
  intros x X. unfold scast, ofZ. rewrite toZ32_cases by exact X.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
  destruct (N.ltb_spec x (2^31)) as [L|L].
  - rewrite Z.mod_small by (change (2^32) with 4294967296 in X; lia).
    rewrite N2Z.id. apply N.mod_small. exact X.
  - replace ((Z.of_N x - 2^32) mod 18446744073709551616)%Z with (Z.of_N (x + 18446744069414584320)).
    + rewrite N2Z.id. rewrite N.add_mod by discriminate.
      change (18446744069414584320 mod 2^32) with 0.
      rewrite N.add_0_r, !N.mod_mod by discriminate. apply N.mod_small. exact X.
    + apply Z.mod_unique with (q := (-1)%Z);
      change (2^32) with 4294967296 in *; change (2^31) with 2147483648 in *; lia.
Qed.

Lemma lcg_low:
  forall x, x < 2^32 -> (12345 + scast 32 64 x * scast 32 64 1103515245) mod 2^32 = lcg32 x.
Proof.
  intros x X. unfold lcg32.
  rewrite N.add_comm, <- N.add_mod_idemp_l, N.mul_mod, !scast32_low by (assumption || discriminate || reflexivity).
  rewrite N.add_mod_idemp_l by discriminate. reflexivity.
Qed.

Lemma low12_bits:
  forall z i, i < 12 -> N.testbit (57 + z) i = N.testbit (12345 + z) i.
Proof.
  intros z i I. rewrite <- (N.mod_pow2_bits_low (57 + z) 12 i I), <- (N.mod_pow2_bits_low (12345 + z) 12 i I).
  f_equal. replace (12345 + z) with (57 + z + 3 * 2^12) by (change (2^12) with 4096; lia).
  symmetry. apply N.Div0.mod_add.
Qed.

(* evaluate closed comparisons and testbits of constants *)
Ltac closed_cmp :=
  repeat match goal with |- context [?a <? ?b] =>
    let v := eval vm_compute in (a <? b) in change (a <? b) with v end;
  repeat match goal with |- context [N.testbit ?c ?k] =>
    lazymatch c with Npos _ =>
      let v := eval vm_compute in (N.testbit c k) in change (N.testbit c k) with v end end;
  cbn [andb orb xorb negb].

(* bitblast over 32 bits, identifying the low bits of B with those of A;
   each bit is closed by btauto (case splitting on the leaves blows up) *)
Ltac bb32 HB :=
  apply N.bits_inj; let i := fresh "i" in intro i;
  let IW := fresh "IW" in
  destruct (N.lt_ge_cases i 32) as [IW|IW];
  [ let rec go k :=
      lazymatch eval compute in (k <? 32) with
      | true => destruct (N.eq_dec i k) as [->|?];
                [ bits_rewrite; bits_norm_idx; closed_cmp;
                  repeat match goal with |- context [N.testbit ?B ?j] =>
                    lazymatch type of HB with context [N.testbit B _] =>
                      rewrite (HB j) by (vm_compute; reflexivity) end end;
                  btauto
                | let k1 := eval compute in (N.succ k) in go k1 ]
      | false => exfalso; lia
      end in go 0
  | bits_rewrite; bits_cases ].

(* ---------- srand ---------- *)

Definition srand_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x15c278 => true | _ => false end | _ => false end.

Definition srand_invs (s0:store) (m:memory) (sd:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15c26e => Some (s V_MEM64 = m /\ s R_RDI mod 2^32 = sd /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x15c278 => Some (s V_MEM64 = m [Ⓠseed_addr := msub 32 sd 1] /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None
  end | _ => None end.

Theorem srand_correct:
  forall prog s t s' x' m sd
         (SRAND: srand_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c26e, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SD: s R_RDI mod 2^32 = sd),
  satisfies_all prog (srand_invs s m sd) srand_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m sd SRAND ENTRY MDL MEM SD.
  eapply satisfies_all_pmono with (p1:=srand_amd64); [exact SRAND| |].
    intros a s1 t1 EXIT NOCODE. unfold srand_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m sd MDL MEM SD START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply srand_amd64.welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [SD [RSP CS]]].
  repeat x64_step.
  split. rewrite <- SD, msub_mod_l. unfold seed_addr. sreflexivity.
  conj_tac.
Qed.

(* ---------- rand ---------- *)

Definition rand_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x15c29a => true | _ => false end | _ => false end.

Definition rand_next (x:N) := (0x5851f42d4c957f2d * x + 1) mod 2^64.

Definition rand_invs (s0:store) (m:memory) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15c279 => Some (s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x15c29a => Some (s V_MEM64 = m [Ⓠseed_addr := rand_next (m Ⓠ[seed_addr])] /\
                      s R_RAX = rand_next (m Ⓠ[seed_addr]) >> 33 /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None
  end | _ => None end.

Theorem rand_correct:
  forall prog s t s' x' m
         (RAND: rand_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c279, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m),
  satisfies_all prog (rand_invs s m) rand_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m RAND ENTRY MDL MEM.
  eapply satisfies_all_pmono with (p1:=rand_amd64); [exact RAND| |].
    intros a s1 t1 EXIT NOCODE. unfold rand_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m MDL MEM START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply rand_amd64.welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [RSP CS]].
  repeat x64_step.
  unfold rand_next, seed_addr.
  split. rewrite <- setmem_mod_r. rewrite (N.add_comm 1). change (2^(8*8)) with (2^64). sreflexivity.
  split. rewrite (N.add_comm 1). sreflexivity.
  conj_tac.
Qed.

(* ---------- rand_r ---------- *)

Definition rand_r_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x15c2d3 => true | _ => false end | _ => false end.


Definition rand_r_invs (s0:store) (m:memory) (p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15c29b => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x15c2d3 => Some (s V_MEM64 = m [Ⓓp := lcg32 (m Ⓓ[p])] /\
                      s R_RAX = temper (lcg32 (m Ⓓ[p])) / 2 /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None
  end | _ => None end.

Theorem rand_r_correct:
  forall prog s t s' x' m p
         (RANDR: rand_r_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c29b, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p),
  satisfies_all prog (rand_r_invs s m p) rand_r_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p RANDR ENTRY MDL MEM P.
  eapply satisfies_all_pmono with (p1:=rand_r_amd64); [exact RANDR| |].
    intros a s1 t1 EXIT NOCODE. unfold rand_r_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p MDL MEM P START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply rand_r_amd64.welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [P [RSP CS]]].
  repeat x64_step.
  pose proof (getmem_bound 64 LittleE 4 m p) as XB. change (2^(4*8)) with (2^32) in XB.
  pose proof (lcg_low _ XB) as LCG.
  pose proof (low12_bits (scast 32 64 (m Ⓓ[p]) * scast 32 64 1103515245)) as HB.
  split. rewrite <- setmem_mod_r. change (2^(4*8)) with (2^32). rewrite LCG. sreflexivity.
  split.
  - rewrite <- LCG. clear LCG.
    set (Z := scast 32 64 (m Ⓓ[p]) * scast 32 64 1103515245) in *. clearbody Z.
    replace (temper ((12345 + Z) mod 2^32) / 2) with (temper ((12345 + Z) mod 2^32) >> 1)
      by (rewrite N.shiftr_div_pow2; reflexivity).
    unfold temper. cbv zeta.
    set (A := 12345 + Z) in *. set (B := 57 + Z) in *. clearbody A B.
    bb32 HB.
  - conj_tac.
Qed.
