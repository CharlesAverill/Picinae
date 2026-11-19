From Stdlib Require Import NArith Lia FunctionalExtensionality.
Require Import Picinae_armv7.
From Picinae.coqettu.kimi.armv7 Require Import
  division_program signed_div_spec signed_div_stages signed_div_entry.
Import ARM7Notations.
Open Scope N.
Open Scope bool.

Definition signed_div_frame (s0 s : store) : Prop :=
  s V_MEM32 = s0 V_MEM32 /\ s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR /\ s R_R4 = s0 R_R4.

Definition signed_div_post (s0 s : store) : Prop :=
  s R_R0 = signed_quotient (s0 R_R0) (s0 R_R1) /\ signed_div_frame s0 s.

Definition signed_div_sign_pre (cs ps s : store) : Prop :=
  exists q r, unsigned_div_post cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) q r s /\
    s R_R12 = quotient_sign (ps R_R0) (ps R_R1) /\ signed_div_frame ps s.

Definition signed_div_setup (ps s : store) : Prop :=
  s R_R0 = ps R_R0 /\
  s R_R1 = magnitude (ps R_R1) /\
  s R_R2 = magnitude (ps R_R1) ⊖ 1 /\
  s R_R12 = N.lxor (ps R_R0) (ps R_R1) /\
  s R_ZF = (if magnitude (ps R_R1) ⊖ 1 =? 0 then 1 else 0) /\
  signed_div_frame ps s.

Definition signed_div_compare (ps s : store) : Prop :=
  s R_R0 = ps R_R0 /\
  s R_R1 = magnitude (ps R_R1) /\
  s R_R2 = magnitude (ps R_R1) ⊖ 1 /\
  s R_R3 = magnitude (ps R_R0) /\
  s R_R12 = N.lxor (ps R_R0) (ps R_R1) /\
  s R_CF = (if magnitude (ps R_R1) <=? magnitude (ps R_R0) then 1 else 0) /\
  s R_ZF = (if magnitude (ps R_R0) =? magnitude (ps R_R1) then 1 else 0) /\
  signed_div_frame ps s.

Definition divmod_pushmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
      ((s0 R_SP) ⊖ 8) (s0 R_R1))
    ((s0 R_SP) ⊖ 12) (s0 R_R0).

Definition divmod_post (s0 s : store) : Prop :=
  s R_R0 = signed_quotient (s0 R_R0) (s0 R_R1) /\
  s R_R1 = signed_remainder (s0 R_R0) (s0 R_R1) /\
  s V_MEM32 = divmod_pushmem s0 /\ s R_SP = s0 R_SP /\
  s R_LR = s0 R_LR /\ s R_R4 = s0 R_R4.

Definition div_pushmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (s0 V_MEM32) ((s0 R_SP) ⊖ 4) (s0 R_LR))
    ((s0 R_SP) ⊖ 8) (s0 R_R4).

Definition div_callmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4 (div_pushmem s0)
        (((s0 R_SP) ⊖ 8) ⊖ 4) 0x5a5c5)
      (((s0 R_SP) ⊖ 8) ⊖ 8) (s0 R_R2))
    (((s0 R_SP) ⊖ 8) ⊖ 12) (s0 R_R1).

Definition div_finalmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (div_callmem s0) (s0 R_R0)
      (signed_quotient (s0 R_R1) (s0 R_R2)))
    (4 + s0 R_R0) (signed_remainder (s0 R_R1) (s0 R_R2)).

Definition div_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s V_MEM32 = div_finalmem s0 /\
  s R_SP = (s0 R_SP) ⊖ 8 /\ s R_LR = 0x5a5c5.

Definition ldiv_pushmem (s0 : store) : memory := div_pushmem s0.

Definition ldiv_callmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4
      (setmem 32 LittleE 4 (ldiv_pushmem s0)
        (((s0 R_SP) ⊖ 8) ⊖ 4) 0x5a617)
      (((s0 R_SP) ⊖ 8) ⊖ 8) (s0 R_R2))
    (((s0 R_SP) ⊖ 8) ⊖ 12) (s0 R_R1).

Definition ldiv_finalmem (s0 : store) : memory :=
  setmem 32 LittleE 4
    (setmem 32 LittleE 4 (ldiv_callmem s0) (s0 R_R0)
      (signed_quotient (s0 R_R1) (s0 R_R2)))
    (4 + s0 R_R0) (signed_remainder (s0 R_R1) (s0 R_R2)).

Definition ldiv_post (s0 s : store) : Prop :=
  s R_R0 = s0 R_R0 /\ s V_MEM32 = ldiv_finalmem s0 /\
  s R_SP = (s0 R_SP) ⊖ 8 /\ s R_LR = 0x5a617.

Definition signed_div_family (cs ps : store) : invariant_set :=
  fun T Inv Post NoInv s a =>
  match a with
  | 0x3046e => Inv 1 (s = ps)
  | 0x30478 => Inv 1 (signed_div_setup ps s)
  | 0x30484 => Inv 1 (signed_div_compare ps s)
  | 0x304b0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 31 q r s)
  | 0x304c0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 30 q r s)
  | 0x304d0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 29 q r s)
  | 0x304e0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 28 q r s)
  | 0x304f0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 27 q r s)
  | 0x30500 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 26 q r s)
  | 0x30510 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 25 q r s)
  | 0x30520 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 24 q r s)
  | 0x30530 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 23 q r s)
  | 0x30540 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 22 q r s)
  | 0x30550 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 21 q r s)
  | 0x30560 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 20 q r s)
  | 0x30570 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 19 q r s)
  | 0x30580 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 18 q r s)
  | 0x30590 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 17 q r s)
  | 0x305a0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 16 q r s)
  | 0x305b0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 15 q r s)
  | 0x305c0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 14 q r s)
  | 0x305d0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 13 q r s)
  | 0x305e0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 12 q r s)
  | 0x305f0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 11 q r s)
  | 0x30600 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 10 q r s)
  | 0x30610 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 9 q r s)
  | 0x30620 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 8 q r s)
  | 0x30630 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 7 q r s)
  | 0x30640 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 6 q r s)
  | 0x30650 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 5 q r s)
  | 0x30660 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 4 q r s)
  | 0x30670 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 3 q r s)
  | 0x30680 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 2 q r s)
  | 0x30690 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 1 q r s)
  | 0x306a0 => Inv 0 (exists q r, unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) 0 q r s)
  | 0x306b0 => Post 0 (exists q r, unsigned_div_post cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) q r s)
  | 0x306b8 => Post 1 (signed_div_post ps s)
  | 0x306c2 => Post 1 (signed_div_post ps s)
  | 0x306d2 => Post 1 (signed_div_post ps s)
  | 0x306e8 => Post 1 (signed_div_post ps s)
  | 0x306fc => Inv 2 (s = ps)
  | 0x30712 => Post 2 (divmod_post ps s)
  | 0x5a5b8 => Inv 3 (s = ps)
  | 0x5a5ca => Post 3 (div_post ps s)
  | 0x5a60a => Inv 4 (s = ps)
  | 0x5a61c => Post 4 (ldiv_post ps s)
  | _ => NoInv
  end.

Lemma signed_stage_invs (cs ps : store) (t : trace) :
  make_invs 0 division_program (signed_div_family cs ps) t =
  unsigned_div_invs cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) t.
Proof.
  unfold make_invs, signed_div_family, unsigned_div_invs.
  destruct t as [|[[a|i] s] t]; try reflexivity.
  repeat first [ reflexivity |
    match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  all: match goal with
    |- context [division_program ?st ?a] =>
      destruct (division_program st a); reflexivity
  end.
Qed.

Lemma signed_stage_exits (cs ps : store) (t : trace) :
  make_exits 0 division_program (signed_div_family cs ps) t =
  unsigned_div_exit t.
Proof.
  unfold make_exits, signed_div_family, unsigned_div_exit.
  destruct t as [|[[a|i] s] t]; try reflexivity.
  repeat first [ reflexivity |
    match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  all: match goal with
    |- context [division_program ?st ?a] =>
      destruct (division_program st a); reflexivity
  end.
Qed.

Theorem unsigned_div_family_correct :
  forall cs ps k q r t xs
    (ENTRY : startof t xs = (Addr (divstage_addr k), cs))
    (MDL : models arm7typctx cs)
    (K31 : k <= 31)
    (PRE : unsigned_div_stage cs (magnitude (ps R_R0)) (magnitude (ps R_R1)) k q r cs),
  satisfies_all division_program
    (make_invs 0 division_program (signed_div_family cs ps))
    (make_exits 0 division_program (signed_div_family cs ps)) (xs :: t).
Proof.
  intros.
  assert (HI : make_invs 0 division_program (signed_div_family cs ps) =
    unsigned_div_invs cs (magnitude (ps R_R0)) (magnitude (ps R_R1))).
  { extensionality tr. apply signed_stage_invs. }
  assert (HE : make_exits 0 division_program (signed_div_family cs ps) =
    unsigned_div_exit).
  { extensionality tr. apply signed_stage_exits. }
  rewrite HI, HE.
  exact (unsigned_div_stages_correct division_program (fun s a x H => H)
    cs (magnitude (ps R_R0)) (magnitude (ps R_R1))
    k q r t xs ENTRY MDL K31 PRE).
Qed.
