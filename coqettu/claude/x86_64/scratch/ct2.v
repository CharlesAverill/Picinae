Require Import Picinae_amd64.
Require Import CoqEtTu.programs.isalpha_amd64.
Require Import CoqEtTu.programs.isdigit_amd64.
Require Import CoqEtTu.programs.isalnum_amd64.
Require Import CoqEtTu.programs.isupper_amd64.
Require Import CoqEtTu.programs.islower_amd64.
Require Import CoqEtTu.programs.isspace_amd64.
Require Import CoqEtTu.programs.isxdigit_amd64.
Require Import CoqEtTu.programs.isprint_amd64.
Require Import CoqEtTu.programs.isgraph_amd64.
Require Import CoqEtTu.programs.iscntrl_amd64.
Require Import CoqEtTu.programs.isblank_amd64.
Require Import CoqEtTu.programs.isascii_amd64.
Require Import CoqEtTu.programs.toupper_amd64.
Require Import CoqEtTu.programs.tolower_amd64.
Require Import CoqEtTu.programs.toascii_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_ctype.
Open Scope N.

(* Close a classification goal: case on every test and refute or compute. *)
Ltac ct_split :=
  ctype_cases;
  repeat match goal with |- context [N.b2n ?b] =>
    lazymatch b with true => fail | false => fail | _ => destruct b eqn:? end end;
  ctype_cases;
  cbn [N.lor N.b2n orb andb Pos.lor] in *.
Ltac ct_close :=
  first [ reflexivity
        | exfalso; unfold msub in *; change (2^32) with 4294967296 in *; lia
        | unfold msub in *; change (2^32) with 4294967296 in *; lia ].
Ltac ct_finish := ct_split; ct_close.

(* Normalize (x | 32) and msub 32 (x | 32) _ to the low 32 bits y of x. *)
Ltac or32_prep x :=
  repeat rewrite lor_mod32 by reflexivity;
  repeat match goal with |- context [msub 32 (x .| 32) ?k] =>
    rewrite <- (msub_mod_l 32 32 (x .| 32) k) by reflexivity; rewrite lor_mod32 by reflexivity end;
  repeat match goal with H: context [msub 32 (x .| 32) ?k] |- _ =>
    rewrite <- (msub_mod_l 32 32 (x .| 32) k) in H by reflexivity; rewrite lor_mod32 in H by reflexivity end;
  repeat match goal with H: context [(x .| 32) mod 2^32] |- _ => rewrite lor_mod32 in H by reflexivity end;
  let Y := fresh "Y" in
  assert (Y: x mod 2^32 < 2^32) by (apply N.mod_lt; discriminate);
  pose proof (lor32_lt _ Y);
  pose proof (or32_range (x mod 2^32) 122 (or_introl eq_refl));
  pose proof (or32_range (x mod 2^32) 102 (or_intror eq_refl));
  destruct (N.lt_ge_cases (x mod 2^32) 256);
  [| match goal with H: 256 <= x mod 2^32 |- _ => pose proof (lor_ge256 _ 32 H) end].

(* ---- toupper ---- *)
Definition toupper_spec (y:N) := if inr 97 122 y then y - 32 else y.

Theorem toupper_nwc: forall s2 s1, toupper_amd64 s1 = toupper_amd64 s2.
Proof. reflexivity. Qed.

Theorem toupper_welltyped: welltyped_prog x64typctx toupper_amd64.
Proof. exact toupper_amd64.welltyped. Qed.

Theorem toupper_preserves_memory:
  forall_endstates toupper_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition toupper_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x141946 => true | _ => false end | _ => false end.

Definition toupper_invs (s0:store) (c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x141938 => Some (s R_RDI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x141946 => Some (s R_RAX = toupper_spec (c mod 2^32) /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None end | _ => None end.

Theorem toupper_correct:
  forall prog s t s' x' c
         (SUB: toupper_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x141938, s))
         (MDL: models x64typctx s) (C: s R_RDI = c),
  satisfies_all prog (toupper_invs s c) toupper_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' c SUB ENTRY MDL C.
  eapply satisfies_all_pmono with (p1:=toupper_amd64); [exact SUB| |].
    intros a s1 t1 EXIT NOCODE. unfold toupper_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 c MDL C START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply toupper_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [RDI [RSP CS]].
  repeat x64_step. all: bc_norm.
  all: split; [|conj_tac].
  all: unfold toupper_spec, inr.
  all: try rewrite (land_mod32 c 95) by reflexivity.
  all: try (rewrite <- N.land_assoc; change (95 .& 18446744069414584320) with 0;
            rewrite N.land_0_r, N.lor_0_r).
  all: ct_split.
  all: try (exfalso; unfold msub in *; change (2^32) with 4294967296 in *; lia).
  all: try reflexivity.
  all: rewrite and95_lower by (unfold msub in *; change (2^32) with 4294967296 in *; lia); reflexivity.
Qed.

(* ---- tolower ---- *)
Definition tolower_spec (y:N) := if inr 65 90 y then y + 32 else y.

Theorem tolower_nwc: forall s2 s1, tolower_amd64 s1 = tolower_amd64 s2.
Proof. reflexivity. Qed.

Theorem tolower_welltyped: welltyped_prog x64typctx tolower_amd64.
Proof. exact tolower_amd64.welltyped. Qed.

Theorem tolower_preserves_memory:
  forall_endstates tolower_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition tolower_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x141932 => true | _ => false end | _ => false end.

Definition tolower_invs (s0:store) (c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x141924 => Some (s R_RDI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x141932 => Some (s R_RAX = tolower_spec (c mod 2^32) /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None end | _ => None end.

Theorem tolower_correct:
  forall prog s t s' x' c
         (SUB: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x141924, s))
         (MDL: models x64typctx s) (C: s R_RDI = c),
  satisfies_all prog (tolower_invs s c) tolower_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' c SUB ENTRY MDL C.
  eapply satisfies_all_pmono with (p1:=tolower_amd64); [exact SUB| |].
    intros a s1 t1 EXIT NOCODE. unfold tolower_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 c MDL C START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply tolower_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [RDI [RSP CS]].
  repeat x64_step. all: bc_norm.
  all: split; [|conj_tac].
  all: unfold tolower_spec, inr.
  all: try rewrite lor_mod32 by reflexivity.
  all: try (rewrite <- N.land_assoc; change (32 .& 18446744069414584320) with 0).
  all: ct_split.
  all: try (exfalso; unfold msub in *; change (2^32) with 4294967296 in *; lia).
  all: try reflexivity.
  all: try (rewrite or32_upper by (unfold msub in *; change (2^32) with 4294967296 in *; lia); reflexivity).
  all: rewrite land_high32, N.lor_0_r by (apply lor32_lt, N.mod_lt; discriminate); reflexivity.
Qed.

(* ---- toascii ---- *)
Definition toascii_spec (y:N) := y mod 128.

Theorem toascii_nwc: forall s2 s1, toascii_amd64 s1 = toascii_amd64 s2.
Proof. reflexivity. Qed.

Theorem toascii_welltyped: welltyped_prog x64typctx toascii_amd64.
Proof. exact toascii_amd64.welltyped. Qed.

Theorem toascii_preserves_memory:
  forall_endstates toascii_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Definition toascii_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 0x141923 => true | _ => false end | _ => false end.

Definition toascii_invs (s0:store) (c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x14191e => Some (s R_RDI = c /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x141923 => Some (s R_RAX = toascii_spec (c mod 2^32) /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | _ => None end | _ => None end.

Theorem toascii_correct:
  forall prog s t s' x' c
         (SUB: toascii_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x14191e, s))
         (MDL: models x64typctx s) (C: s R_RDI = c),
  satisfies_all prog (toascii_invs s c) toascii_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' c SUB ENTRY MDL C.
  eapply satisfies_all_pmono with (p1:=toascii_amd64); [exact SUB| |].
    intros a s1 t1 EXIT NOCODE. unfold toascii_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 c MDL C START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply toascii_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [RDI [RSP CS]].
  repeat x64_step. all: bc_norm.
  all: split; [|conj_tac].
  all: unfold toascii_spec, inr.
  all: change 128 with (2^7); rewrite mp2_mod_mod_min; reflexivity.
Qed.
