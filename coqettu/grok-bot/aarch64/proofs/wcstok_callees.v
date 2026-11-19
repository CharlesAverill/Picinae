(* wcstok: wcsspn and wcscspn proofs (both level 0, sharing wcschr's loop)
   placed at level 1 of the wcstok invariant family (GrokExits, GrokKeep,
   GrokWeaken, GrokCall2).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcstok_armv8 wcsspn_armv8 wcscspn_armv8 wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep GrokWeaken GrokExits GrokCall2.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
From Grok.proofs Require Import wcstok_defs.
Import ARM8Notations.
Open Scope N.

Ltac enum_code IL :=
  unfold wcsspn_proof.wcsspn_prog, wcscspn_proof.wcscspn_prog, updateall2, updateall, wcsspn_armv8.wcsspn_armv8,
    wcscspn_armv8.wcscspn_armv8, wcschr_armv8.wcschr_armv8, wcslen_armv8.wcslen_armv8 in IL;
  match type of IL with context [match ?a with _ => _ end] =>
    destruct a as [|q0]; [discriminate IL|]; repeat (destruct q0 as [q0|q0|]; try discriminate IL) end.

Lemma spn_in_spnprog: wcsspn_armv8.wcsspn_armv8 ⊆2 wcsspn_proof.wcsspn_prog.
Proof. intros s a insn SC. unfold wcsspn_proof.wcsspn_prog, updateall2, updateall, wcschr_armv8.wcschr_armv8.
  unfold wcsspn_armv8.wcsspn_armv8 in SC |- *. contains_tac SC. Qed.

Lemma cspn_in_cspnprog: wcscspn_armv8.wcscspn_armv8 ⊆2 wcscspn_proof.wcscspn_prog.
Proof. intros s a insn SC. unfold wcscspn_proof.wcscspn_prog, updateall2, updateall, wcschr_armv8.wcschr_armv8,
  wcslen_armv8.wcslen_armv8. unfold wcscspn_armv8.wcscspn_armv8 in SC |- *. contains_tac SC. Qed.

Lemma chr_in_cspnprog: wcschr_armv8.wcschr_armv8 ⊆2 wcscspn_proof.wcscspn_prog.
Proof. intros s a insn SC. unfold wcscspn_proof.wcscspn_prog, updateall2, updateall, wcslen_armv8.wcslen_armv8.
  unfold wcschr_armv8.wcschr_armv8 in SC |- *. contains_tac SC. Qed.


Theorem wcsspn_correct_in_wcstok:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k st t xs'
    (ENTRY: startof t xs' = (Addr 0x15fe6c, st)) (MDL: models arm8typctx st)
    (SP: st R_SP = sp - 48) (MEM: st V_MEM64 = wt_M1 sp mem raddr x19 x20 x21 x22 x29) (X30: st R_X30 = 0x160164)
    (X0: st R_X0 = wt_s mem s0 p) (X1: st R_X1 = sep)
    (X19: st R_X19 = wt_s mem s0 p) (X20: st R_X20 = sep) (X21: st R_X21 = p) (X29: st R_X29 = sp - 48)
    (PRE0: wcsspn_proof.wcsspn_pre (sp - 48) (wt_M1 sp mem raddr x19 x20 x21 x22 x29) (wt_s mem s0 p) sep Ls Lc),
  satisfies_all wt_prog (wt_invs1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 0)
                        (wt_exits1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 0) (xs'::t).
Proof.
  intros.
  set (F := invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 0).
  set (G := wcsspn_proof.invs (sp - 48) (wt_M1 sp mem raddr x19 x20 x21 x22 x29) 0x160164 (wt_s mem s0 p) sep
              (wt_s mem s0 p) sep p (sp - 48) Ls Lc).
  unfold wt_invs1, wt_exits1. fold F.
  apply satisfies_all_transfer2 with (p1 := wcsspn_proof.wcsspn_prog) (I1 := make_invs 1 wcsspn_proof.wcsspn_prog F).
  - exact wt_contains_spn.
  - intros a s1 t1 N0. unfold make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 insn IL. unfold make_invs. cbv beta iota. rewrite IL, (wt_contains_spn _ _ _ IL). reflexivity.
  - reflexivity.
  - reflexivity.
  - intros xs1 t1 START. rewrite ENTRY in START.
    apply satisfies_all_weaken with (I1 := make_invs 0 wcsspn_proof.wcsspn_prog G).
    + intros [|[[a|i] s1] t2] H; try reflexivity. revert H. unfold make_invs. cbv beta iota.
      destruct (wcsspn_proof.wcsspn_prog s1 a) eqn:IL; [|reflexivity].
      enum_code IL; simpl; first [discriminate | reflexivity].
    + intros [|[[a|i] s1] t2] P1 H; try discriminate H. revert H. unfold make_invs. cbv beta iota.
      destruct (wcsspn_proof.wcsspn_prog s1 a) eqn:IL; [|discriminate].
      enum_code IL; simpl; intro H; try discriminate H; injection H as <-;
        (eexists; split; [reflexivity | first [exact (fun x => x) | exact (fun x => or_introl x) | exact (fun x => conj x eq_refl)]]).
    + apply satisfies_all_xa with (xp1 := make_exits 0 wcsspn_proof.wcsspn_prog G).
      * intros a s1 t2 insn IL. unfold make_exits. cbv beta iota.
        rewrite IL, (wt_contains_spn _ _ _ IL). enum_code IL; reflexivity.
      * reflexivity.
      * eapply wcsspn_proof.wcsspn_partial_correctness; try eassumption.
        apply spn_in_spnprog. apply subset_updateall2.
Qed.

Lemma cspn_noassign: ∀ mem s0 p k vx, In vx (wt_KC mem s0 p k) -> prog_noassign (fst vx) wcscspn_proof.wcscspn_prog.
Proof. intros mem s0 p k vx IN. destruct IN as [<-|[]]. simpl. prove_noassign. Qed.

Theorem wcscspn_correct_in_wcstok:
  ∀ sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k st t xs'
    (ENTRY: startof t xs' = (Addr 0x15fb44, st)) (MDL: models arm8typctx st)
    (SP: st R_SP = sp - 48) (MEM: st V_MEM64 = wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p)
    (X30: st R_X30 = 0x16017c)
    (X0: st R_X0 = wt_s mem s0 p + 4*k) (X1: st R_X1 = sep)
    (X19: st R_X19 = wt_s mem s0 p) (X20: st R_X20 = sep) (X21: st R_X21 = p) (X29: st R_X29 = sp - 48)
    (X22: st R_X22 = wt_s mem s0 p + 4*k)
    (PRE0: wcscspn_proof.wcscspn_pre (sp - 48) (wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p)
             (wt_s mem s0 p + 4*k) sep (Ls - k) Lc),
  satisfies_all wt_prog (wt_invs1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1)
                        (wt_exits1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1) (xs'::t).
Proof.
  intros.
  set (F := invs sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k 1).
  set (G := wcscspn_proof.invs (sp - 48) (wt_W1 sp mem raddr x19 x20 x21 x22 x29 s0 sep p) 0x16017c
              (wt_s mem s0 p + 4*k) sep (wt_s mem s0 p) sep p (sp - 48) (Ls - k) Lc).
  unfold wt_invs1, wt_exits1. fold F.
  apply satisfies_all_transfer2 with (p1 := wcscspn_proof.wcscspn_prog) (I1 := make_invs 1 wcscspn_proof.wcscspn_prog F).
  - exact wt_contains_cspn.
  - intros a s1 t1 N0. unfold make_invs. rewrite N0. reflexivity.
  - intros a s1 t1 insn IL. unfold make_invs. cbv beta iota. rewrite IL, (wt_contains_cspn _ _ _ IL). reflexivity.
  - reflexivity.
  - reflexivity.
  - intros xs1 t1 START. rewrite ENTRY in START.
    apply satisfies_all_weaken with (I1 := keepl_invs (make_invs 0 wcscspn_proof.wcscspn_prog G) (wt_KC mem s0 p k)).
    + intros [|[[a|i] s1] t2] H; try reflexivity. revert H. unfold keepl_invs, make_invs. cbv beta iota.
      destruct (wcscspn_proof.wcscspn_prog s1 a) eqn:IL; [|reflexivity].
      enum_code IL; simpl; first [discriminate | reflexivity].
    + intros [|[[a|i] s1] t2] P1 H; try discriminate H. revert H. unfold keepl_invs, make_invs. cbv beta iota.
      destruct (wcscspn_proof.wcscspn_prog s1 a) eqn:IL; [|discriminate].
      enum_code IL; simpl; intro H; try discriminate H; injection H as <-;
        (eexists; split; [reflexivity | first [exact (fun x => x) | exact (fun x => or_intror x) | exact (fun x => conj x eq_refl)]]).
    + apply satisfies_all_xa with (xp1 := make_exits 0 wcscspn_proof.wcscspn_prog G).
      * intros a s1 t2 insn IL. unfold make_exits. cbv beta iota.
        rewrite IL, (wt_contains_cspn _ _ _ IL). enum_code IL; reflexivity.
      * reflexivity.
      * apply (satisfies_all_keepl _ _ _ (wt_KC mem s0 p k) (cspn_noassign mem s0 p k) xs1 t1).
        -- rewrite START. simpl. split; [exact X22 | exact I].
        -- intros xs2 t2 START2. rewrite START in START2.
           eapply wcscspn_proof.wcscspn_partial_correctness; try eassumption.
           apply cspn_in_cspnprog. apply chr_in_cspnprog. apply subset_updateall2.
        -- reflexivity.
Qed.
