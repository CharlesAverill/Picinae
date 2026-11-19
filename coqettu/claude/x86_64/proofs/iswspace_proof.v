(* iswspace iswspace_l -- wide white-space test (musl x86_64, C), composed
   with wcschr (-> wcslen)

   SEMANTICS
   ---------
   musl's iswspace (src/ctype/iswspace.c) is

       int iswspace(wint_t wc)
       {
           static const wchar_t spaces[] = {
               ' ', '\t', '\n', '\r', 11, 12,  0x0085,
               0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005,
               0x2006, 0x2008, 0x2009, 0x200a,
               0x2028, 0x2029, 0x205f, 0x3000, 0 };
           return wc && wcschr(spaces, wc);
       }

   The table is in .rodata at 0x173360 (bytes checked against the binary:
   the 21 words of `spaces` and a 0).  The binary tests wc, then CALLs
   wcschr (0x13c310, call_leaf_ni over wcschr_proof.v) and returns
   RAX != 0.  iswspace_l (0x1418c0) is a JMP into iswspace (tail_leaf_ni).

   SPECIFICATION (man 3 iswspace, Linux man-pages 6.9.1, paraphrased)
   -----------------------------------------------------------------
     int iswspace(wint_t wc);
     iswspace tests whether wc is a wide character of class "space"; here
     the 21 Unicode spaces listed above.  iswspace_l takes an ignored locale.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            iswspace at 0x41899, iswspace_l at 0x418c0, spaces at 0x73360,
            wcschr at 0x3c310, wcslen at 0x3c380 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/{iswspace,iswspace_l}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = wc (w = wc mod 2^32 is used); RSP = rsp; m = memory.
            Precondition (spc_ok): m holds the table at 0x173360 (it is
            read-only data of the binary), and the table's 88 bytes are
            outside the 48 bytes below rsp.
   Output:  At a RET: RAX = 1 if w <> 0 and w is one of the 21 spaces, else
            0 (iswspace_spec); nothing outside the 48 bytes below rsp
            changes; RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.iswspace_amd64 CoqEtTu.programs.iswspace_l_amd64
               CoqEtTu.programs.wcschr_amd64 CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List Bool.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcslen_proof CoqEtTu.proofs.wcschr_proof CoqEtTu.proofs.wcsspn_proof.
Open Scope N.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Definition spaces : list N := [0x20; 0x9; 0xa; 0xd; 0xb; 0xc; 0x85; 0x2000; 0x2001; 0x2002; 0x2003; 0x2004; 0x2005; 0x2006; 0x2008; 0x2009; 0x200a; 0x2028; 0x2029; 0x205f; 0x3000].
Definition TAB := 0x173360.
Definition spc (i:N) : N := nth (N.to_nat i) spaces 0.

Definition iswspace_spec (w:N) : bool := negb (w =? 0) && existsb (N.eqb w) spaces.

Definition spc_ok (m:memory) (rsp:N) :=
  (forall i, i <= 21 -> m Ⓓ[TAB ⊕ 4*i] = spc i) /\ ~ overlap 64 TAB 88 (rsp ⊖ 48) 48.

Lemma lt21: forall i, i < 21 -> i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20.
Proof. intros. lia. Qed.

Lemma spc_nz: forall i, i < 21 -> spc i <> 0.
Proof. intros i I. destruct (lt21 i I) as [H|H]; repeat (destruct H as [H|H]); subst i; discriminate. Qed.

Lemma spc_21: spc 21 = 0.
Proof. reflexivity. Qed.

Lemma spc_mem: forall i, i < 21 -> existsb (N.eqb (spc i)) spaces = true.
Proof. intros i I. destruct (lt21 i I) as [H|H]; repeat (destruct H as [H|H]); subst i; reflexivity. Qed.

Lemma spc_notmem: forall w, (forall i, i < 21 -> spc i <> w) -> existsb (N.eqb w) spaces = false.
Proof.
  intros w NE. apply not_true_iff_false. intro H. cbn [existsb spaces] in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); try discriminate H; apply N.eqb_eq in H; subst w;
  first [exact (NE 0 ltac:(lia) eq_refl) | exact (NE 1 ltac:(lia) eq_refl) | exact (NE 2 ltac:(lia) eq_refl) | exact (NE 3 ltac:(lia) eq_refl) | exact (NE 4 ltac:(lia) eq_refl) | exact (NE 5 ltac:(lia) eq_refl) | exact (NE 6 ltac:(lia) eq_refl) | exact (NE 7 ltac:(lia) eq_refl) | exact (NE 8 ltac:(lia) eq_refl) | exact (NE 9 ltac:(lia) eq_refl) | exact (NE 10 ltac:(lia) eq_refl) | exact (NE 11 ltac:(lia) eq_refl) | exact (NE 12 ltac:(lia) eq_refl) | exact (NE 13 ltac:(lia) eq_refl) | exact (NE 14 ltac:(lia) eq_refl) | exact (NE 15 ltac:(lia) eq_refl) | exact (NE 16 ltac:(lia) eq_refl) | exact (NE 17 ltac:(lia) eq_refl) | exact (NE 18 ltac:(lia) eq_refl) | exact (NE 19 ltac:(lia) eq_refl) | exact (NE 20 ltac:(lia) eq_refl)].
Qed.

Definition iswspace_exit (t:trace) :=
  match t with (Addr a,_)::_ => (a =? 0x14189f) || (a =? 0x1418bf) | _ => false end.

Definition iswspace_post (s0:store) (m w:N) (s:store) :=
  s R_RAX = N.b2n (iswspace_spec (w mod 2^32)) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 48 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition iswspace_invs (s0:store) (m w:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? 0x141899 then Some (s V_MEM64 = m /\ s R_RDI = w /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if (a =? 0x14189f) || (a =? 0x1418bf) then Some (iswspace_post s0 m w s)
    else None
  | _ => None end.

Definition iswspace_program : program := updateall2 iswspace_amd64 wcschr_program.

Lemma iswspace_program_welltyped: welltyped_prog x64typctx iswspace_program.
Proof.
  intros s a. unfold iswspace_program, updateall2 at 1, updateall.
  destruct (wcschr_program s a) as [[sz q]|] eqn:SL.
    pose proof (wcschr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply iswspace_amd64.welltyped.
Qed.

Lemma tab_word: forall (m:memory) rsp v i, ~ overlap 64 TAB 88 (rsp ⊖ 48) 48 -> i <= 21 ->
  (m [Ⓠrsp ⊖ 16 := v]) Ⓓ[TAB ⊕ 4*i] = m Ⓓ[TAB ⊕ 4*i].
Proof.
  intros m rsp v i NOV I. apply getmem_noverlap. intros [x [y [X [Y E]]]].
  apply NOV. exists (4*i + x), (32 + y). split. lia. split. lia. unfold TAB in *. mlia.
Qed.

Lemma frame_16_48: forall (m M:memory) rsp v, stack_frame (m [Ⓠrsp ⊖ 16 := v]) M (rsp ⊖ 16) 32 ->
  stack_frame m M rsp 48.
Proof.
  intros m M rsp v SF b B. rewrite (SF b) by mlia.
  apply (stack_store_frame _ rsp 16 _ b 48); [lia | reflexivity | exact B].
Qed.

Lemma ra16_kept: forall (M M':memory) rsp, stack_frame M M' (rsp ⊖ 16) 32 -> M' Ⓠ[rsp ⊖ 16] = M Ⓠ[rsp ⊖ 16].
Proof.
  intros M M' rsp SF. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
  apply SF. mlia.
Qed.

Lemma tab_nz: forall k, k <= 21 -> (TAB ⊕ 4*k =? 0) = false.
Proof. intros. apply N.eqb_neq. unfold TAB. rewrite N.mod_small by lia. lia. Qed.

Theorem iswspace_correct:
  forall prog s t s' x' m w
         (P0: iswspace_amd64 ⊆2 prog) (P1: wcschr_amd64 ⊆2 prog) (P2: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x141899, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (W: s R_RDI = w) (OK: spc_ok m (s R_RSP)),
  satisfies_all prog (iswspace_invs s m w) iswspace_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m w P0 P1 P2 ENTRY MDL MEM W OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=iswspace_program).
  { unfold iswspace_program, wcschr_program. repeat apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold iswspace_invs, iswspace_exit in *.
    unfold iswspace_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact iswspace_program_welltyped. intro MDL1.
  destruct OK as [TW TOV].
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [W' [RSP CS]]].
  x64_step. x64_step.
  - (* w = 0 *)
    match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into W0 end.
    repeat x64_step.
    rewrite ?N.shiftr_0_r in W0.
    split. unfold iswspace_spec. rewrite W0. reflexivity.
    split. rewrite MEM'. apply stack_frame_refl. conj_tac.
  - match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into WNZ end.
    x64_step. x64_step. x64_step. x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
    apply (models_after_steps iswspace_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 iswspace_program_welltyped).
    intro MDL2.
    assert (S2M: s2 V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := 0x1418b2]) by (unfold s2; reg; first [sreflexivity | (rewrite MEM'; sreflexivity)]).
    assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 16) by (unfold s2; reg; reflexivity).
    assert (S2C: s2 R_RSI = w mod 2^32) by (unfold s2; reg; reflexivity).
    assert (WNZ': w mod 2^32 <> 0) by (rewrite ?N.shiftr_0_r in WNZ; exact WNZ).
    assert (TM: forall i, i <= 21 -> (m [Ⓠs0 R_RSP ⊖ 16 := 0x1418b2]) Ⓓ[TAB ⊕ 4*i] = spc i)
      by (intros i I; rewrite (tab_word m _ _ i TOV I); exact (TW i I)).
    eapply (call_leaf_ni iswspace_program wcschr_program _ _ (wcschr_invs s2 (s2 V_MEM64) TAB (s2 R_RSI)) wcschr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold wcschr_invs.
      unfold wcschr_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x'' s''] START'. apply wcschr_correct;
        [ apply wcschr_in_prog | apply subset_updateall2 | exact START' | exact MDL2 | reflexivity
        | (unfold s2; reg; reflexivity) | reflexivity | idtac ].
      intro H. exfalso. apply WNZ'. rewrite S2C, N.mod_mod in H by discriminate. exact H.
    + intros a s t' NC. unfold iswspace_invs, iswspace_exit.
      unfold wcschr_program, updateall2, updateall in NC.
      destruct (N.eqb_spec a 0x141899) as [->|_]; [exfalso; apply NC; reflexivity|].
      destruct (N.eqb_spec a 0x14189f) as [->|_]; [exfalso; apply NC; reflexivity|].
      destruct (N.eqb_spec a 0x1418bf) as [->|_]; [exfalso; apply NC; reflexivity|].
      split; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold wcschr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' sx t2 ENTRY' UT2 PRE2.
      unfold get_postcondition in PRE2.
      destruct (wcschr_exit _) eqn:EX; [|destruct PRE2].
      unfold wcschr_exit in EX. addr_cases EX.
      all: simpl in PRE2.
      all: rewrite app_assoc.
      all: apply (models_after_steps _ _ _ _ _ sx (t2 ++ tm) _ ss1 tt1 MDL1 iswspace_program_welltyped).
      all: intro MDL3.
      all: destruct PRE2 as [[k [CF RES]] [SF [RSP' CS']]].
      all: rewrite S2M, S2C, N.mod_mod in CF, RES by discriminate.
      all: rewrite S2M in SF. all: rewrite S2R in SF, RSP'.
      all: assert (KL: k <= 21) by
             (destruct (N.le_gt_cases k 21) as [H|H]; [exact H|];
              exfalso; apply (proj1 (CF 21 H)); rewrite (TM 21 ltac:(lia)); reflexivity).
      all: assert (RA: sx V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x1418b2)
             by (rewrite (ra16_kept _ _ _ SF); rewrite getmem_setmem by discriminate; reflexivity).
      all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
      all: unfold s2 in D0, D1, D2, D3, D4, D5. all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
      all: rewrite (TM k KL) in RES.
      all: destruct RES as [[HK RAXv]|[HK [_ RAXv]]].
      all: x64_step; try rewrite RA; repeat x64_step.
      all: split; [| split; [exact (frame_16_48 _ _ _ _ SF) | split; [reflexivity |
             unfold callee_saved_eq; destruct CS as (B0 & B1 & B2 & B3 & B4 & B5);
             repeat split; reg; rewrite ?D0, ?D1, ?D2, ?D3, ?D4, ?D5; reg; sassumption]]].
      all: unfold iswspace_spec; rewrite (proj2 (N.eqb_neq _ _) WNZ'); cbn [negb andb].
      1,3,5: (assert (K21: k < 21) by (destruct (N.lt_ge_cases k 21) as [H|H]; [exact H|];
                exfalso; apply WNZ'; rewrite <- HK; replace k with 21 by lia; reflexivity);
              rewrite tab_nz by exact KL; rewrite <- HK, (spc_mem k K21); reflexivity).
      all: assert (K21: k = 21) by (destruct (N.lt_ge_cases k 21) as [H|H]; [exfalso; exact (spc_nz k H HK) | lia]).
      all: rewrite spc_notmem; [reflexivity |].
      all: intros i I E; apply (proj2 (CF i ltac:(lia))); rewrite (TM i ltac:(lia)); exact E.
Qed.

(* ---- iswspace_l: JMP iswspace ---- *)
Definition iswspace_l_program : program := updateall2 iswspace_l_amd64 iswspace_program.

Lemma iswspace_l_program_welltyped: welltyped_prog x64typctx iswspace_l_program.
Proof.
  intros s a. unfold iswspace_l_program, updateall2 at 1, updateall.
  destruct (iswspace_program s a) as [[sz q]|] eqn:SL.
    pose proof (iswspace_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply iswspace_l_amd64.welltyped.
Qed.

Lemma iswspace_in: iswspace_amd64 ⊆2 iswspace_program.
Proof.
  intros s a insn SC. unfold iswspace_program, wcschr_program, updateall2, updateall.
  destruct (wcslen_amd64 s a) eqn:SL.
  - exfalso. revert SC SL. unfold iswspace_amd64, wcslen_amd64.
    repeat first [ discriminate | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - destruct (wcschr_amd64 s a) eqn:SC2; [|exact SC].
    exfalso. revert SC SC2. unfold iswspace_amd64, wcschr_amd64.
    repeat first [ discriminate | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Definition iswspace_l_invs (s0:store) (m w:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? 0x1418c0 then Some (s V_MEM64 = m /\ s R_RDI = w /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if (a =? 0x14189f) || (a =? 0x1418bf) then Some (iswspace_post s0 m w s)
    else None
  | _ => None end.

Theorem iswspace_l_correct:
  forall prog s t s' x' m w
         (PL: iswspace_l_amd64 ⊆2 prog) (P0: iswspace_amd64 ⊆2 prog) (P1: wcschr_amd64 ⊆2 prog) (P2: wcslen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1418c0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (W: s R_RDI = w) (OK: spc_ok m (s R_RSP)),
  satisfies_all prog (iswspace_l_invs s m w) iswspace_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m w PL P0 P1 P2 ENTRY MDL MEM W OK.
  eapply satisfies_all_pmono with (p1:=iswspace_l_program).
  { unfold iswspace_l_program, iswspace_program, wcschr_program. repeat apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold iswspace_l_invs, iswspace_exit in *.
    unfold iswspace_l_program, iswspace_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact iswspace_l_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [W' [RSP CS]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps iswspace_l_program _ _ _ _ s2 nil _ ss1 tt1 MDL1 iswspace_l_program_welltyped).
  intro MDL2.
  assert (C02: callee_saved_eq s0 s2) by
    (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
  assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM').
  assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
  eapply (tail_leaf_ni iswspace_l_program iswspace_program _ _ (iswspace_invs s2 (s2 V_MEM64) w) iswspace_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold iswspace_invs, iswspace_exit in *.
    unfold iswspace_program, wcschr_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity].
  - intros t' [x'' s''] START'. apply iswspace_correct;
      [ exact iswspace_in | (intros sx ax ix H; apply subset_updateall2; apply wcschr_in_prog, H)
      | (intros sx ax ix H; apply subset_updateall2; unfold wcschr_program; apply subset_updateall2, H)
      | exact START' | exact MDL2 | reflexivity | (unfold s2; reg; exact W') | (rewrite S2M, S2R; exact OK) ].
  - intros a s t' NC X2. unfold iswspace_l_invs, iswspace_exit in *.
    unfold iswspace_program, wcschr_program, updateall2, updateall in NC.
    destruct (N.eqb_spec a 0x1418c0) as [->|_]; [exfalso; apply NC; reflexivity|].
    rewrite X2. split; reflexivity.
  - intros a s t' X2. unfold iswspace_exit in X2. unfold iswspace_l_invs, iswspace_invs, iswspace_exit.
    rewrite X2. destruct (N.eqb_spec a 0x1418c0) as [->|_]; [discriminate X2|].
    destruct (N.eqb_spec a 0x141899) as [->|_]; [discriminate X2|].
    split. reflexivity. unfold post_or_true, true_inv, iswspace_post.
    intros [A [B [D E]]]. rewrite S2M in B. rewrite S2R in B, D.
    split. exact A. split. exact B. split. exact D. exact (callee_saved_eq_trans _ _ _ C02 E).
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold iswspace_exit in X.
    apply orb_true_iff in X. destruct X as [X|X]; apply N.eqb_eq in X; subst a; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.
