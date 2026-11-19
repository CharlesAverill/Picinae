(* strcasecmp_l strncasecmp_l -- locale variants of the case-insensitive
   string comparisons (musl x86_64, C), tail calls into strcasecmp /
   strncasecmp (-> tolower)

   SEMANTICS
   ---------
   musl (src/string/strcasecmp.c, strncasecmp.c):

       int __strcasecmp_l(const char *l, const char *r, locale_t loc)
       { return strcasecmp(l, r); }
       int __strncasecmp_l(const char *l, const char *r, size_t n, locale_t loc)
       { return strncasecmp(l, r, n); }

   Each compiles to a single JMP into the plain function, whose contract
   (strcasecmp_proof.v, strncasecmp_proof.v) is used through tail_leaf_ni
   (lib/x64_tail.v).

   SPECIFICATION (man 3 strcasecmp, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------------
     int strcasecmp_l(const char *s1, const char *s2, locale_t loc);
     int strncasecmp_l(const char *s1, const char *s2, size_t n, locale_t loc);
     Like strcasecmp / strncasecmp, using the given locale; musl's case
     mapping is the C locale's, so the locale is ignored.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcasecmp_l at 0x65944 (-> strcasecmp 0x658e8), strncasecmp_l at
            0x65b34 (-> strncasecmp 0x65ab9), tolower at 0x41924 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/{strcasecmp_l,strncasecmp_l}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = l, RSI = r (RDX = n for strncasecmp_l), next argument the
            ignored locale; m = memory.  Precondition: that of the plain
            function (casecmp_ok / ncase_ok), relative to the wrapper's RSP.
   Output:  At the plain function's RET: exactly its postcondition
            (strcasecmp_post / strncasecmp_post) relative to the wrapper's
            entry state.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcasecmp_l_amd64 CoqEtTu.programs.strncasecmp_l_amd64
               CoqEtTu.programs.strcasecmp_amd64 CoqEtTu.programs.strncasecmp_amd64 CoqEtTu.programs.tolower_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail
               CoqEtTu.lib.x64_ctype.
Require Import CoqEtTu.proofs.ctype_proof CoqEtTu.proofs.strcasecmp_proof CoqEtTu.proofs.strncasecmp_proof.
Open Scope N.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

(* ---- W ---- *)
Definition strcasecmp_l_program : program := updateall2 strcasecmp_l_amd64 strcasecmp_program.

Lemma strcasecmp_l_program_welltyped: welltyped_prog x64typctx strcasecmp_l_program.
Proof.
  intros s a. unfold strcasecmp_l_program, updateall2 at 1, updateall.
  destruct (strcasecmp_program s a) as [[sz q]|] eqn:SL.
    pose proof (strcasecmp_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strcasecmp_l_amd64.welltyped.
Qed.

Lemma strcasecmp_in_W: strcasecmp_amd64 ⊆2 strcasecmp_program.
Proof.
  intros s a insn SC. unfold strcasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strcasecmp_amd64, tolower_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Definition strcasecmp_l_invs (s0:store) (m l r:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165944 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165943 => Some (strcasecmp_post s0 m l r s)
  | _ => None end | _ => None end.

Theorem strcasecmp_l_correct:
  forall prog s t s' x' m l r
         (SUB: strcasecmp_l_amd64 ⊆2 prog) (SUBF: strcasecmp_amd64 ⊆2 prog) (TOLOWER: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165944, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r)
         (OK: casecmp_ok m l r (s R_RSP)),
  satisfies_all prog (strcasecmp_l_invs s m l r) strcasecmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r SUB SUBF TOLOWER ENTRY MDL MEM L R OK.
  eapply satisfies_all_pmono with (p1:=strcasecmp_l_program).
    unfold strcasecmp_l_program, strcasecmp_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strcasecmp_l_invs.
    unfold strcasecmp_l_program, strcasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcasecmp_l_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [L' [R' [RSP CS]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps strcasecmp_l_program _ _ _ _ s2 nil _ ss1 tt1 MDL1 strcasecmp_l_program_welltyped).
  intro MDL2.
  assert (C02: callee_saved_eq s0 s2) by
    (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
  assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM').
  assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
  eapply (tail_leaf_ni strcasecmp_l_program strcasecmp_program _ _ (strcasecmp_invs s2 (s2 V_MEM64) l r) strcasecmp_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold strcasecmp_invs.
    unfold strcasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x'' s''] START'. apply strcasecmp_correct;
      [ apply strcasecmp_in_W | apply subset_updateall2 | exact START' | exact MDL2 | reflexivity
      | (unfold s2; reg; exact L') | (unfold s2; reg; exact R') | (rewrite ?S2M, S2R; exact OK) ].
  - intros a s t' NC X2. unfold strcasecmp_l_invs, strcasecmp_exit in *.
    unfold strcasecmp_program, updateall2, updateall in NC.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold strcasecmp_exit, strcasecmp_l_invs, strcasecmp_invs in *.
    repeat first
    [ discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: split; [reflexivity|]; unfold post_or_true, true_inv, strcasecmp_post.
    all: intros [A [B [D E]]]; rewrite S2M in A, B; rewrite S2R in B, D.
    all: split; [exact A|]; split; [exact B|]; split; [exact D | exact (callee_saved_eq_trans _ _ _ C02 E)].
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold strcasecmp_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.

(* ---- W ---- *)
Definition strncasecmp_l_program : program := updateall2 strncasecmp_l_amd64 strncasecmp_program.

Lemma strncasecmp_l_program_welltyped: welltyped_prog x64typctx strncasecmp_l_program.
Proof.
  intros s a. unfold strncasecmp_l_program, updateall2 at 1, updateall.
  destruct (strncasecmp_program s a) as [[sz q]|] eqn:SL.
    pose proof (strncasecmp_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strncasecmp_l_amd64.welltyped.
Qed.

Lemma strncasecmp_in_W: strncasecmp_amd64 ⊆2 strncasecmp_program.
Proof.
  intros s a insn SC. unfold strncasecmp_program, updateall2, updateall.
  destruct (tolower_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strncasecmp_amd64, tolower_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Definition strncasecmp_l_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165b34 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x165b30 | 0x165b33 => Some (strncasecmp_post s0 m l r n s)
  | _ => None end | _ => None end.

Theorem strncasecmp_l_correct:
  forall prog s t s' x' m l r n
         (SUB: strncasecmp_l_amd64 ⊆2 prog) (SUBF: strncasecmp_amd64 ⊆2 prog) (TOLOWER: tolower_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165b34, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n)
         (OK: ncase_ok l r n (s R_RSP)),
  satisfies_all prog (strncasecmp_l_invs s m l r n) strncasecmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n SUB SUBF TOLOWER ENTRY MDL MEM L R Nn OK.
  eapply satisfies_all_pmono with (p1:=strncasecmp_l_program).
    unfold strncasecmp_l_program, strncasecmp_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strncasecmp_l_invs.
    unfold strncasecmp_l_program, strncasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. apply strncasecmp_l_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [L' [R' [Nd' [RSP CS]]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps strncasecmp_l_program _ _ _ _ s2 nil _ ss1 tt1 MDL1 strncasecmp_l_program_welltyped).
  intro MDL2.
  assert (C02: callee_saved_eq s0 s2) by
    (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
  assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM').
  assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
  eapply (tail_leaf_ni strncasecmp_l_program strncasecmp_program _ _ (strncasecmp_invs s2 (s2 V_MEM64) l r n) strncasecmp_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold strncasecmp_invs.
    unfold strncasecmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x'' s''] START'. apply strncasecmp_correct;
      [ apply strncasecmp_in_W | apply subset_updateall2 | exact START' | exact MDL2 | reflexivity
      | (unfold s2; reg; exact L') | (unfold s2; reg; exact R') | (unfold s2; reg; exact Nd') | (rewrite ?S2M, S2R; exact OK) ].
  - intros a s t' NC X2. unfold strncasecmp_l_invs, strncasecmp_exit in *.
    unfold strncasecmp_program, updateall2, updateall in NC.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold strncasecmp_exit, strncasecmp_l_invs, strncasecmp_invs in *.
    repeat first
    [ discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: split; [reflexivity|]; unfold post_or_true, true_inv, strncasecmp_post.
    all: intros [A [B [D E]]]; rewrite S2M in A, B; rewrite S2R in B, D.
    all: split; [exact A|]; split; [exact B|]; split; [exact D | exact (callee_saved_eq_trans _ _ _ C02 E)].
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold strncasecmp_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.

