(* wcscoll_l -- compare two wide strings in a locale (musl x86_64, C), a
   tail call into wcscmp

   SEMANTICS
   ---------
   musl's __wcscoll_l (src/locale/wcscoll.c), exported as wcscoll_l, is

       int __wcscoll_l(const wchar_t *l, const wchar_t *r, locale_t loc)
       {
           return wcscmp(l, r);
       }

   compiled to a single JMP wcscmp (0x134b20).  wcscmp's contract
   (wcscmp_proof.v) is used through tail_leaf (lib/x64_tail.v).  (wcscoll
   itself first loads the thread's locale through FS:[0]; the shared lifter
   does not model FS, which leaves its lift ill-typed, so wcscoll is not
   proved here: scratch/wcscoll_amd64.v.bad.)

   SPECIFICATION (man 3 wcscoll, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     int wcscoll_l(const wchar_t *s1, const wchar_t *s2, locale_t locale);
     wcscoll compares s1 and s2 according to the collation of the locale;
     in the "POSIX" or "C" locale it is equivalent to wcscmp.  musl only
     has code-point collation, so the result is wcscmp's for every locale.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            __wcscoll_l (wcscoll_l) at 0x4642d, wcscmp at 0x34b20 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/wcscoll_l_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = l, RSI = r (RDX = locale, ignored); m = memory.  No
            precondition.
   Output:  At wcscmp's RET (0x134b61), which returns to wcscoll_l's caller:
            wcscmp_post: RAX = -1/0/1 (wcmp) at wcscmp's stop index K; memory unchanged; RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcscoll_l_amd64 CoqEtTu.programs.wcscmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.wcscmp_proof.
Open Scope N.

Definition wcscoll_l_program : program := updateall2 wcscoll_l_amd64 wcscmp_amd64.

Theorem wcscoll_l_welltyped: welltyped_prog x64typctx wcscoll_l_amd64.
Proof. exact wcscoll_l_amd64.welltyped. Qed.

Lemma wcscoll_l_program_welltyped: welltyped_prog x64typctx wcscoll_l_program.
Proof.
  intros s a. unfold wcscoll_l_program, updateall2, updateall.
  destruct (wcscmp_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (wcscmp_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply wcscoll_l_welltyped.
Qed.

Definition wcscoll_l_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134b61 => true
  | _ => false end | _ => false end.

Definition wcscoll_l_invs (s0:store) (m l r:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x14642d => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134b61 => Some (wcscmp_post s0 m l r s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem wcscoll_l_correct:
  forall prog s t s' x' m l r
         (WCSCOLL_L: wcscoll_l_amd64 ⊆2 prog) (WCSCMP: wcscmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x14642d, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r),
  satisfies_all prog (wcscoll_l_invs s m l r) wcscoll_l_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r WCSCOLL_L WCSCMP ENTRY MDL MEM L R.
  eapply satisfies_all_pmono with (p1:=wcscoll_l_program).
    unfold wcscoll_l_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold wcscoll_l_invs.
    unfold wcscoll_l_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r MDL MEM L R START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscoll_l_program_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [L [R [RSP CS]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps wcscoll_l_program _ _ _ _ s2 nil _ s1 t MDL1 wcscoll_l_program_welltyped).
  intro MDL2.
  eapply (tail_leaf_ni wcscoll_l_program wcscmp_amd64 _ _ (wcscmp_invs s2 (s2 V_MEM64) l r) wcscmp_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold wcscmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply wcscmp_correct; first
      [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
  - intros a s t' NC X2. unfold wcscoll_l_invs, wcscoll_l_exit. unfold wcscmp_exit in X2.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold wcscoll_l_exit, wcscoll_l_invs, wcscmp_invs. unfold wcscmp_exit in X2.
    repeat first
    [ discriminate X2
    | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    all: unfold wcscmp_post, callee_saved_eq in POST |- *; unfold s2 in POST.
    all: rewrite ?update_frame in POST by discriminate.
    all: rewrite MEM, RSP, B0, B1, B2, B3, B4, B5 in POST.
    all: exact POST.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold wcscmp_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.

