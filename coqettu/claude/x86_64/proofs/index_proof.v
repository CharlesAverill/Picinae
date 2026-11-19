(* index -- locate a byte in a string (musl x86_64, C), a tail call into
   strchr (which itself calls strchrnul, which calls strlen)

   SEMANTICS
   ---------
   musl's index (src/legacy/index.c... src/string/index.c) is

       char *index(const char *s, int c) { return strchr(s, c); }

   compiled to a single JMP strchr (0x1659b5).  strchr's contract
   (strchr_proof.v, a three-level composition) is used through tail_leaf
   (lib/x64_tail.v): index's exit is strchr's RET.

   SPECIFICATION (man 3 index, Linux man-pages 6.9.1, paraphrased)
   --------------------------------------------------------------
     char *index(const char *s, int c);
     index is identical to strchr: it returns a pointer to the first
     occurrence of the character c in the string s (the terminating null
     byte counts as part of the string), or NULL.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            index at 0x658d0, strchr at 0x659b5 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/index_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Exactly strchr's (strchr_proof.v): RDI = s, ESI = c, str_ok (s is
   terminated and off the 48 bytes below rsp).  At strchr's RET (0x1659c6),
   which returns to index's caller, strchr_post holds relative to index's
   entry state: RAX = s + k for the first k with s[k] = c8, or NULL if the
   terminator comes first (c8 <> 0); nothing outside the 48 bytes below rsp
   changes; RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.index_amd64 CoqEtTu.programs.strchr_amd64
               CoqEtTu.programs.strchrnul_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.strchrnul_proof CoqEtTu.proofs.strchr_proof.
Open Scope N.

Definition index_program : program := updateall2 index_amd64 strchr_program.

Theorem index_welltyped: welltyped_prog x64typctx index_amd64.
Proof. exact index_amd64.welltyped. Qed.

Lemma index_program_welltyped: welltyped_prog x64typctx index_program.
Proof.
  intros s a. unfold index_program, updateall2 at 1, updateall.
  destruct (strchr_program s a) as [[sz q]|] eqn:SL.
    pose proof (strchr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply index_welltyped.
Qed.

Lemma strchr_in_prog: strchr_amd64 ⊆2 strchr_program.
Proof.
  intros s a insn SC. unfold strchr_program, updateall2 at 1, updateall.
  destruct (strchrnul_program s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strchrnul_program, updateall2, updateall, strchr_amd64, strchrnul_amd64, strlen_amd64.
  cbv beta.
  repeat first
  [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Lemma strchrnul_in_prog: strchrnul_amd64 ⊆2 strchr_program.
Proof. intros s a insn H. apply subset_updateall2, strchrnul_in_program, H. Qed.

Lemma strlen_in_prog: strlen_amd64 ⊆2 strchr_program.
Proof. intros s a insn H. apply subset_updateall2. unfold strchrnul_program. apply subset_updateall2, H. Qed.

Definition index_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1659c6 => true
  | _ => false end | _ => false end.

Definition index_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1658d0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ str_ok m p (s0 R_RSP))
  | 0x1659c6 => Some (strchr_post s0 m p c s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem index_correct:
  forall prog s t s' x' m p c
         (INDEX: index_amd64 ⊆2 prog) (STRCHR: strchr_amd64 ⊆2 prog)
         (STRCHRNUL: strchrnul_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658d0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STR: str_ok m p (s R_RSP)),
  satisfies_all prog (index_invs s m p c) index_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c INDEX STRCHR STRCHRNUL STRLEN ENTRY MDL MEM P C STR.
  eapply satisfies_all_pmono with (p1:=index_program).
    unfold index_program, strchr_program, strchrnul_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold index_invs.
    unfold index_program, strchr_program, strchrnul_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C STR START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply index_program_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [P [C [RSP [CS STR]]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps index_program _ _ _ _ s2 nil _ s1 t MDL1 index_program_welltyped).
  intro MDL2.
  eapply (tail_leaf_ni index_program strchr_program _ _ (strchr_invs s2 (s2 V_MEM64) p c) strchr_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold strchr_invs.
    unfold strchr_program, strchrnul_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply strchr_correct; first
      [ apply strchr_in_prog | apply strchrnul_in_prog | apply strlen_in_prog
      | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
    unfold s2. reg. rewrite ?RSP, ?MEM. exact STR.
  - intros a s t' NC X2. unfold index_invs, index_exit. unfold strchr_exit in X2.
    unfold strchr_program, strchrnul_program, updateall2, updateall in NC.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold index_exit, index_invs, strchr_invs. unfold strchr_exit in X2.
    repeat first
    [ discriminate X2
    | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    all: unfold strchr_post, callee_saved_eq in POST |- *; unfold s2 in POST.
    all: rewrite ?update_frame in POST by discriminate.
    all: rewrite MEM, RSP, B0, B1, B2, B3, B4, B5 in POST.
    all: exact POST.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold strchr_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.
