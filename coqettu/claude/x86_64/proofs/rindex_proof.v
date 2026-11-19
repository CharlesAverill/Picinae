(* rindex -- locate the last occurrence of a byte in a string (musl x86_64,
   C), a tail call into strrchr (which calls strlen and tail-calls memrchr)

   SEMANTICS
   ---------
   musl's rindex (src/string/rindex.c) is

       char *rindex(const char *s, int c) { return strrchr(s, c); }

   compiled to a single JMP strrchr (0x165bc2).  strrchr's contract
   (strrchr_proof.v: a call to strlen and a tail call to memrchr) is used
   through tail_leaf (lib/x64_tail.v): rindex's exit is memrchr's RET.
   Tail calls compose: strrchr's own exits are already its callee's.

   SPECIFICATION (man 3 index, Linux man-pages 6.9.1, paraphrased)
   --------------------------------------------------------------
     char *rindex(const char *s, int c);
     rindex is identical to strrchr: it returns a pointer to the last
     occurrence of the character c in the string s (the terminating null
     byte counts as part of the string), or NULL.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            rindex at 0x658e3, strrchr at 0x65bc2 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/rindex_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Exactly strrchr's (strrchr_proof.v): RDI = s, ESI = c, srch_ok (s is
   terminated and off the 32 bytes below rsp).  At memrchr's RET
   (0x1347da), which returns to rindex's caller, strrchr_post holds relative
   to rindex's entry state: RAX = s + K for the last K <= L with s[K] = c8,
   or NULL; nothing outside the 32 bytes below rsp changes; RSP = rsp; RBX,
   RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.rindex_amd64 CoqEtTu.programs.strrchr_amd64
               CoqEtTu.programs.strlen_amd64 CoqEtTu.programs.memrchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.memrchr_proof CoqEtTu.proofs.strrchr_proof.
Open Scope N.

Definition rindex_program : program := updateall2 rindex_amd64 strrchr_program.

Theorem rindex_welltyped: welltyped_prog x64typctx rindex_amd64.
Proof. exact rindex_amd64.welltyped. Qed.

Lemma rindex_program_welltyped: welltyped_prog x64typctx rindex_program.
Proof.
  intros s a. unfold rindex_program, updateall2 at 1, updateall.
  destruct (strrchr_program s a) as [[sz q]|] eqn:SL.
    pose proof (strrchr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply rindex_welltyped.
Qed.

Lemma strrchr_in_prog: strrchr_amd64 ⊆2 strrchr_program.
Proof.
  intros s a insn SC. unfold strrchr_program, updateall2, updateall.
  destruct (memrchr_amd64 s a) eqn:SM.
  - exfalso. revert SC SM. unfold strrchr_amd64, memrchr_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
  - destruct (strlen_amd64 s a) eqn:SL; [|exact SC].
    exfalso. revert SC SL. unfold strrchr_amd64, strlen_amd64.
    repeat first
    [ (let H1 := fresh in let H2 := fresh in intros H1 H2; first [discriminate H1 | discriminate H2])
    | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Definition rindex_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1347da => true
  | _ => false end | _ => false end.

Definition rindex_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1658e3 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ srch_ok m p (s0 R_RSP))
  | 0x1347da => Some (strrchr_post s0 m p c s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem rindex_correct:
  forall prog s t s' x' m p c
         (RINDEX: rindex_amd64 ⊆2 prog) (STRRCHR: strrchr_amd64 ⊆2 prog)
         (STRLEN: strlen_amd64 ⊆2 prog) (MEMRCHR: memrchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658e3, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STR: srch_ok m p (s R_RSP)),
  satisfies_all prog (rindex_invs s m p c) rindex_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c RINDEX STRRCHR STRLEN MEMRCHR ENTRY MDL MEM P C STR.
  eapply satisfies_all_pmono with (p1:=rindex_program).
    unfold rindex_program, strrchr_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold rindex_invs.
    unfold rindex_program, strrchr_program, updateall2, updateall in NOCODE.
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
  eapply models_at_invariant; try eassumption. apply rindex_program_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [P [C [RSP [CS STR]]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps rindex_program _ _ _ _ s2 nil _ s1 t MDL1 rindex_program_welltyped).
  intro MDL2.
  eapply (tail_leaf_ni rindex_program strrchr_program _ _ (strrchr_invs s2 (s2 V_MEM64) p c) strrchr_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold strrchr_invs.
    unfold strrchr_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply strrchr_correct; first
      [ apply strrchr_in_prog | apply strlen_in_strrchr | apply subset_updateall2
      | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
    unfold s2. reg. rewrite ?RSP, ?MEM. exact STR.
  - intros a s t' NC X2. unfold rindex_invs, rindex_exit. unfold strrchr_exit in X2.
    unfold strrchr_program, updateall2, updateall in NC.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold rindex_exit, rindex_invs, strrchr_invs. unfold strrchr_exit in X2.
    repeat first
    [ discriminate X2
    | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    all: unfold strrchr_post, callee_saved_eq in POST |- *; unfold s2 in POST.
    all: rewrite ?update_frame in POST by discriminate.
    all: rewrite MEM, RSP, B0, B1, B2, B3, B4, B5 in POST.
    all: exact POST.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold strrchr_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.
