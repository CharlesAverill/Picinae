(* bzero -- zero a byte string (musl x86_64, C), a tail call into memset

   SEMANTICS
   ---------
   musl's bzero (src/string/bzero.c) is

       void bzero(void *s, size_t n) { memset(s, 0, n); }

   GCC compiles it to MOV RDX,RSI; XOR ESI,ESI; JMP memset, so memset's RET
   returns directly to bzero's caller.  memset's contract (memset_proof.v,
   hand-written assembly) is used through tail_leaf (lib/x64_tail.v): the
   exits of bzero are memset's RETs, and memset's postcondition there implies
   bzero's.

   SPECIFICATION (man 3 bzero, Linux man-pages 6.9.1, paraphrased)
   --------------------------------------------------------------
     void bzero(void s[.n], size_t n);
     bzero erases the data in the n bytes of memory starting at s by
     writing zeros (bytes containing '\0') to that area.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            bzero at 0x658b3, memset at 0x66095 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/bzero_amd64.v, memset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = n; RSP = rsp; m = memory; DF clear (ABI).
            No other precondition.
   Output:  At memset's RETs (0x166124, 0x166142), which return to bzero's
            caller: the n bytes at s (mod 2^64) are 0 and every other byte
            is unchanged (filled); RAX = s (memset's return value, ignored
            by bzero's callers); RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.bzero_amd64 CoqEtTu.programs.memset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose
               CoqEtTu.lib.x64_fill_sets CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.memset_proof.
Open Scope N.

Definition bzero_program : program := updateall2 bzero_amd64 memset_amd64.

Theorem bzero_welltyped: welltyped_prog x64typctx bzero_amd64.
Proof. exact bzero_amd64.welltyped. Qed.

Lemma bzero_program_welltyped: welltyped_prog x64typctx bzero_program.
Proof.
  intros s a. unfold bzero_program, updateall2, updateall.
  destruct (memset_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (memset_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply bzero_welltyped.
Qed.

Definition bzero_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x166124 | 0x166142 => true
  | _ => false end | _ => false end.

Definition bzero_post (s0:store) (m:memory) (d n:N) (s:store) :=
  filled m (s V_MEM64) d 0 n /\ s R_RAX = d /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition bzero_invs (s0:store) (m:memory) (d n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1658b3 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = n /\ s R_DF = 0 /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x166124 | 0x166142 => Some (bzero_post s0 m d n s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem bzero_correct:
  forall prog s t s' x' m d n
         (BZERO: bzero_amd64 ⊆2 prog) (MEMSET: memset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658b3, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (Nn: s R_RSI = n) (DF: s R_DF = 0),
  satisfies_all prog (bzero_invs s m d n) bzero_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d n BZERO MEMSET ENTRY MDL MEM D Nn DF.
  eapply satisfies_all_pmono with (p1:=bzero_program).
    unfold bzero_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold bzero_invs.
    unfold bzero_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d n MDL MEM D Nn DF START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply bzero_program_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [D [Nn [DF [RSP CS]]]]].
  x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps bzero_program _ _ _ _ s2 tm _ s1 t MDL1 bzero_program_welltyped).
  intro MDL2.
  eapply (tail_leaf_ni bzero_program memset_amd64 _ _ (memset_invs s2 (s2 V_MEM64) d 0 n) memset_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold memset_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply memset_correct; first
      [ apply pf2sub_refl | assumption | reflexivity
      | (unfold s2; reg; assumption) | idtac ].
  - intros a s t' NC X2. unfold bzero_invs, bzero_exit. unfold memset_exit in X2.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold bzero_exit, bzero_invs, memset_invs. unfold memset_exit in X2.
    repeat first
    [ discriminate X2
    | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: destruct POST as [PA [PR [PC PF]]].
    all: assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM).
    all: assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
    all: assert (C02: callee_saved_eq s0 s2) by
           (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
    all: rewrite S2M in PF; change (0 mod 2^8) with 0 in PF.
    all: split; [exact PF|]; split; [exact PA|]; split; [rewrite PR; exact S2R|].
    all: exact (callee_saved_eq_trans _ _ _ C02 PC).
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold memset_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.
