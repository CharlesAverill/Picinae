(* ispunct -- punctuation character test (musl x86_64, C), composed with
   isalnum

   SEMANTICS
   ---------
   musl's ispunct (src/ctype/ispunct.c) is

       return isgraph(c) && !isalnum(c);

   with isgraph inlined as (unsigned)c-0x21 < 0x5e and a CALL to isalnum
   (0x141589).  isalnum's contract (ctype_proof.v) is used through
   call_leaf_ni.

   SPECIFICATION (man 3 ispunct, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <ctype.h>
            int ispunct(int c);

     DESCRIPTION
            ispunct() checks for any printable character which is not a
            space or an alphanumeric character.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            ispunct at 0x4163d, isalnum at 0x41589 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/ispunct_amd64.v, isalnum_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI = c (y = RDI mod 2^32).  No precondition.
   Output:  At either RET: RAX = 1 if y is in [0x21, 0x7e] and is neither a
            letter nor a digit, else 0 -- for every 32-bit int c.  The only
            memory written is the return address below RSP (stack_frame);
            RSP and RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.ispunct_amd64 CoqEtTu.programs.isalnum_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_ctype CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.ctype_proof.
Open Scope N.

Definition ispunct_spec (y:N) := inr 33 126 y && negb (isalnum_spec y).

Definition ispunct_program : program := updateall2 ispunct_amd64 isalnum_amd64.

Theorem ispunct_welltyped: welltyped_prog x64typctx ispunct_amd64.
Proof. exact ispunct_amd64.welltyped. Qed.

Lemma ispunct_program_welltyped: welltyped_prog x64typctx ispunct_program.
Proof.
  intros s a. unfold ispunct_program, updateall2, updateall.
  destruct (isalnum_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (isalnum_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply ispunct_welltyped.
Qed.

Definition ispunct_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x141647 | 0x14165d => true
  | _ => false end | _ => false end.

Definition ispunct_post (s0:store) (c:N) (s:store) :=
  s R_RAX = N.b2n (ispunct_spec (c mod 2^32)) /\
  stack_frame (s0 V_MEM64) (s V_MEM64) (s0 R_RSP) 16 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition ispunct_invs (s0:store) (c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x14163d => Some (s R_RDI = c /\ s V_MEM64 = s0 V_MEM64 /\ s R_RSP = s0 R_RSP /\
                      callee_saved_eq s0 s /\ s0 R_RSP < 2^64)
  | 0x14164c => Some (s R_RDI = c /\ s V_MEM64 = s0 V_MEM64 /\ s R_RSP = s0 R_RSP ⊖ 8 /\
                      callee_saved_eq s0 s /\ inr 33 126 (c mod 2^32) = true /\ s0 R_RSP < 2^64)
  | 0x141647 | 0x14165d => Some (ispunct_post s0 c s)
  | _ => None
  end | _ => None end.

Theorem ispunct_correct:
  forall prog s t s' x' c
         (ISPUNCT: ispunct_amd64 ⊆2 prog) (ISALNUM: isalnum_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x14163d, s))
         (MDL: models x64typctx s) (C: s R_RDI = c),
  satisfies_all prog (ispunct_invs s c) ispunct_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' c ISPUNCT ISALNUM ENTRY MDL C.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=ispunct_program).
    unfold ispunct_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold ispunct_invs.
    unfold ispunct_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 c MDL C RB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ispunct_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [RDI [MEM [RSP [CS RB']]]].
    repeat x64_step. all: bc_norm.
    all: match goal with |- ?G => idtac "E:" G end.
    all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | context [models] => fail | _ => idtac "H:" H T; clear H end end).
    all: admit.
  - destruct PRE as [RDI [MEM [RSP [CS [GR RB']]]]].
    x64_step.
    match goal with |- ?G => idtac "CALL:" G end.
    admit.
Admitted.
