(* posix_spawnattr_init -- zero a spawn attributes object (musl x86_64, C)

   SEMANTICS
   ---------
   musl (src/process/posix_spawnattr_init.c):

       int posix_spawnattr_init(posix_spawnattr_t *attr)
       { *attr = (posix_spawnattr_t){0}; return 0; }

   compiled to XOR EAX,EAX; MOV ECX,42; REP STOSQ; RET: sizeof
   (posix_spawnattr_t) = 336 = 42 quadwords.  The REP instruction is a cut
   (0x15cd87) with a fill invariant (lib/x64_fill_sets.v), as in memset.

   SPECIFICATION (POSIX.1-2017 posix_spawnattr_init, paraphrased)
   -------------------------------------------------------------
     int posix_spawnattr_init(posix_spawnattr_t *attr);
     initializes a spawn attributes object with the default value for all of
     the individual attributes and returns 0.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            posix_spawnattr_init at 0x5cd80 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/posix_spawnattr_init_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = attr; DF = 0 (ABI); m = memory.  No other precondition.
   Output:  At the RET (0x15cd8a): RAX = 0; the 336 bytes at attr are 0 and
            every other byte is unchanged (filled m M attr 0 336); RSP and
            RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.posix_spawnattr_init_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_fill_sets.
Open Scope N.

Lemma bytes_are_zero: forall L, bytes_are 0 L 0.
Proof. intros L k K. unfold xbits. rewrite N.shiftr_0_l. apply N.mod_0_l. apply N.pow_nonzero. discriminate. Qed.

Definition sai_exit (t:trace) :=
  match t with (Addr a,_)::_ => a =? 0x15cd8a | _ => false end.

Definition sai_invs (s0:store) (m d:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? 0x15cd80 then Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_DF = 0 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if a =? 0x15cd87 then
      Some (exists i, i <= 42 /\ s R_RCX = 42 - i /\ s R_RDI = d ⊕ 8*i /\ s R_RAX = 0 /\ s R_DF = 0 /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ fil m (s V_MEM64) d 0 (fun j => j < 8*i))
    else if a =? 0x15cd8a then
      Some (s R_RAX = 0 /\ filled m (s V_MEM64) d 0 336 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Theorem posix_spawnattr_init_correct:
  forall prog s t s' x' m d
         (P: posix_spawnattr_init_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cd80, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (DF: s R_DF = 0),
  satisfies_all prog (sai_invs s m d) sai_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d P ENTRY MDL MEM D DF.
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono; [exact P| |].
  { intros a s1 t1 EXIT NOCODE; unfold sai_invs, sai_exit in *.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START; rewrite ENTRY in START.
  apply prove_invs.
  simpl; rewrite START; x64_step; conj_tac; apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption; [exact posix_spawnattr_init_amd64.welltyped|]; intro MDL1.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM' [D' [DF' [RSP CS]]]].
    repeat x64_step.
    exists 0. split. lia. split. reflexivity.
    split. rewrite ?D', N.mul_0_r, N.add_0_r, N.mod_small by exact DB. reflexivity.
    split. reflexivity. split. assumption. split. assumption. split. callee_saved_tac.
    rewrite MEM'. eapply fil_equiv; [|apply fil_empty]. intro j. cbv beta. lia.
  - destruct PRE as [i [IL [RCX [RDI [RAX [DF' [RSP [CS FIL]]]]]]]].
    x64_step'. all: repeat x64_step.
    all: bc_norm.
    + split. reflexivity. split.
      eapply fil_filled; [|exact FIL]. intro j. cbv beta.
      lia.
      split. assumption. callee_saved_tac.
    + exists (i + 1).
      split. lia. split. lia.
      split. f_equal. lia.
      conj_tac.
      all: eapply fil_equiv; [|eapply (fil_store m (ss1 V_MEM64) d _ _ (8*i) 8 _ 0);
        [exact FIL | | lia | lia | | apply bytes_are_zero]].
      * intro j. cbv beta. lia.
      * intros j Hj. cbv beta in Hj. lia.
      * reflexivity.
Qed.
