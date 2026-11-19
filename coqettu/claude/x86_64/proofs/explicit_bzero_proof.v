(* explicit_bzero -- zero a buffer, not elided by the compiler (musl x86_64, C),
   composed with memset

   SEMANTICS
   ---------
   musl's explicit_bzero (src/string/explicit_bzero.c) is

       void explicit_bzero(void *d, size_t n)
       {
           d = memset(d, 0, n);
           __asm__ __volatile__ ("" : : "r"(d) : "memory");
       }

   compiled to SUB RSP,8; MOV RDX,RSI; XOR ESI,ESI; CALL memset (0x166095,
   the proved hand-written asm, via call_leaf_ni); ADD RSP,8; RET.

   SPECIFICATION (man 3 explicit_bzero, Linux man-pages 6.9.1, paraphrased)
   -----------------------------------------------------------------------
     void explicit_bzero(void *s, size_t n);
     explicit_bzero erases the data in the n bytes of memory starting at s
     by writing zeros, like bzero, but the operation is guaranteed not to be
     optimized away.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            explicit_bzero at 0x658bd, memset at 0x66095 (Ghidra image base
            0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/explicit_bzero_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = n; RSP = rsp; DF = 0 (ABI); m = memory.
            Precondition: the n bytes at d do not overlap the 16 bytes below
            rsp (where the return address of the inner call is stored).
   Output:  At the RET (0x1658cf): the n bytes at d are 0; every other byte
            outside the 16 bytes below rsp is unchanged; RSP = rsp; RBX, RBP,
            R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.explicit_bzero_amd64 CoqEtTu.programs.memset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_fill_sets.
Require Import CoqEtTu.proofs.memset_proof.
Open Scope N.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Definition ebz_program : program := updateall2 explicit_bzero_amd64 memset_amd64.

Lemma ebz_program_welltyped: welltyped_prog x64typctx ebz_program.
Proof.
  intros s a. unfold ebz_program, updateall2, updateall.
  destruct (memset_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (memset_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply explicit_bzero_amd64.welltyped.
Qed.

Definition ebz_exit (t:trace) :=
  match t with (Addr a,_)::_ => a =? 0x1658cf | _ => false end.

Definition ebz_post (s0:store) (m:memory) (d n:N) (s:store) :=
  (forall i, i < n -> s V_MEM64 Ⓑ[d ⊕ i] = 0) /\
  (forall b, ~ (msub 64 b d < n) -> 16 <= msub 64 b (s0 R_RSP ⊖ 16) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition ebz_invs (s0:store) (m:memory) (d n:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? 0x1658bd then Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = n /\ s R_DF = 0 /\
                                s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\
                                ~ overlap 64 d n (s0 R_RSP ⊖ 16) 16)
    else if a =? 0x1658cf then Some (ebz_post s0 m d n s)
    else None
  | _ => None end.

Lemma frame16b: forall (m:memory) rsp v b, 16 <= msub 64 b (rsp ⊖ 16) -> (m [Ⓠrsp ⊖ 16 := v]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. apply (stack_store_frame _ rsp 16 _ b 16); [lia | reflexivity | assumption]. Qed.

Lemma ra_outside: forall (M M1:memory) d n a, ~ overlap 64 d n (a ⊖ 16) 16 ->
  (forall b, ~ (msub 64 b d < n) -> M Ⓑ[b] = M1 Ⓑ[b]) -> M Ⓠ[a ⊖ 16] = M1 Ⓠ[a ⊖ 16].
Proof.
  intros M M1 d n a NOV F. apply getmem_frame_mem. intros b B.
  rewrite <- !getmem_1 with (e:=LittleE). apply F. intro H.
  apply NOV. exists (msub 64 b d), (msub 64 b (a ⊖ 16)). split. exact H. split. lia. mlia.
Qed.

Theorem explicit_bzero_correct:
  forall prog s t s' x' m d n
         (P1: explicit_bzero_amd64 ⊆2 prog) (P2: memset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658bd, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (Nn: s R_RSI = n) (DF: s R_DF = 0)
         (OK: ~ overlap 64 d n (s R_RSP ⊖ 16) 16),
  satisfies_all prog (ebz_invs s m d n) ebz_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d n P1 P2 ENTRY MDL MEM D Nn DF OK.
  eapply satisfies_all_pmono with (p1:=ebz_program).
  { unfold ebz_program. apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold ebz_invs, ebz_exit in *.
    unfold ebz_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. split. exact MEM. split. exact D. split. exact Nn. split. exact DF.
    split. reflexivity. split. apply callee_saved_eq_refl. exact OK.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact ebz_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [D' [Nn' [DF' [RSP [CS OV]]]]]].
  x64_step. x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps ebz_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 ebz_program_welltyped).
  intro MDL2.
  assert (S2M: s2 V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := 0x1658cb]) by (unfold s2; reg; first [sreflexivity | (rewrite MEM'; sreflexivity)]).
  assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 16) by (unfold s2; reg; reflexivity).
  eapply (call_leaf_ni ebz_program memset_amd64 _ _ (memset_invs s2 (s2 V_MEM64) d 0 n) memset_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold memset_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x'' s''] START'. apply memset_correct;
      [ apply pf2sub_refl | exact START' | exact MDL2 | reflexivity
      | (unfold s2; reg; first [reflexivity | exact D']) | (unfold s2; reg; reflexivity)
      | (unfold s2; reg; first [reflexivity | exact Nn']) | (unfold s2; reg; first [reflexivity | exact DF']) ].
  - intros a s t' NC. unfold ebz_invs, ebz_exit.
    destruct (N.eqb_spec a 0x1658bd) as [->|_]; [exfalso; apply NC; reflexivity|].
    destruct (N.eqb_spec a 0x1658cf) as [->|_]; [exfalso; apply NC; reflexivity|].
    split; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold memset_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
  - intros a' sx t2 ENTRY' UT2 PRE2.
    unfold get_postcondition in PRE2.
    destruct (memset_exit _) eqn:EX; [|destruct PRE2].
    unfold memset_exit in EX. addr_cases EX.
    all: simpl in PRE2.
    all: rewrite app_assoc.
    all: apply (models_after_steps _ _ _ _ _ sx (t2 ++ tm) _ ss1 tt1 MDL1 ebz_program_welltyped).
    all: intro MDL3.
    all: destruct PRE2 as [RAXv [RSP' [CS' [FZ FO]]]].
    all: rewrite S2M in FO. all: rewrite S2R in RSP'.
    all: change (0 mod 2^8) with 0 in FZ.
    all: assert (RA: sx V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x1658cb)
           by (rewrite (ra_outside _ _ d n _ OV FO); rewrite getmem_setmem by discriminate; reflexivity).
    all: destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
    all: unfold s2 in D0, D1, D2, D3, D4, D5. all: rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
    all: x64_step; try rewrite RA; repeat x64_step.
    all: split; [exact FZ |].
    all: split; [intros b B1 B2; rewrite (FO b B1); exact (frame16b m (s0 R_RSP) 0x1658cb b B2) |].
    all: split; [reflexivity |].
    all: destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    all: unfold callee_saved_eq; repeat split; reg; rewrite ?D0, ?D1, ?D2, ?D3, ?D4, ?D5; reg; sassumption.
Qed.
