(* strcpy -- copy a string (musl x86_64, C), composed with stpcpy

   SEMANTICS
   ---------
   musl's strcpy (src/string/strcpy.c) is

       __stpcpy(dest, src);
       return dest;

   The binary saves RBX, keeps dest in RBX across the CALL to stpcpy
   (0x1347e0) and returns it.  stpcpy's contract (stpcpy_proof.v) is used
   through call_leaf_ni; stpcpy is not re-verified here.

   SPECIFICATION (man 3 strcpy, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strcpy(char *restrict dst, const char *restrict src);

     DESCRIPTION
            These functions copy the string pointed to by src, into a string
            at the buffer pointed to by dst.  The programmer is responsible
            for allocating a destination buffer large enough, that is,
            strlen(src) + 1.

     RETURN VALUE
            strcpy()
            strcat()
                   These functions return dst.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strcpy at 0x659c7, stpcpy at 0x347e0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strcpy_amd64.v, stpcpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dst, RSI = src; RSP = rsp; m = memory.  Precondition
            (strcpy_ok): stpcpy's cpy_ok (src has length L, the two L+1-byte
            ranges are disjoint), and neither range overlaps the 16 bytes
            below rsp that strcpy and its CALL write.
   Output:  At the RET (0x1659d4): RAX = dst; dst[i] = src[i] for i <= L;
            every byte outside the L+1 bytes at dst and the 16 bytes below
            rsp is unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strcpy_amd64 CoqEtTu.programs.stpcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_memcpy_sets.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.stpcpy_proof.
Open Scope N.

Definition strcpy_program : program := updateall2 strcpy_amd64 stpcpy_amd64.

Lemma strcpy_program_welltyped: welltyped_prog x64typctx strcpy_program.
Proof.
  intros s a. unfold strcpy_program, updateall2, updateall.
  destruct (stpcpy_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (stpcpy_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply strcpy_amd64.welltyped.
Qed.

Theorem strcpy_welltyped: welltyped_prog x64typctx strcpy_amd64.
Proof. exact strcpy_amd64.welltyped. Qed.

Definition strcpy_ok (m d src L rsp:N) :=
  cpy_ok m d src L /\ ~ overlap 64 d (L + 1) (rsp ⊖ 16) 16 /\ ~ overlap 64 src (L + 1) (rsp ⊖ 16) 16.

Definition strcpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1659d4 => true
  | _ => false end | _ => false end.

Definition strcpy_post (s0:store) (m d src L:N) (s:store) :=
  s R_RAX = d /\
  (forall i, i < L + 1 -> s V_MEM64 Ⓑ[d ⊕ i] = m Ⓑ[src ⊕ i]) /\
  (forall b, ~ (msub 64 b d < L + 1) -> 16 <= msub 64 b (s0 R_RSP ⊖ 16) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b]) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strcpy_invs (s0:store) (m d src L:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1659c7 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ strcpy_ok m d src L (s0 R_RSP) /\
                      s0 R_RSP < 2^64)
  | 0x1659cb => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RBX = d /\ s R_RSP = s0 R_RSP ⊖ 8 /\
                      s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
                      s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15 /\
                      strcpy_ok m d src L (s0 R_RSP) /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64)
  | 0x1659d4 => Some (strcpy_post s0 m d src L s)
  | _ => None
  end | _ => None end.

(* bytes outside the 16 stack bytes are unaffected by the two pushes *)
Lemma push2_off:
  forall m x n rsp v1 v2 i, ~ overlap 64 x n (rsp ⊖ 16) 16 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof.
  intros m x n rsp v1 v2 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (8 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, y. split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma strcpy_ok_stack:
  forall m d src L rsp v1 v2, strcpy_ok m d src L rsp ->
  cpy_ok (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) d src L.
Proof.
  intros m d src L rsp v1 v2 [[NF [Z NOV]] [ND NS]]. split; [|split].
  - intros i I. rewrite push2_off with (n := L + 1) by (assumption || lia). apply NF, I.
  - rewrite push2_off with (n := L + 1) by (assumption || lia). exact Z.
  - exact NOV.
Qed.

(* The 8 bytes at rsp-k (k in {8,16}) are not part of the copy. *)
Lemma stack_byte_outside:
  forall d L rsp k a, ~ overlap 64 d (L + 1) (rsp ⊖ 16) 16 -> (k = 8 \/ k = 16) ->
  msub 64 a (msub 64 rsp k) < 8 -> ~ (msub 64 a d < L + 1).
Proof.
  intros d L rsp k a NOV K A H. apply NOV.
  exists (msub 64 a d), (16 - k + msub 64 a (msub 64 rsp k)). split. exact H. split. lia.
  unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Theorem strcpy_correct:
  forall prog s t s' x' m d src L
         (STRCPY: strcpy_amd64 ⊆2 prog) (STPCPY: stpcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1659c7, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: strcpy_ok m d src L (s R_RSP)),
  satisfies_all prog (strcpy_invs s m d src L) strcpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src L STRCPY STPCPY ENTRY MDL MEM D S OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strcpy_program).
    unfold strcpy_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strcpy_invs.
    unfold strcpy_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src L MDL MEM D S OK RB RBXB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strcpy_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP [CS [OK RB']]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B. conj_tac.
  - destruct PRE as [MEM [RDI [RSI [RBX [RSP [BP [R12 [R13 [R14 [R15 [OK [RB' RBXB']]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strcpy_program _ _ _ _ s2 nil _ s1 t MDL1 strcpy_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strcpy_program stpcpy_amd64 _ _
              (stpcpy_invs s2 (s2 V_MEM64) d src L) stpcpy_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold stpcpy_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply stpcpy_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption)
        | (unfold s2; rewrite update_updated; apply strcpy_ok_stack; assumption) ].
    + intros a s t' NC. unfold strcpy_invs, strcpy_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold stpcpy_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (stpcpy_exit _) eqn:EX; [|destruct PRE].
      unfold stpcpy_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strcpy_program_welltyped).
      intro MDL3.
      destruct PRE as [RAX [CPd [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame, update_updated in RSP' by discriminate.
      rewrite update_updated in CPd.
      destruct OK as [OK0 [ND NS]].
      assert (RQ: forall k, k = 8 \/ k = 16 ->
                  s' V_MEM64 Ⓠ[s0 R_RSP ⊖ k] =
                  (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 16 := 1464784]) Ⓠ[s0 R_RSP ⊖ k]).
      { intros k K. apply getmem_frame_mem. intros a' A'.
        rewrite <- !getmem_1 with (e:=LittleE). apply (proj2 CPd).
        apply (stack_byte_outside d L (s0 R_RSP) k); assumption. }
      assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 1464784).
      { rewrite (RQ 16) by (right; reflexivity). rewrite getmem_setmem by discriminate. reflexivity. }
      assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      { rewrite (RQ 8) by (left; reflexivity).
        rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64).
        rewrite getmem_setmem by discriminate. apply N.mod_small; assumption. }
      x64_step. rewrite RA. repeat x64_step.
      assert (RBXs: s' R_RBX = d) by (rewrite (proj1 CS'), !update_frame by discriminate; exact RBX).
      assert (CSb: s' R_RBP = s0 R_RBP /\ s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\
                   s' R_R14 = s0 R_R14 /\ s' R_R15 = s0 R_R15) by
        (destruct CS' as (_ & B & C & D' & E & F); rewrite B, C, D', E, F;
         rewrite !update_frame by discriminate; repeat split; assumption).
      split. exact RBXs.
      split. intros i I. rewrite (proj1 CPd i) by lia. apply push2_off with (n := L + 1); assumption || lia.
      split. intros b B1 B2. rewrite (proj2 CPd b) by (rewrite N.add_comm; exact B1).
        rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 16) by (assumption || reflexivity || lia).
        rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 16) by (assumption || reflexivity || lia).
        reflexivity.
      split. apply N.mod_small; exact RB.
      destruct CSb as (B1 & B2 & B3 & B4 & B5).
      repeat split; rewrite ?update_frame by discriminate;
        first [ assumption | rewrite update_updated; exact R8 ].
Qed.

