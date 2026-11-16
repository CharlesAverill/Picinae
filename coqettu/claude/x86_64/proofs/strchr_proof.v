(* strchr -- locate a byte in a string (musl x86_64, C), composed with
   strchrnul and (transitively) strlen

   SEMANTICS
   ---------
   musl's strchr (src/string/strchr.c) is

       char *r = __strchrnul(s, c);
       return *(unsigned char * )r == (unsigned char)c ? r : 0;

   The binary pushes RBX, keeps c in EBX across the CALL to strchrnul
   (0x124140), compares the byte at the returned pointer with BL and returns
   it or NULL (CMOVNE).  This is a three-level composition: strchrnul's
   contract (strchrnul_proof.v), itself proved with strlen's contract, is
   used through call_leaf_ni; neither callee is re-verified here.  The
   callee's memory frame (stack_frame: nothing outside the 32 bytes below its
   RSP changes) is what lets strchr read its saved RBX, its return address
   and the found byte after the call.

   SPECIFICATION (man 3 strchr, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            char *strchr(const char *s, int c);

     DESCRIPTION
            The strchr() function returns a pointer to the first occurrence
            of the character c in the string s.
            Here "character" means "byte"; these functions do not work with
            wide or multibyte characters.

     RETURN VALUE
            The strchr() and strrchr() functions return a pointer to the
            matched character or NULL if the character is not found.  The
            terminating null byte is considered part of the string, so that
            if c is specified as '\0', these functions return a pointer to
            the terminator.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strchr at 0x659b5, strchrnul at 0x24140, strlen at 0x348c0
            (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strchr_amd64.v etc.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (c8 = c mod 256); RSP = rsp; m = memory.  The
            theorem holds for every program containing strchr's, strchrnul's
            and strlen's instructions.  Precondition (str_ok): s is
            NUL-terminated and the string through its terminator does not
            overlap the 48 bytes below rsp, which strchr, strchrnul and their
            CALLs use as stack.
   Output:  At the RET (0x1659c6): for some k, the bytes s[0..k) are neither
            0 nor c8, and either s[k] = c8 and RAX = s + k (mod 2^64), or
            s[k] = 0, c8 <> 0 and RAX = 0 (NULL).  No byte outside the 48
            bytes below rsp has changed; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strchr_amd64 CoqEtTu.programs.strchrnul_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.strchrnul_proof.
Open Scope N.

(* strchr with its callees strchrnul and strlen *)
Definition strchr_program : program := updateall2 strchr_amd64 strchrnul_program.

Lemma strchr_program_welltyped: welltyped_prog x64typctx strchr_program.
Proof.
  intros s a. unfold strchr_program, updateall2, updateall.
  destruct (strchrnul_program s a) as [[sz q]|] eqn:SC.
    pose proof (strchrnul_program_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply strchr_amd64.welltyped.
Qed.

Theorem strchr_welltyped: welltyped_prog x64typctx strchr_amd64.
Proof. exact strchr_amd64.welltyped. Qed.

Definition strchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1659c6 => true
  | _ => false end | _ => false end.

(* s is terminated and, through its terminator, lies outside the 48 bytes
   below rsp that strchr, strchrnul and their CALLs may write *)
Definition str_ok (m p rsp:N) :=
  exists L, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ ~ overlap 64 p (L + 1) (rsp ⊖ 48) 48.

Definition strchr_post (s0:store) (m p c:N) (s:store) :=
  (exists k, cfree m p (c mod 2^8) k /\
     ((m Ⓑ[p ⊕ k] = c mod 2^8 /\ s R_RAX = p ⊕ k) \/
      (m Ⓑ[p ⊕ k] = 0 /\ c mod 2^8 <> 0 /\ s R_RAX = 0))) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 48 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strchr_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1659b5 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ str_ok m p (s0 R_RSP) /\
                      s0 R_RSP < 2^64)
  | 0x1659b8 => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RBX = c mod 2^32 /\ s R_RSP = s0 R_RSP ⊖ 8 /\
                      s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
                      s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15 /\
                      str_ok m p (s0 R_RSP) /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64)
  | 0x1659c6 => Some (strchr_post s0 m p c s)
  | _ => None
  end | _ => None end.

(* The two pushes below rsp leave the string's bytes [0, L] alone. *)
Lemma push2_bytes:
  forall m p L rsp v1 v2 i, ~ overlap 64 p (L + 1) (rsp ⊖ 48) 48 -> i <= L ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i].
Proof.
  intros m p L rsp v1 v2 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [x [y [X [Y E]]]]. apply NOV. exists i, (40 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [x [y [X [Y E]]]]. apply NOV. exists i, (32 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma str_ok_stack:
  forall m p c rsp v1 v2, str_ok m p rsp ->
  stack_ok (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2]) p c (rsp ⊖ 16).
Proof.
  intros m p c rsp v1 v2 [L [NL [ZL NOV]]] _. exists L. split; [|split].
  - intros i I. rewrite push2_bytes with (L:=L) by (assumption || lia). apply NL, I.
  - rewrite push2_bytes with (L:=L) by (assumption || lia). exact ZL.
  - intros [x [y [X [Y E]]]]. apply NOV. exists x, (y + 0). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma str_frame_off:
  forall p k L rsp, k <= L -> rsp < 2^64 -> ~ overlap 64 p (L + 1) (rsp ⊖ 48) 48 ->
  32 <= msub 64 (p ⊕ k) (msub 64 (msub 64 rsp 16) 32).
Proof.
  intros p k L rsp KL RB NOV.
  assert (E: msub 64 (msub 64 rsp 16) 32 = msub 64 rsp 48).
  { unfold msub. change (2^64) with 18446744073709551616 in *. lia. }
  rewrite E. assert (BB: msub 64 rsp 48 < 2^64) by apply (msub_lt 64). set (b := msub 64 rsp 48) in *. clearbody b.
  destruct (N.le_gt_cases 48 (msub 64 (p ⊕ k) b)) as [D|D]. lia. exfalso.
  apply NOV. exists k, (msub 64 (p ⊕ k) b). split. lia. split. exact D.
  unfold msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma rsp16_32: forall rsp, msub 64 (msub 64 rsp 16) 32 = msub 64 rsp 48.
Proof. intros. unfold msub. change (2^64) with 18446744073709551616 in *. lia. Qed.

Theorem strchr_correct:
  forall prog s t s' x' m p c
         (STRCHR: strchr_amd64 ⊆2 prog) (STRCHRNUL: strchrnul_amd64 ⊆2 prog)
         (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1659b5, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STR: str_ok m p (s R_RSP)),
  satisfies_all prog (strchr_invs s m p c) strchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c STRCHR STRCHRNUL STRLEN ENTRY MDL MEM P C STR.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strchr_program).
    unfold strchr_program, strchrnul_program.
    apply updateall2_lub. exact STRCHR. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strchr_invs.
    unfold strchr_program, strchrnul_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C STR RB RBXB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchr_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [C [RSP [CS [STR RB']]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B. conj_tac.
  - destruct PRE as [MEM [RDI [RSI [RBX [RSP [BP [R12 [R13 [R14 [R15 [STR [RB' RBXB']]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strchr_program _ _ _ _ s2 nil _ s1 t MDL1 strchr_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strchr_program strchrnul_program _ _
              (strchrnul_invs s2 (s2 V_MEM64) p c) strchrnul_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strchrnul_invs.
      unfold strchrnul_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strchrnul_correct_self; first
        [ assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption)
        | (unfold s2; rewrite update_updated, update_frame, update_updated by discriminate;
           apply str_ok_stack; assumption) ].
    + intros a s t' NC. unfold strchr_invs, strchr_exit.
      unfold strchrnul_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strchrnul_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strchrnul_exit _) eqn:EX; [|destruct PRE].
      unfold strchrnul_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strchr_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [[k [RAX [CF ZC]]] [FR [RSP' CS']]].
      all: unfold s2 in *; rewrite !update_frame in RSP' by discriminate; rewrite update_updated in RSP'.
      all: rewrite update_updated in CF, ZC, FR.
      all: rewrite update_frame, update_updated in FR by discriminate.
      all: assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x1659bd).
      all: try (rewrite (stack_frame_get8 _ _ _ 32 _ FR) by
                 (reflexivity || mlia64);
                rewrite getmem_setmem by discriminate; reflexivity).
      all: assert (RBX8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBX).
      all: try (rewrite (stack_frame_get8 _ _ _ 32 _ FR) by
                 (reflexivity || mlia64);
                rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64);
                rewrite getmem_setmem by discriminate; apply N.mod_small; assumption).
      all: x64_step.
      all: rewrite RA.
      all: repeat x64_step.
      all: bc_norm.
      all: destruct STR as [L [NL [ZL NOV]]].
      all: assert (RBXc: s' R_RBX = c mod 2^32) by
             (rewrite (proj1 CS'), !update_frame by discriminate; exact RBX).
      all: assert (CSb: s' R_RBP = s0 R_RBP /\ s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\
                        s' R_R14 = s0 R_R14 /\ s' R_R15 = s0 R_R15) by
             (destruct CS' as (_ & B & C & D & E & F); rewrite B, C, D, E, F;
              rewrite !update_frame by discriminate; repeat split; assumption).
      all: assert (KL: k <= L) by
             (destruct (N.le_gt_cases k L) as [|KG]; [assumption|];
              exfalso; apply (proj1 (CF L KG)); rewrite push2_bytes with (L:=L) by (assumption || mlia64);
              exact ZL).
      all: assert (BK: s' V_MEM64 Ⓑ[p + k] = m Ⓑ[p ⊕ k]).
      all: try (rewrite <- getmem_mod_l; change (getmem 64 LittleE 1 (s' V_MEM64) ((p + k) mod 2^64))
                with (s' V_MEM64 Ⓑ[p ⊕ k]);
                rewrite FR; [apply push2_bytes with (L:=L); assumption |];
                apply (str_frame_off p k L (s0 R_RSP)); assumption).
      all: rewrite ?BK in *.
      all: rewrite RBXc, mp2_mod_mod_min in BC; change (N.min 32 8) with 8 in BC.
      all: assert (CFm: cfree m p (c mod 2^8) k) by
             (intros i I; rewrite <- (push2_bytes m p L (s0 R_RSP) (s0 R_RBX) 1464765 i) by (assumption || mlia64);
              apply CF, I).
      all: assert (ZCm: m Ⓑ[p ⊕ k] = 0 \/ m Ⓑ[p ⊕ k] = c mod 2^8) by
             (rewrite <- (push2_bytes m p L (s0 R_RSP) (s0 R_RBX) 1464765 k) by (assumption || mlia64);
              exact ZC).
      all: split; [ exists k; split; [exact CFm|];
                    first [ left; split; [exact BC | reflexivity]
                          | right; destruct ZCm as [Z0|Zc]; [|contradiction];
                            split; [exact Z0|]; split; [intro; congruence | reflexivity] ] |].
      all: split; [ intros b B; rewrite FR;
                    [ rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 48) by (assumption || reflexivity || lia);
                      rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 48) by (assumption || reflexivity || lia);
                      reflexivity
                    | rewrite rsp16_32; mlia64 ] |].
      all: split; [apply N.mod_small; exact RB|].
      all: destruct CSb as (B1 & B2 & B3 & B4 & B5).
      all: repeat split; rewrite ?update_frame by discriminate;
           first [ assumption | rewrite update_updated; exact RBX8 ].
Qed.

