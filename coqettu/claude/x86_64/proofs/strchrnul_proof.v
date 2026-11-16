(* strchrnul -- locate a byte or the end of a string (musl x86_64, C),
   composed with its callee strlen

   SEMANTICS
   ---------
   musl's __strchrnul (src/string/strchrnul.c) is

       c = (unsigned char)c;
       if (!c) return (char * )s + strlen(s);
       for (; (uintptr_t)s % ALIGN; s++)
           if (!*s || *(unsigned char * )s == c) return (char * )s;
       size_t k = ONES * c;
       for (w = (void * )s; !HASZERO( *w) && !HASZERO( *w^k); w++);
       s = (void * )w;
       for (; *s && *(unsigned char * )s != c; s++);
       return (char * )s;

   For c mod 256 = 0 the binary calls strlen (at its global address
   0x1348c0), after spilling s to its stack frame.  The proof handles that
   CALL compositionally: strlen's own contract (strlen_proof.v) is used through
   call_leaf_ni (lib/x64_compose.v), which wraps Picinae's exec_subroutine;
   strlen's code is not re-verified here.  The word loop uses
   haszero2_bytes: HASZERO(w) | HASZERO(w ^ c*ONES) = 0 implies no byte of w
   is 0 or c.

   SPECIFICATION (man 3 strchrnul, Linux man-pages 6.9.1)
   ------------------------------------------------------

     SYNOPSIS
            #define _GNU_SOURCE
            #include <string.h>
            char *strchrnul(const char *s, int c);

     DESCRIPTION
            The strchrnul() function is like strchr() except that if c is not
            found in s, then it returns a pointer to the null byte at the end
            of s, rather than NULL.
            Here "character" means "byte"; these functions do not work with
            wide or multibyte characters.

     RETURN VALUE
            The strchrnul() function returns a pointer to the matched
            character, or a pointer to the null byte at the end of s (i.e.,
            s+strlen(s)) if the character is not found.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strchrnul at 0x24140, strlen at 0x348c0 (Ghidra image base
            0x100000: 0x124140, 0x1348c0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strchrnul_amd64.v, strlen_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (only c8 = c mod 256 matters); RSP = rsp;
            m = memory on entry.  The theorem holds for every program that
            contains both strchrnul's and strlen's instructions.
            Precondition (stack_ok), only when c8 = 0: s is terminated and
            the string through its terminator does not overlap the 32 bytes
            below rsp, which strchrnul and its CALL overwrite before strlen
            reads the string.  (No live C object can be there.)
   Output:  At either RET (0x124186, 0x124202): RAX = s + k (mod 2^64) where
            the bytes s[0..k) are all neither 0 nor c8, and s[k] is 0 or c8;
            no byte outside the 32 bytes below rsp has changed (stack_frame);
            RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strchrnul_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof.
Open Scope N.

(* strchrnul together with its callee strlen, at their global addresses *)
Definition strchrnul_program : program := updateall2 strchrnul_amd64 strlen_amd64.

Lemma strchrnul_program_welltyped: welltyped_prog x64typctx strchrnul_program.
Proof.
  intros s a. unfold strchrnul_program, updateall2, updateall.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply strchrnul_amd64.welltyped.
Qed.

(* bytes p+0 .. p+k-1 are neither 0 nor c *)
Definition cfree (m:memory) (p c k:N) := forall i, i < k -> m Ⓑ[p ⊕ i] <> 0 /\ m Ⓑ[p ⊕ i] <> c.

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Lemma cfree_succ: forall m p c k, cfree m p c k -> m Ⓑ[p ⊕ k] <> 0 -> m Ⓑ[p ⊕ k] <> c ->
  cfree m p c (k + 1).
Proof.
  intros m p c k CF B0 BC i I. destruct (N.lt_ge_cases i k). apply CF. assumption.
  replace i with k by lia. split; assumption.
Qed.

Lemma cfree_add8:
  forall (m:memory) p c k, c < 256 -> cfree m p c k ->
  ((m Ⓠ[p + k] ⊖ 0x0101010101010101 .& N.lnot (m Ⓠ[p + k]) 64) .|
   (N.lnot (m Ⓠ[p + k] .^ c * 0x0101010101010101) 64 .&
    (m Ⓠ[p + k] .^ c * 0x0101010101010101) ⊖ 0x0101010101010101))
  .& 0x8080808080808080 = 0 ->
  cfree m p c (k + 8).
Proof.
  intros m p c k C CF H i I. destruct (N.lt_ge_cases i k) as [IK|IK]. apply CF, IK.
  pose proof (haszero2_bytes _ c (getmem_bound 64 LittleE 8 m (p + k)) C H (i - k) ltac:(lia)) as B.
  rewrite byte_of_load in B by lia.
  rewrite !getmem_mod_l in *. replace (p + k + (i - k)) with (p + i) in B by lia. exact B.
Qed.

Lemma c8_lt: forall c, c mod 2^8 < 256.
Proof. intros. apply N.mod_lt. discriminate. Qed.

(* For c = 0 strchrnul calls strlen after writing 16 bytes of its own stack
   frame (a saved register and the return address), so the string, up to its
   terminator, must not lie in the 32 bytes below the caller's RSP (where no
   live C object can be). *)
Definition stack_ok (m p c rsp:N) :=
  c mod 2^8 = 0 -> exists L, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ ~ overlap 64 p (L + 1) (rsp ⊖ 32) 32.

Lemma nilfree_unique:
  forall m p k L, nilfree m p k -> m Ⓑ[p ⊕ k] = 0 -> nilfree m p L -> m Ⓑ[p ⊕ L] = 0 -> k = L.
Proof.
  intros m p k L NK ZK NL ZL. destruct (N.lt_trichotomy k L) as [H|[H|H]].
  - exfalso. apply (NL k H ZK).
  - exact H.
  - exfalso. apply (NK L H ZL).
Qed.

(* The two stack writes before the call leave the string's bytes alone. *)
Lemma frame_bytes:
  forall m p L rsp v1 v2 i, ~ overlap 64 p (L + 1) (rsp ⊖ 32) 32 -> i <= L ->
  (m [Ⓠrsp ⊖ 16 := v1] [Ⓠrsp ⊖ 32 := v2]) Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i].
Proof.
  intros m p L rsp v1 v2 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [x [y [X [Y E]]]]. apply NOV. exists i, (16 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [x [y [X [Y E]]]]. apply NOV. exists i, y. split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Ltac frame_tac :=
  lazymatch goal with |- stack_frame _ _ _ _ =>
    repeat (apply stack_frame_store; [lia | reflexivity |]);
    first [ apply stack_frame_refl
          | match goal with H: _ V_MEM64 = _ |- _ => rewrite H; apply stack_frame_refl end ]
  end.
Ltac fin := conj_tac; try frame_tac.

Definition strchrnul_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x124186 | 0x124202 => true
  | _ => false end | _ => false end.

Definition strchrnul_post (s0:store) (m p c:N) (s:store) :=
  (exists k, s R_RAX = p ⊕ k /\ cfree m p (c mod 2^8) k /\
             (m Ⓑ[p ⊕ k] = 0 \/ m Ⓑ[p ⊕ k] = c mod 2^8)) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 32 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strchrnul_invs (s0:store) (m p c:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x124140 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ stack_ok m p c (s0 R_RSP))
  (* just before the call to strlen (c mod 256 = 0) *)
  | 0x124172 => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := p] /\ s R_RDI = p /\
                      s R_RSP = s0 R_RSP ⊖ 24 /\ c mod 2^8 = 0 /\ callee_saved_eq s0 s /\
                      stack_ok m p c (s0 R_RSP) /\ s0 R_RSP < 2^64)
  (* the alignment loop and the final byte loop *)
  | 0x12414b | 0x1241f4 =>
      Some (exists k, s R_RDX = p ⊕ k /\ cfree m p (c mod 2^8) k /\ s R_RSI = c mod 2^8 /\
            c mod 2^8 <> 0 /\ s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* the word loop *)
  | 0x1241c0 =>
      Some (exists k, s R_RDX = p ⊕ k /\ cfree m p (c mod 2^8) k /\ s R_RSI = c mod 2^8 /\
            c mod 2^8 <> 0 /\ s R_R8 = 0xfefefefefefefeff /\ s R_R10 = 0x8080808080808080 /\
            s R_R9 = c mod 2^8 * 0x0101010101010101 /\
            s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x124186 | 0x124202 => Some (strchrnul_post s0 m p c s)
  | _ => None
  end | _ => None end.

Theorem strchrnul_correct:
  forall prog s t s' x' m p c
         (STRCHRNUL: strchrnul_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x124140, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STK: stack_ok m p c (s R_RSP)),
  satisfies_all prog (strchrnul_invs s m p c) strchrnul_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c STRCHRNUL STRLEN ENTRY MDL MEM P C STK.
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strchrnul_program).
    unfold strchrnul_program. rewrite <- (updateall2_subset _ _ STRLEN).
    apply updateall2_mono. exact STRCHRNUL.
    intros a s1 t1 EXIT NOCODE. unfold strchrnul_invs.
    unfold strchrnul_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c MDL MEM P C PB STK START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strchrnul_program_welltyped. intro MDL1.
  clear - PRE MDL1 PB. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [P [C [RSP [CS STK]]]]].
    assert (RB: s0 R_RSP < 2^64) by (rewrite <- RSP; apply (MDL1 R_RSP 64); reflexivity).
    repeat x64_step. all: bc_norm.
    + fin.
    + exists 0. split. rewrite N.add_0_r, N.mod_small by assumption. reflexivity.
      split. intros i I. lia. fin.
  - (* alignment loop *)
    destruct PRE as [k [RDX [CF [RSI [CNZ [MEM [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + (* aligned: enter the word loop *)
      exists k. fin.
      rewrite N.shiftr_0_r, (N.mod_small (c mod 2^8)), scast_32_64_small by
        (pose proof (c8_lt c); change (2^32) with 4294967296; change (2^31) with 2147483648; lia).
      apply N.mod_small. pose proof (c8_lt c). change (2^64) with 18446744073709551616. lia.
    + split. exists k. split. reflexivity. split. assumption. left. assumption. fin.
    + split. exists k. split. reflexivity. split. assumption. right. assumption. fin.
    + exists (k + 1). split. f_equal. lia. split. apply cfree_succ; assumption. fin.
  - (* the call to strlen *)
    destruct PRE as [MEM [RDI [RSP [C0 [CS [STK RB]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strchrnul_program _ _ _ _ s2 nil _ s1 t MDL1 strchrnul_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strchrnul_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) p) strlen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ assumption | apply pf2sub_refl | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; exact RDI) ].
    + intros a s t' NC. unfold strchrnul_invs, strchrnul_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strlen_exit in X. addr_cases X. discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strlen_exit _) eqn:EX; [|destruct PRE].
      unfold strlen_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strchrnul_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z.
      repeat x64_step.
      destruct (STK C0) as [L [NL [ZL NOV]]].
      assert (KL: k = L).
      { apply (nilfree_unique _ p _ L NF Z).
        intros i I. rewrite frame_bytes with (L:=L) by (assumption || lia). apply NL, I.
        rewrite frame_bytes with (L:=L) by (assumption || lia). exact ZL. }
      rewrite KL in *.
      split. exists L. split. reflexivity. split.
        intros i I. rewrite C0. split; apply NL, I.
        left. exact ZL.
      split. frame_tac.
      split. apply N.mod_small, RB.
      assert (CS2: callee_saved_eq s0 s').
      { eapply callee_saved_eq_trans. exact CS. eapply callee_saved_eq_trans; [|exact CS'].
        repeat split; rewrite !update_frame by discriminate; reflexivity. }
      callee_saved_tac.
  - (* word loop *)
    destruct PRE as [k [RDX [CF [RSI [CNZ [R8 [R10 [R9 [MEM [RSP CS]]]]]]]]]].
    repeat x64_step. all: bc_norm.
    + exists (k + 8). split. f_equal. lia. split. apply cfree_add8. apply c8_lt. assumption. assumption.
      fin.
    + exists k. fin.
  - (* final byte loop *)
    destruct PRE as [k [RDX [CF [RSI [CNZ [MEM [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + split. exists k. split. reflexivity. split. assumption. left. assumption. fin.
    + split. exists k. split. reflexivity. split. assumption. right. assumption. fin.
    + exists (k + 1). split. f_equal. lia. split. apply cfree_succ; assumption. fin.
Qed.

Lemma strchrnul_in_program: strchrnul_amd64 ⊆2 strchrnul_program.
Proof.
  intros s a insn SC. unfold strchrnul_program, updateall2, updateall.
  destruct (strlen_amd64 s a) eqn:SL; [|exact SC].
  exfalso. revert SC SL. unfold strchrnul_amd64, strlen_amd64.
  repeat first
  [ discriminate
  | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

(* strchrnul's contract for its own program (the callee view used by strchr). *)
Corollary strchrnul_correct_self:
  forall s t s' x' m p c
         (ENTRY: startof t (x',s') = (Addr 0x124140, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c)
         (STK: stack_ok m p c (s R_RSP)),
  satisfies_all strchrnul_program (strchrnul_invs s m p c) strchrnul_exit ((x',s')::t).
Proof.
  intros. apply strchrnul_correct; try assumption.
  apply strchrnul_in_program. apply subset_updateall2.
Qed.
