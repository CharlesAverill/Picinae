(* strnlen -- length of a fixed-size string (musl x86_64, C), composed with
   memchr

   SEMANTICS
   ---------
   musl's strnlen (src/string/strnlen.c) is

       const char *p = memchr(s, 0, n);
       return p ? p-s : n;

   The binary saves RBP and RBX (keeping s and n there), reserves 8 more
   stack bytes, CALLs memchr (0x123940) and returns p-s, or n when memchr
   returns NULL (CMOVZ).  memchr's contract (memchr_proof.v), including its
   stack_frame clause, is used through call_leaf_ni.

   SPECIFICATION (man 3 strnlen, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <string.h>
            size_t strnlen(const char s[.maxlen], size_t maxlen);

     DESCRIPTION
            The strnlen() function returns the number of bytes in the string
            pointed to by s, excluding the terminating null byte ('\0'), but
            at most maxlen.  In doing this, strnlen() looks only at the first
            maxlen characters in the string pointed to by s and never beyond
            s[maxlen-1].

     RETURN VALUE
            The strnlen() function returns strlen(s), if that is less than
            maxlen, or maxlen if there is no null terminating ('\0') among
            the first maxlen characters pointed to by s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            strnlen at 0x65b81, memchr at 0x23940 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/strnlen_amd64.v, memchr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = maxlen n; RSP = rsp; m = memory.  Preconditions
            (strnlen_ok): s <> 0 and s + n <= 2^64 (the area is a C object:
            not at NULL and not wrapping; otherwise a NUL at address 0 would
            make memchr's result look like "not found"), and the n bytes at s
            do not overlap the 40 bytes below rsp (strnlen's and memchr's
            stack).  s need not be terminated.
   Output:  At the RET (0x165baa): RAX = K where K <= n, s[0..K) are all
            nonzero, and s[K] = 0 if K < n.  No byte outside the 40 bytes
            below rsp has changed; RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strnlen_amd64 CoqEtTu.programs.memchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.memchr_proof.
Open Scope N.

Definition strnlen_program : program := updateall2 strnlen_amd64 memchr_amd64.

Lemma strnlen_program_welltyped: welltyped_prog x64typctx strnlen_program.
Proof.
  intros s a. unfold strnlen_program, updateall2, updateall.
  destruct (memchr_amd64 s a) as [[sz q]|] eqn:SC.
    pose proof (memchr_welltyped s a) as WT. rewrite SC in WT. exact WT.
    apply strnlen_amd64.welltyped.
Qed.

Theorem strnlen_welltyped: welltyped_prog x64typctx strnlen_amd64.
Proof. exact strnlen_amd64.welltyped. Qed.

Definition strnlen_ok (p n rsp:N) := 0 < p /\ p + n <= 2^64 /\ ~ overlap 64 p n (rsp ⊖ 40) 40.

Definition strnlen_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x165baa => true
  | _ => false end | _ => false end.

Definition strnlen_post (s0:store) (m p n:N) (s:store) :=
  (exists K, K <= n /\ cabsent m p 0 K /\ (K < n -> m Ⓑ[p ⊕ K] = 0) /\ s R_RAX = K) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 40 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition strnlen_invs (s0:store) (m p n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x165b81 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ strnlen_ok p n (s0 R_RSP) /\
                      s0 R_RSP < 2^64)
  | 0x165b92 => Some (s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX] /\
                      s R_RDI = p /\ s R_RSI = 0 /\ s R_RDX = n /\
                      s R_RBX = n /\ s R_RBP = p /\ s R_RSP = s0 R_RSP ⊖ 24 /\
                      s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
                      s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15 /\
                      strnlen_ok p n (s0 R_RSP) /\ s0 R_RSP < 2^64 /\ s0 R_RBX < 2^64 /\
                      s0 R_RBP < 2^64)
  | 0x165baa => Some (strnlen_post s0 m p n s)
  | _ => None
  end | _ => None end.

(* The three stack writes leave the buffer alone. *)
Lemma push3_off:
  forall m p n rsp v1 v2 v3 i, ~ overlap 64 p n (rsp ⊖ 40) 40 -> i < n ->
  (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) Ⓑ[p ⊕ i] = m Ⓑ[p ⊕ i].
Proof.
  intros m p n rsp v1 v2 v3 i NOV I.
  rewrite getmem_noverlap. rewrite getmem_noverlap. rewrite getmem_noverlap. reflexivity.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (32 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (24 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
  - intros [a [y [A [Y E]]]]. apply NOV. exists i, (8 + y). split. lia. split. lia.
    unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma strnlen_ok_memchr:
  forall p n rsp, strnlen_ok p n rsp -> ~ overlap 64 p n (rsp ⊖ 32 ⊖ 8) 8.
Proof.
  intros p n rsp [_ [_ NOV]] [x [y [X [Y E]]]]. apply NOV. exists x, y. split. lia. split. lia.
  unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma cabsent_push3:
  forall m p n rsp v1 v2 v3 K, ~ overlap 64 p n (rsp ⊖ 40) 40 -> K <= n ->
  cabsent (m [Ⓠrsp ⊖ 8 := v1] [Ⓠrsp ⊖ 16 := v2] [Ⓠrsp ⊖ 32 := v3]) p 0 K -> cabsent m p 0 K.
Proof.
  intros m p n rsp v1 v2 v3 K NOV KN CA i I.
  rewrite <- (push3_off m p n rsp v1 v2 v3 i NOV) by lia. apply CA, I.
Qed.

Lemma found_nonnull: forall p n K, 0 < p -> p + n <= 2^64 -> K < n -> p ⊕ K <> 0.
Proof. intros p n K P PN KN. rewrite N.mod_small by lia. lia. Qed.

Lemma found_sub: forall p n K, p + n <= 2^64 -> K < n -> msub 64 (p ⊕ K) p = K.
Proof. intros p n K PN KN. rewrite N.mod_small by lia. unfold msub. change (2^64) with 18446744073709551616 in *. lia. Qed.

Theorem strnlen_correct:
  forall prog s t s' x' m p n
         (STRNLEN: strnlen_amd64 ⊆2 prog) (MEMCHR: memchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x165b81, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (Nn: s R_RSI = n)
         (OK: strnlen_ok p n (s R_RSP)),
  satisfies_all prog (strnlen_invs s m p n) strnlen_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p n STRNLEN MEMCHR ENTRY MDL MEM P Nn OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=strnlen_program).
    unfold strnlen_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold strnlen_invs.
    unfold strnlen_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p n MDL MEM P Nn OK RB RBXB RBPB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strnlen_program_welltyped. intro MDL1.
  clear - PRE MDL1 RB RBXB RBPB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [Nn [RSP [CS [OK RB']]]]]].
    repeat x64_step.
    destruct CS as (B & BP & B12 & B13 & B14 & B15). rewrite B, BP. conj_tac.
  - destruct PRE as [MEM [RDI [RSI [RDX [RBX [RBP [RSP [R12 [R13 [R14 [R15 [OK [RB' [RBXB' RBPB']]]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps strnlen_program _ _ _ _ s2 nil _ s1 t MDL1 strnlen_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni strnlen_program memchr_amd64 _ _
              (memchr_invs s2 (s2 V_MEM64) p 0 n) memchr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold memchr_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply memchr_correct; first
        [ apply pf2sub_refl | assumption | reflexivity
        | (unfold s2; rewrite !update_frame by discriminate; assumption)
        | (unfold s2; rewrite update_frame, update_updated by discriminate;
           replace (s0 R_RSP ⊖ 24 ⊖ 8) with (s0 R_RSP ⊖ 32) by mlia64;
           apply strnlen_ok_memchr; assumption) ].
    + intros a s t' NC. unfold strnlen_invs, strnlen_exit.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold memchr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (memchr_exit _) eqn:EX; [|destruct PRE].
      unfold memchr_exit in EX. addr_cases EX.
      all: simpl in PRE.
      all: apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 strnlen_program_welltyped).
      all: intro MDL3.
      all: destruct PRE as [RES [FR [RSP' CS']]].
      all: unfold s2 in *.
      all: rewrite !update_frame, update_updated in RSP' by discriminate.
      all: rewrite update_updated in RES, FR.
      all: rewrite update_frame, update_updated in FR by discriminate.
      all: change (0 mod 2^8) with 0 in RES.
      all: destruct OK as [P0 [PN NOV]].
      all: set (m1 := m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 16 := s0 R_RBX] [Ⓠs0 R_RSP ⊖ 32 := 1465239]) in *.
      all: assert (RQ: forall k, k = 8 \/ k = 16 \/ k = 32 -> s' V_MEM64 Ⓠ[s0 R_RSP ⊖ k] = m1 Ⓠ[s0 R_RSP ⊖ k]) by
             (intros k K; apply (stack_frame_get8 _ _ (s0 R_RSP ⊖ 32) 8 _ FR); [reflexivity | mlia64]).
      all: assert (RA: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 32] = 1465239) by
             (rewrite RQ by (right; right; reflexivity); subst m1;
              rewrite getmem_setmem by discriminate; reflexivity).
      all: assert (R16: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = s0 R_RBX) by
             (rewrite RQ by (right; left; reflexivity); subst m1;
              rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64);
              rewrite getmem_setmem by discriminate; apply N.mod_small; assumption).
      all: assert (R8: s' V_MEM64 Ⓠ[s0 R_RSP ⊖ 8] = s0 R_RBP) by
             (rewrite RQ by (left; reflexivity); subst m1;
              rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64);
              rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia64);
              rewrite getmem_setmem by discriminate; apply N.mod_small; assumption).
      all: x64_step; rewrite RA; repeat x64_step.
      all: bc_norm.
      all: assert (RBXv: s' R_RBX = n) by (rewrite (proj1 CS'), !update_frame by discriminate; exact RBX).
      all: assert (RBPv: s' R_RBP = p) by (rewrite (proj1 (proj2 CS')), !update_frame by discriminate; exact RBP).
      all: assert (CSb: s' R_R12 = s0 R_R12 /\ s' R_R13 = s0 R_R13 /\ s' R_R14 = s0 R_R14 /\
                        s' R_R15 = s0 R_R15) by
             (destruct CS' as (_ & _ & C & D' & E & F); rewrite C, D', E, F;
              rewrite !update_frame by discriminate; repeat split; assumption).
      all: rewrite ?RBXv, ?RBPv in *.
      all: split; [ destruct RES as [[K [KN [CA [BK RV]]]] | [CA RV]];
        [ (* found at K *)
          rewrite RV in *; exists K; split; [lia|];
          split; [apply (cabsent_push3 m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1465239); assumption || lia|];
          split; [intros _; rewrite <- (push3_off m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1465239 K NOV KN); exact BK|];
          first [ apply (found_sub p n K); assumption
                | exfalso; apply (found_nonnull p n K); assumption ]
        | (* not found *)
          rewrite RV in *; exists n; split; [lia|];
          split; [apply (cabsent_push3 m p n (s0 R_RSP) (s0 R_RBP) (s0 R_RBX) 1465239); assumption || lia|];
          split; [intros; lia|];
          first [ reflexivity | exfalso; congruence ] ] |].
      all: split; [ intros b B; rewrite FR by mlia64;
                    subst m1;
                    rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 40) by (assumption || reflexivity || lia);
                    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 40) by (assumption || reflexivity || lia);
                    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 40) by (assumption || reflexivity || lia);
                    reflexivity |].
      all: split; [apply N.mod_small; assumption|].
      all: destruct CSb as (C12 & C13 & C14 & C15).
      all: repeat split; rewrite ?update_frame by discriminate;
           first [ assumption | rewrite update_updated; first [exact R16 | exact R8]
                 | rewrite update_frame, update_updated by discriminate; first [exact R16 | exact R8] ].
Qed.

