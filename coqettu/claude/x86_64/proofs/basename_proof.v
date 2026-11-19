(* basename -- strip directory from a path (musl x86_64, C), composed with
   strlen

   SEMANTICS
   ---------
   musl's basename (src/misc/basename.c) is

       char *basename(char *s)
       {
           size_t i;
           if (!s || !*s) return ".";
           i = strlen(s)-1;
           for (; i&&s[i]=='/'; i--) s[i] = 0;
           for (; i&&s[i-1]!='/'; i--);
           return s+i;
       }

   The binary returns the static "." (0x1a22a6) for NULL or "", else spills
   s, CALLs strlen (0x1348c0), strips trailing slashes in place and scans
   back to the previous slash.  strlen's contract (strlen_proof.v) is used
   through call_leaf_ni.

   SPECIFICATION (man 3 basename, Linux man-pages 6.9.1, paraphrased)
   -----------------------------------------------------------------
     char *basename(char *path);
     basename returns the component following the final '/' of path;
     trailing '/' characters are not counted as part of the pathname.  If
     path is NULL or empty, "." is returned.  basename may modify path (here:
     it overwrites trailing slashes, except one at index 0, with NULs).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            basename at 0x3b350, strlen at 0x348c0, "." at 0xa22a6 (Ghidra
            image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/basename_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; RSP = rsp; m = memory.  Precondition (bn_ok): s = 0, or
            s is a string of length L whose L+1 bytes do not overlap the 32
            bytes below rsp.
   Output:  At a RET: if s = 0 or s[0] = 0, RAX = 0x1a22a6 and memory is
            unchanged outside the stack.  Otherwise, with L = strlen(s) >= 1,
            there are j <= L-1 and i <= j such that s[k] = '/' for
            j < k <= L-1 and (j = 0 or s[j] <> '/') (trailing slashes), and
            s[k-1] <> '/' for i < k <= j and (i = 0 or s[i-1] = '/') (start of
            the last component); RAX = s + i; the bytes s[j+1 .. L-1] are now
            0 and every other byte outside the 32 bytes below rsp is
            unchanged.  RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.basename_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof.
Open Scope N.

Definition basename_program : program := updateall2 basename_amd64 strlen_amd64.

Theorem basename_welltyped: welltyped_prog x64typctx basename_amd64.
Proof. exact basename_amd64.welltyped. Qed.

Lemma basename_program_welltyped: welltyped_prog x64typctx basename_program.
Proof.
  intros s a. unfold basename_program, updateall2, updateall.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply basename_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition dot := 0x1a22a6.

Definition bn_ok (m s rsp:N) :=
  s = 0 \/ exists L, nilfree m s L /\ m Ⓑ[s ⊕ L] = 0 /\ ~ overlap 64 s (L + 1) (rsp ⊖ 32) 32.

(* the bytes s[j+1 .. L-1] are 0; everything else is as in M0 *)
Definition zf (M0 M:memory) (s j L:N) :=
  (forall k, j < k < L -> M Ⓑ[s ⊕ k] = 0) /\
  (forall b, ~ (j < msub 64 b s < L) -> M Ⓑ[b] = M0 Ⓑ[b]).

Definition trail (m:memory) (s j L:N) := forall k, j < k < L -> m Ⓑ[s ⊕ k] = 47.

Definition basename_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13b361 | 0x13b3aa | 0x13b3ab => true
  | _ => false end | _ => false end.

Definition basename_post (s0:store) (m p:N) (s:store) :=
  (((p = 0 \/ m Ⓑ[p] = 0) /\ s R_RAX = dot /\
    (forall b, 32 <= msub 64 b (s0 R_RSP ⊖ 32) -> s V_MEM64 Ⓑ[b] = m Ⓑ[b])) \/
   (exists L j i, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ 1 <= L /\ j < L /\ trail m p j L /\
      (j = 0 \/ m Ⓑ[p ⊕ j] <> 47) /\ i <= j /\
      (forall k, i < k <= j -> m Ⓑ[p ⊕ (k - 1)] <> 47) /\ (i = 0 \/ m Ⓑ[p ⊕ (i - 1)] = 47) /\
      s R_RAX = p ⊕ i /\
      (forall k, j < k < L -> s V_MEM64 Ⓑ[p ⊕ k] = 0) /\
      (forall b, ~ (j < msub 64 b p < L) -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                 s V_MEM64 Ⓑ[b] = m Ⓑ[b]))) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition mb (s0:store) (m p:N) := m [Ⓠs0 R_RSP ⊖ 16 := p] [Ⓠs0 R_RSP ⊖ 32 := 0x13b370].

Definition basename_invs (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13b350 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13b36b => Some (p <> 0 /\ m Ⓑ[p] <> 0 /\ s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := p] /\
                      s R_RDI = p /\ s R_RSP = s0 R_RSP ⊖ 24 /\ callee_saved_eq s0 s)
  | 0x13b379 => Some (exists L i, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ 1 <= L /\
                      ~ overlap 64 p (L + 1) (s0 R_RSP ⊖ 32) 32 /\ i < L /\
                      trail m p i L /\ zf (mb s0 m p) (s V_MEM64) p i L /\
                      s R_RDI = p /\ s R_RAX = i /\ s R_RSP = s0 R_RSP ⊖ 24 /\ callee_saved_eq s0 s)
  | 0x13b394 => Some (exists L j i, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ 1 <= L /\
                      ~ overlap 64 p (L + 1) (s0 R_RSP ⊖ 32) 32 /\ j < L /\
                      trail m p j L /\ (j = 0 \/ m Ⓑ[p ⊕ j] <> 47) /\ i <= j /\
                      (forall k, i < k <= j -> m Ⓑ[p ⊕ (k - 1)] <> 47) /\
                      zf (mb s0 m p) (s V_MEM64) p j L /\
                      s R_RDI = p /\ s R_RAX = i /\ s R_RSP = s0 R_RSP ⊖ 24 /\ callee_saved_eq s0 s)
  | 0x13b361 | 0x13b3aa | 0x13b3ab => Some (basename_post s0 m p s)
  | _ => None
  end | _ => None end.

Lemma mb_frame: forall s0 m p b, 32 <= msub 64 b (s0 R_RSP ⊖ 32) -> mb s0 m p Ⓑ[b] = m Ⓑ[b].
Proof.
  intros. unfold mb.
  rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 32) by (assumption || lia).
  rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 32) by (assumption || lia).
  reflexivity.
Qed.

Lemma outside32:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 32) 32 -> i < n -> 32 <= msub 64 (x ⊕ i) (rsp ⊖ 32).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 32 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 32) in *. clearbody b.
  destruct (N.le_gt_cases 32 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

Lemma mb_slot: forall s0 m p, p < 2^64 -> mb s0 m p Ⓠ[s0 R_RSP ⊖ 16] = p.
Proof.
  intros. unfold mb. rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma zf_init: forall M0 p L, 1 <= L -> zf M0 M0 p (L - 1) L.
Proof. intros. split. intros k K. lia. reflexivity. Qed.

Lemma zf_store:
  forall M0 M p i L, zf M0 M p i L -> 0 < i -> i < L -> L < 2^64 ->
  zf M0 (setmem 64 LittleE 1 M (p + i) 0) p (i - 1) L.
Proof.
  intros M0 M p i L [Z F] I0 IL LB. split.
  - intros k K. destruct (N.eq_dec k i) as [->|NE].
    + rewrite getmem_mod_l, getmem_setmem by discriminate. reflexivity.
    + rewrite getmem_noverlap. apply Z. lia.
      intros [x [y [X [Y E]]]]. apply NE. mlia.
  - intros b B. rewrite getmem_noverlap. apply F. intro H. apply B. lia.
    intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

Lemma zf_read: forall M0 M p j L k, zf M0 M p j L -> k <= j -> k < 2^64 ->
  M Ⓑ[p ⊕ k] = M0 Ⓑ[p ⊕ k].
Proof.
  intros M0 M p j L k [_ F] K KB. apply F. intros [H1 H2].
  assert (E: msub 64 (p ⊕ k) p = k) by mlia. lia.
Qed.

Lemma nilfree_unique':
  forall m p a b, nilfree m p a -> m Ⓑ[p ⊕ a] = 0 -> nilfree m p b -> m Ⓑ[p ⊕ b] = 0 -> a = b.
Proof.
  intros m p a b NA ZA NB ZB. destruct (N.lt_trichotomy a b) as [H|[H|H]].
  - exfalso. exact (NB a H ZA).
  - exact H.
  - exfalso. exact (NA b H ZB).
Qed.

Lemma addr_m1: forall p i, 1 <= i -> p < 2^64 -> (p ⊖ 1 + i) mod 2^64 = p ⊕ (i - 1).
Proof. intros. mlia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Theorem basename_correct:
  forall prog s t s' x' m p
         (BASENAME: basename_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13b350, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p)
         (OK: bn_ok m p (s R_RSP)),
  satisfies_all prog (basename_invs s m p) basename_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p BASENAME STRLEN ENTRY MDL MEM P OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=basename_program).
    unfold basename_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold basename_invs.
    unfold basename_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p MDL MEM P OK RB PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply basename_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB PB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [RSP CS]]].
    repeat x64_step.
    + match goal with BC: (p =? 0) = true |- _ => apply N.eqb_eq in BC end.
      split. left. split. left. assumption. split. reflexivity. intros b B. rewrite MEM. reflexivity.
      conj_tac.
    + match goal with BC: (m Ⓑ[p] =? 0) = true |- _ => apply N.eqb_eq in BC end.
      split. left. split. right. assumption. split. reflexivity. intros b B. reflexivity.
      conj_tac.
    + match goal with BC: (p =? 0) = false |- _ => apply N.eqb_neq in BC end.
      match goal with BC: (m Ⓑ[p] =? 0) = false |- _ => apply N.eqb_neq in BC end.
      conj_tac.
  - (* call strlen(s) *)
    destruct PRE as [P0 [Z0 [MEM [RDI [RSP CS]]]]].
    destruct OK as [OK|(L & NL & ZL & NOV)]; [contradiction|].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (L1: 1 <= L).
    { destruct (N.eq_dec L 0) as [E|E]. exfalso. apply Z0. subst L. rewrite N.add_0_r, N.mod_small in ZL by exact PB. exact ZL. lia. }
    assert (MBB: forall k, k <= L -> mb s0 m p Ⓑ[p ⊕ k] = m Ⓑ[p ⊕ k])
      by (intros k K; apply mb_frame, (outside32 p (L + 1)); [exact NOV | lia]).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps basename_program _ _ _ _ s2 nil _ s1 t MDL1 basename_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni basename_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) p) strlen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold basename_invs, basename_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 basename_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z, RSP'.
      fold (mb s0 m p) in MEM', NF, Z.
      assert (KE: k = L).
      { apply (nilfree_unique' _ p k L NF Z).
        - intros i I. rewrite MBB by (clear - I; lia). apply NL, I.
        - rewrite MBB by (clear; lia). exact ZL. }
      subst k.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      pose proof (mb_slot s0 m p PB) as SL16.
      assert (RA: mb s0 m p Ⓠ[s0 R_RSP ⊖ 32] = 0x13b370) by (unfold mb; rewrite getmem_setmem by discriminate; reflexivity).
      x64_step. rewrite RA. repeat x64_step.
      assert (M1: msub 64 L 1 = L - 1) by (clear - L1 LB; mlia).
      exists L, (L - 1). split. exact NL. split. exact ZL. split. exact L1. split. exact NOV. split. clear - L1; lia.
      split. intros k K. exfalso. clear - K; lia.
      split. apply zf_init, L1. split. exact SL16. split. exact M1. split. reflexivity.
      destruct CS as (B0 & B1 & B2 & B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg;
        first [sassumption | (rewrite ?C0, ?C1, ?C2, ?C3, ?C4, ?C5; sassumption)].
  - destruct PRE as [L [i [NL [ZL [L1 [NOV [IL [TR [ZF [RDI [RAX [RSP CS]]]]]]]]]]]].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (BI: s1 V_MEM64 Ⓑ[p + i] = m Ⓑ[p ⊕ i]).
    { rewrite <- getmem_mod_l. rewrite (zf_read _ _ p i L i ZF (N.le_refl i)) by (clear - IL LB; lia).
      apply mb_frame, (outside32 p (L + 1)). exact NOV. clear - IL; lia. }
    repeat x64_step.
    all: rewrite ?BI in *.
    + match goal with BC: (i =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into I0 end.
      rewrite I0 in TR, ZF.
      split. right. exists L, 0, 0. split. exact NL. split. exact ZL. split. exact L1. split. clear - L1; lia.
        split. exact TR. split. left; reflexivity. split. reflexivity.
        split. intros k K. exfalso. clear - K; lia. split. left; reflexivity.
        split. rewrite N.add_0_r, N.mod_small by exact PB. reflexivity.
        split. exact (proj1 ZF).
        intros b B1 B2. rewrite (proj2 ZF b B1). apply mb_frame, B2.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (m Ⓑ[p ⊕ i] =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SL end.
      exists L, (i - 1). split. exact NL. split. exact ZL. split. exact L1. split. exact NOV.
      split. clear - IL; lia.
      split. intros k K. destruct (N.eq_dec k i) as [->|NE]. exact SL. apply TR. clear - K NE; lia.
      split. apply zf_store; try assumption. clear - I0; lia.
      split. reflexivity. split. clear - I0 IL LB; mlia.
      conj_tac.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (m Ⓑ[p ⊕ i] =? 47) = false |- _ => apply N.eqb_neq in BC; rename BC into SL end.
      exists L, i, i. split. exact NL. split. exact ZL. split. exact L1. split. exact NOV.
      split. exact IL. split. exact TR. split. right. exact SL. split. reflexivity.
      split. intros k K. exfalso. clear - K; lia.
      conj_tac.
  - destruct PRE as [L [j [i [NL [ZL [L1 [NOV [JL [TR [JS [IJ [NS [ZF [RDI [RAX [RSP CS]]]]]]]]]]]]]]]].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (BI: 1 <= i -> s1 V_MEM64 Ⓑ[p ⊖ 1 + i] = m Ⓑ[p ⊕ (i - 1)]).
    { intro I1. rewrite <- getmem_mod_l, (addr_m1 p i I1 PB).
      rewrite (zf_read _ _ p j L (i - 1) ZF) by (clear - IJ JL LB; lia).
      apply mb_frame, (outside32 p (L + 1)). exact NOV. clear - IJ JL; lia. }
    repeat x64_step.
    + match goal with BC: (i =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into I0 end.
      rewrite I0 in NS, IJ.
      split. right. exists L, j, 0. split. exact NL. split. exact ZL. split. exact L1. split. exact JL.
        split. exact TR. split. exact JS. split. exact IJ. split. exact NS. split. left; reflexivity.
        split. rewrite N.add_0_r, N.mod_small by exact PB. reflexivity.
        split. exact (proj1 ZF).
        intros b B1 B2. rewrite (proj2 ZF b B1). apply mb_frame, B2.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SL end.
      rewrite BI in SL by (clear - I0; lia).
      split. right. exists L, j, i. split. exact NL. split. exact ZL. split. exact L1. split. exact JL.
        split. exact TR. split. exact JS. split. exact IJ. split. exact NS. split. right; exact SL.
        split. reflexivity.
        split. exact (proj1 ZF).
        intros b B1 B2. rewrite (proj2 ZF b B1). apply mb_frame, B2.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = false |- _ => apply N.eqb_neq in BC; rename BC into SL end.
      rewrite BI in SL by (clear - I0; lia).
      exists L, j, (i - 1). split. exact NL. split. exact ZL. split. exact L1. split. exact NOV.
      split. exact JL. split. exact TR. split. exact JS. split. clear - IJ; lia.
      split. intros k K. destruct (N.eq_dec k i) as [->|NE]. exact SL. apply NS. clear - K NE; lia.
      split. exact ZF. split. reflexivity. split. clear - I0 IJ JL LB; mlia.
      conj_tac.
Qed.
