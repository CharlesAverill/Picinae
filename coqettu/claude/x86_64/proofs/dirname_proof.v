(* dirname -- parent directory of a path (musl x86_64, C), composed with
   strlen

   SEMANTICS
   ---------
   musl's dirname (src/misc/dirname.c) is

       char *dirname(char *s)
       {
           size_t i;
           if (!s || !*s) return ".";
           i = strlen(s)-1;
           for (; s[i]=='/'; i--) if (!i) return "/";
           for (; s[i]!='/'; i--) if (!i) return ".";
           for (; s[i]=='/'; i--) if (!i) return "/";
           s[i+1] = 0;
           return s;
       }

   The binary returns the static "." (0x1a22a6) or "/" (0x1a282c), else
   spills s, CALLs strlen (0x1348c0, call_leaf_ni over strlen_proof.v) and
   runs the three loops (cuts 0x13b3e5, 0x13b400, 0x13b424).

   SPECIFICATION (man 3 dirname, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     char *dirname(char *path);
     dirname returns the string up to, but not including, the final '/';
     trailing '/' characters are not counted as part of the pathname.  If
     path does not contain a slash, dirname returns ".".  If path is "/",
     dirname returns "/".  If path is NULL or empty, "." is returned.
     dirname may modify path (here: it writes one NUL).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            dirname at 0x3b3b0, strlen at 0x348c0, "." at 0xa22a6, "/" at
            0xa282c (bytes 2e 00 and 2f 00; Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/dirname_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; RSP = rsp; m = memory.  Precondition (bn_ok, shared with
            basename): s = 0, or s is a string of length L whose L+1 bytes do
            not overlap the 32 bytes below rsp.
   Output:  At a RET (dirname_post): if s = 0 or s[0] = 0, RAX = "." .
            Otherwise, with L = strlen(s) >= 1, exactly one shape holds:
            (1) s is all '/': RAX = "/";
            (2) s = A B with A nonempty and slash-free, B all '/': RAX = ".";
            (3) s = S A B with S nonempty all '/', A nonempty slash-free, B
                all '/': RAX = "/";
            (4) s = P S A B with P nonempty ending in a non-'/' at index h, S
                nonempty all '/', A nonempty slash-free, B all '/': s[h+1]
                is now 0 and RAX = s.
            Every other byte outside the 32 bytes below rsp is unchanged.
            RSP = rsp; RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.dirname_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.basename_proof.
Open Scope N.

Definition dirname_program : program := updateall2 dirname_amd64 strlen_amd64.

Theorem dirname_welltyped: welltyped_prog x64typctx dirname_amd64.
Proof. exact dirname_amd64.welltyped. Qed.

Lemma dirname_program_welltyped: welltyped_prog x64typctx dirname_program.
Proof.
  intros s a. unfold dirname_program, updateall2, updateall.
  destruct (strlen_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (strlen_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply dirname_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition slash := 0x1a282c.

(* s[a..b] are all '/', resp. none is *)
Definition allsl (m:memory) (s a b:N) := forall k, a <= k <= b -> m Ⓑ[s ⊕ k] = 47.
Definition nosl (m:memory) (s a b:N) := forall k, a <= k <= b -> m Ⓑ[s ⊕ k] <> 47.

(* memory unchanged outside the 32 bytes below rsp *)
Definition fu (M m:memory) (rsp:N) := forall b, 32 <= msub 64 b (rsp ⊖ 32) -> M Ⓑ[b] = m Ⓑ[b].

Definition dirname_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13b3c1 | 0x13b3cd => true
  | _ => false end | _ => false end.

Definition dirname_post (s0:store) (m p:N) (s:store) :=
  (((p = 0 \/ m Ⓑ[p] = 0) /\ s R_RAX = dot /\ fu (s V_MEM64) m (s0 R_RSP)) \/
   (exists L, nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ 1 <= L /\
    ((allsl m p 0 (L - 1) /\ s R_RAX = slash /\ fu (s V_MEM64) m (s0 R_RSP)) \/
     (exists j, j < L /\ trail m p j L /\ nosl m p 0 j /\
                s R_RAX = dot /\ fu (s V_MEM64) m (s0 R_RSP)) \/
     (exists j i, i < j /\ j < L /\ trail m p j L /\ nosl m p (i + 1) j /\ allsl m p 0 i /\
                  s R_RAX = slash /\ fu (s V_MEM64) m (s0 R_RSP)) \/
     (exists j i h, h < i /\ i < j /\ j < L /\ trail m p j L /\ nosl m p (i + 1) j /\ allsl m p (h + 1) i /\
                    m Ⓑ[p ⊕ h] <> 47 /\ s R_RAX = p /\ s V_MEM64 Ⓑ[p ⊕ (h + 1)] = 0 /\
                    (forall b, msub 64 b p <> h + 1 -> 32 <= msub 64 b (s0 R_RSP ⊖ 32) ->
                               s V_MEM64 Ⓑ[b] = m Ⓑ[b]))))) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition md (s0:store) (m p:N) := m [Ⓠs0 R_RSP ⊖ 16 := p] [Ⓠs0 R_RSP ⊖ 32 := 0x13b3dc].

Definition dn_common (s0:store) (m p L:N) (s:store) :=
  nilfree m p L /\ m Ⓑ[p ⊕ L] = 0 /\ 1 <= L /\ ~ overlap 64 p (L + 1) (s0 R_RSP ⊖ 32) 32 /\
  s V_MEM64 = md s0 m p /\ s R_RDI = p /\ s R_RSP = s0 R_RSP ⊖ 24 /\ callee_saved_eq s0 s.

Definition dirname_invs (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13b3b0 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13b3d7 => Some (p <> 0 /\ m Ⓑ[p] <> 0 /\ s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := p] /\
                      s R_RDI = p /\ s R_RSP = s0 R_RSP ⊖ 24 /\ callee_saved_eq s0 s)
  | 0x13b3e5 => Some (exists L i, dn_common s0 m p L s /\ i < L /\ trail m p i L /\ s R_RAX = i)
  | 0x13b400 => Some (exists L j i, dn_common s0 m p L s /\ j < L /\ trail m p j L /\ i <= j /\
                      nosl m p i j /\ s R_RAX = i)
  | 0x13b424 => Some (exists L j i h, dn_common s0 m p L s /\ j < L /\ trail m p j L /\ i < j /\
                      nosl m p (i + 1) j /\ h <= i /\ allsl m p (h + 1) i /\ m Ⓑ[p ⊕ i] = 47 /\
                      s R_RAX = h)
  | 0x13b3c1 | 0x13b3cd => Some (dirname_post s0 m p s)
  | _ => None
  end | _ => None end.

Lemma md_frame: forall s0 m p b, 32 <= msub 64 b (s0 R_RSP ⊖ 32) -> md s0 m p Ⓑ[b] = m Ⓑ[b].
Proof.
  intros. unfold md.
  rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 32) by (assumption || lia).
  rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 32) by (assumption || lia).
  reflexivity.
Qed.

Lemma md_fu: forall s0 m p, fu (md s0 m p) m (s0 R_RSP).
Proof. intros s0 m p b B. apply md_frame, B. Qed.

Lemma md_slot: forall s0 m p, p < 2^64 -> md s0 m p Ⓠ[s0 R_RSP ⊖ 16] = p.
Proof.
  intros. unfold md. rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia).
  rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

(* the string's bytes through the terminator are those of m *)
Lemma md_byte: forall s0 m p L k, ~ overlap 64 p (L + 1) (s0 R_RSP ⊖ 32) 32 -> k <= L ->
  md s0 m p Ⓑ[p + k] = m Ⓑ[p ⊕ k].
Proof.
  intros s0 m p L k NOV K. rewrite <- getmem_mod_l. apply md_frame, (outside32 p (L + 1)). exact NOV. lia.
Qed.

Lemma cut_byte: forall (M:memory) p h, M [Ⓑ1 + p + h := 0] Ⓑ[p ⊕ (h + 1)] = 0.
Proof.
  intros. rewrite getmem_mod_l. replace (p + (h + 1)) with (1 + p + h) by lia.
  rewrite getmem_setmem by discriminate. reflexivity.
Qed.

Lemma cut_other: forall (M:memory) p h b, h + 1 < 2^64 -> msub 64 b p <> h + 1 ->
  M [Ⓑ1 + p + h := 0] Ⓑ[b] = M Ⓑ[b].
Proof.
  intros M p h b H B. rewrite getmem_noverlap. reflexivity.
  intros [x [y [X [Y E]]]]. apply B. mlia.
Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac dn := unfold dn_common; repeat split; reg; first [sassumption | sreflexivity].

Theorem dirname_correct:
  forall prog s t s' x' m p
         (DIRNAME: dirname_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13b3b0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p)
         (OK: bn_ok m p (s R_RSP)),
  satisfies_all prog (dirname_invs s m p) dirname_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p DIRNAME STRLEN ENTRY MDL MEM P OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=dirname_program).
    unfold dirname_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold dirname_invs.
    unfold dirname_program, updateall2, updateall in NOCODE.
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
  eapply models_at_invariant; try eassumption. apply dirname_program_welltyped. intro MDL1.
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
    assert (MBB: forall k, k <= L -> md s0 m p Ⓑ[p ⊕ k] = m Ⓑ[p ⊕ k])
      by (intros k K; apply md_frame, (outside32 p (L + 1)); [exact NOV | lia]).
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps dirname_program _ _ _ _ s2 nil _ s1 t MDL1 dirname_program_welltyped).
    intro MDL2.
    eapply (call_leaf_ni dirname_program strlen_amd64 _ _ (strlen_invs s2 (s2 V_MEM64) p) strlen_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strlen_invs.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strlen_correct; first
        [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
    + intros a s t' NC. unfold dirname_invs, dirname_exit.
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
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 dirname_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [RAX [NF Z]]] [MEM' [RSP' CS']]].
      unfold s2 in *. rewrite !update_frame in RSP' by discriminate. rewrite update_updated in MEM', NF, Z, RSP'.
      fold (md s0 m p) in MEM', NF, Z.
      assert (KE: k = L).
      { apply (nilfree_unique' _ p k L NF Z).
        - intros i I. rewrite MBB by (clear - I; lia). apply NL, I.
        - rewrite MBB by (clear; lia). exact ZL. }
      subst k.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      pose proof (md_slot s0 m p PB) as SL16.
      assert (RA: md s0 m p Ⓠ[s0 R_RSP ⊖ 32] = 0x13b3dc) by (unfold md; rewrite getmem_setmem by discriminate; reflexivity).
      x64_step. rewrite RA. repeat x64_step.
      assert (M1: msub 64 L 1 = L - 1) by (clear - L1 LB; mlia).
      exists L, (L - 1). split.
      * unfold dn_common. split. exact NL. split. exact ZL. split. exact L1. split. exact NOV.
        split. reg. first [exact MEM' | sreflexivity]. split. reg. exact SL16. split. reg. reflexivity.
        destruct CS as (B0 & B1 & B2 & B3 & B4 & B5). unfold callee_saved_eq. repeat split; reg;
          first [sassumption | (rewrite ?C0, ?C1, ?C2, ?C3, ?C4, ?C5; sassumption)].
      * split. clear - L1; lia. split. intros k K. exfalso. clear - K; lia. exact M1.
  - destruct PRE as [L [i [[NL [ZL [L1 [NOV [MEM [RDI [RSP CS]]]]]]] [IL [TR RAX]]]]].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (BI: md s0 m p Ⓑ[p + i] = m Ⓑ[p ⊕ i]) by (apply (md_byte s0 m p L i NOV); clear - IL; lia).
    repeat x64_step.
    all: rewrite ?BI in *.
    all: pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
    + match goal with BC: (i =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SL end.
      split. right. exists L. split. exact NL. split. exact ZL. split. exact L1. left.
        split. intros k K. destruct (N.eq_dec k 0) as [->|NE]. rewrite I0 in SL. exact SL.
          apply TR. clear - K NE I0 L1; lia.
        split. reflexivity. apply md_fu.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SL end.
      exists L, (i - 1). split. dn.
      split. clear - IL; lia.
      split. intros k K. destruct (N.eq_dec k i) as [->|NE]. exact SL. apply TR. clear - K NE; lia.
      clear - I0 IL LB; mlia.
    + match goal with BC: (_ =? 47) = false |- _ => apply N.eqb_neq in BC; rename BC into SL end.
      exists L, i, i. split. dn.
      split. exact IL. split. exact TR. split. apply N.le_refl.
      split. intros k K. replace k with i by (clear - K; lia). exact SL. reflexivity.
  - destruct PRE as [L [j [i [[NL [ZL [L1 [NOV [MEM [RDI [RSP CS]]]]]]] [JL [TR [IJ [NS RAX]]]]]]]].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (BI2: 1 <= i -> md s0 m p Ⓑ[p + i ⊖ 1] = m Ⓑ[p ⊕ (i - 1)]).
    { intro I1. rewrite <- getmem_mod_l.
      replace ((p + i ⊖ 1) mod 2^64) with ((p + (i - 1)) mod 2^64) by (clear - I1 PB; mlia).
      rewrite getmem_mod_l. apply (md_byte s0 m p L (i - 1) NOV). clear - IJ JL I1; lia. }
    repeat x64_step.
    all: pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
    + match goal with BC: (i =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into I0 end.
      split. right. exists L. split. exact NL. split. exact ZL. split. exact L1. right. left.
        exists j. split. exact JL. split. exact TR. split. rewrite I0 in NS. exact NS.
        split. reflexivity. rewrite MEM. apply md_fu.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SL end.
      rewrite BI2 in SL by (clear - I0; lia).
      exists L, j, (i - 1), (i - 1). split. dn.
      split. exact JL. split. exact TR. split. clear - I0 IJ; lia.
      split. replace (i - 1 + 1) with i by (clear - I0; lia). exact NS.
      split. apply N.le_refl. split. intros k K. exfalso. clear - K; lia.
      split. exact SL. clear - I0 IJ JL LB; mlia.
    + match goal with BC: (i =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into I0 end.
      match goal with BC: (_ =? 47) = false |- _ => apply N.eqb_neq in BC; rename BC into SL end.
      rewrite BI2 in SL by (clear - I0; lia).
      exists L, j, (i - 1). split. dn.
      split. exact JL. split. exact TR. split. clear - IJ; lia.
      split. intros k K. destruct (N.eq_dec k (i - 1)) as [->|NE]. exact SL. apply NS. clear - K NE I0; lia.
      clear - I0 IJ JL LB; mlia.
  - destruct PRE as [L [j [i [h [[NL [ZL [L1 [NOV [MEM [RDI [RSP CS]]]]]]] [JL [TR [IJ [NS [HI [AS [SI RAX]]]]]]]]]]]].
    assert (LB: L < 2^64) by exact (nilfree_bound m p L NL ZL).
    assert (BI3: md s0 m p Ⓑ[p + h] = m Ⓑ[p ⊕ h]) by (apply (md_byte s0 m p L h NOV); clear - HI IJ JL; lia).
    repeat x64_step.
    all: rewrite ?BI3 in *.
    all: pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5).
    + match goal with BC: (h =? 0) = true |- _ => apply N.eqb_eq in BC; rename BC into H0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SH end.
      split. right. exists L. split. exact NL. split. exact ZL. split. exact L1. right. right. left.
        exists j, i. split. exact IJ. split. exact JL. split. exact TR. split. exact NS.
        split. intros k K. destruct (N.eq_dec k 0) as [->|NE]. rewrite H0 in SH. exact SH.
          apply AS. clear - K NE H0; lia.
        split. reflexivity. apply md_fu.
      conj_tac. apply N.mod_small, RB.
    + match goal with BC: (h =? 0) = false |- _ => apply N.eqb_neq in BC; rename BC into H0 end.
      match goal with BC: (_ =? 47) = true |- _ => apply N.eqb_eq in BC; rename BC into SH end.
      exists L, j, i, (h - 1). split. dn.
      split. exact JL. split. exact TR. split. exact IJ. split. exact NS. split. clear - HI; lia.
      split. replace (h - 1 + 1) with h by (clear - H0; lia).
        intros k K. destruct (N.eq_dec k h) as [->|NE]. exact SH. apply AS. clear - K NE; lia.
      split. exact SI. clear - H0 HI IJ JL LB; mlia.
    + match goal with BC: (_ =? 47) = false |- _ => apply N.eqb_neq in BC; rename BC into SH end.
      assert (HLT: h < i).
      { destruct (N.eq_dec h i) as [E|E]. rewrite E in SH. exfalso. exact (SH SI). clear - HI E; lia. }
      split. right. exists L. split. exact NL. split. exact ZL. split. exact L1. right. right. right.
        exists j, i, h. split. exact HLT. split. exact IJ. split. exact JL. split. exact TR.
        split. exact NS. split. exact AS. split. exact SH. split. reflexivity.
        split. apply cut_byte.
        intros b BB1 BB2. rewrite cut_other by (exact BB1 || (clear - HLT IJ JL LB; lia)).
        apply md_frame, BB2.
      conj_tac. apply N.mod_small, RB.
Qed.
