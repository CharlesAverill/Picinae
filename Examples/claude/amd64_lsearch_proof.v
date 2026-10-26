(* lsearch -- linear search of an array, appending the key if absent

   SEMANTICS
   ---------
   lsearch(key, base, nmembp, size, compar) is lfind followed, when the key is
   absent, by memcpy(base + *nmembp * size, key, size) and ++*nmembp; it
   returns the found element or the newly appended one.  glibc inlines the
   lfind loop: it calls compar(key, &base[i]) through a function pointer
   (CALL R14) and memcpy through the PLT (CALL 0x128620).  Both callees are
   modeled as in amd64_lfind_proof.v and amd64_memccpy_proof.v: arbitrary
   code cp outside lsearch, constrained only by lsearch_cmp_contract and
   lsearch_memcpy_contract, which perform_call applies at the call sites.

   glibc tests "lfind returned NULL", so a match at an element whose address
   is 0 would be treated as absent.  The precondition NZ (no element of the
   array is at address 0) excludes that.

   SPECIFICATION (man 3 lsearch, Linux man-pages 5.10, Ubuntu 22.04)
   -----------------------------------------------------------------

     void *lsearch(const void *key, void *base, size_t *nmemb,
                   size_t size, int(*compar)(const void *, const void *));

     lfind() and lsearch() perform a linear search for key in the array base
     which has *nmemb elements of size bytes each.  The comparison function
     referenced by compar is expected to have two arguments which point to
     the key object and to an array member, in that order, and which returns
     zero if the key object matches the array member, and nonzero otherwise.

     lsearch() is similar to lfind(), but if the key is not found it is
     added to the end of the array; *nmemb is incremented.

     lsearch() returns a pointer to a matching member of the array, or to
     the newly added member if no match is found.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol lsearch at 0x120c80 (Ghidra address 0x220c80, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see lsearch_amd64.v (global addresses).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = key, RSI = base, RDX = nmembp, RCX = size, R8 = compar = C,
            RSP = sp; N = m Ⓠ[nmembp]; elt i = base ⊕ i * size.
            lsearch's frame is the 80 bytes below sp (fr sp = sp ⊖ 80).
   Preconditions: N < 2^64 - 1; *nmembp lies outside the frame; no element
            is at address 0; the key bytes and the new slot elt N lie outside
            the frame; *nmembp does not overlap the new slot; the callees
            meet their contracts.
   Output:  RSP = sp; RBX, RBP, R12-R15 have their entry values; and either
              RAX = elt i for the FIRST i < N with cmp key (elt i) = 0, and
              memory outside the frame is unchanged; or
              cmp key (elt i) <> 0 for all i < N, RAX = elt N, the size bytes
              at elt N are the key's bytes, *nmembp = N + 1, and memory
              outside the frame, the new slot and *nmembp is unchanged.
            (Partial correctness.)
 *)

Require Import Picinae_amd64.
Require Import lsearch_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_cstring amd64_memcpy_sets.
Import ListNotations.
Open Scope N.

Theorem lsearch_welltyped: welltyped_prog x64typctx lsearch_amd64.
Proof. Picinae_typecheck. Qed.

Definition C := 0x10000000.          (* the comparator's fixed entry address *)
Definition RET_CMP := 2231505.       (* 0x220cd1, after CALL R14 *)
Definition P_MEMCPY := 0x128620.     (* memcpy's PLT entry *)
Definition RET_MEMCPY := 2231551.    (* 0x220cff, after CALL memcpy *)

Definition lsearch_with (cp: store -> addr -> N * stmt) : program := fun s a =>
  match lsearch_amd64 s a with Some x => Some x | None => Some (cp s a) end.

Definition welltyped_code (cp: store -> addr -> N * stmt) :=
  forall s a, exists c', hastyp_stmt x64typctx x64typctx (snd (cp s a)) c'.

Lemma lsearch_with_welltyped:
  forall cp, welltyped_code cp -> welltyped_prog x64typctx (lsearch_with cp).
Proof.
  intros cp WT s a. unfold lsearch_with.
  pose proof (lsearch_welltyped s a) as H.
  destruct (lsearch_amd64 s a). exact H. destruct (cp s a) eqn:E. specialize (WT s a). rewrite E in WT. exact WT.
Qed.

Definition fr (sp:N) := sp ⊖ 80.

Section Invariants.
  Variable cmp : N -> N -> Z.
  Variable sp : N.
  Variable mem : memory.
  (* lsearch's arguments, or a callee's *)
  Variables key base nmembp size : N.
  Variables rbx rbp r12 r13 r14 r15 : N.

  Definition nmemb := mem Ⓠ[nmembp].
  Definition elt (i:N) := base ⊕ i * size.

  Definition saved (s:store) :=
    s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\
    s R_R13 = r13 /\ s R_R14 = r14 /\ s R_R15 = r15.

  (* the saved registers and base in the frame; nothing outside it changed *)
  Definition slots (M:memory) :=
    M Ⓠ[sp ⊖ 8] = r15 /\ M Ⓠ[sp ⊖ 16] = r14 /\ M Ⓠ[sp ⊖ 24] = r13 /\
    M Ⓠ[sp ⊖ 32] = r12 /\ M Ⓠ[sp ⊖ 40] = rbp /\ M Ⓠ[sp ⊖ 48] = rbx /\
    M Ⓠ[sp ⊖ 64] = base /\ agree (fr sp) 80 M mem.

  Definition result_ok (s:store) :=
    (exists i, i < nmemb /\ s R_RAX = elt i /\ cmp key (elt i) = 0%Z /\
               (forall j, j < i -> cmp key (elt j) <> 0%Z) /\
               agree (fr sp) 80 (s V_MEM64) mem) \/
    ((forall i, i < nmemb -> cmp key (elt i) <> 0%Z) /\ s R_RAX = elt nmemb /\
     (forall j, j < size -> s V_MEM64 Ⓑ[elt nmemb ⊕ j] = mem Ⓑ[key ⊕ j]) /\
     s V_MEM64 Ⓠ[nmembp] = nmemb + 1 /\
     (forall b, ~ inwin (fr sp) 80 b -> ~ msub 64 b (elt nmemb) < size -> ~ msub 64 b nmembp < 8 ->
                s V_MEM64 Ⓑ[b] = mem Ⓑ[b])).

  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    (* the comparator (subroutine 0): compar(key, base) *)
    | 268435456 => Inv 0 (s R_RDI = key /\ s R_RSI = base /\ s R_RSP = sp /\
                          s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_CMP /\ saved s)
    | 2231505 => Post 0 (toZ 32 (s R_RAX mod 2^32) = cmp key base /\ s R_RSP = sp ⊕ 8 /\
                         s V_MEM64 = mem /\ saved s)
    (* memcpy (subroutine 1): memcpy(key, base, size) *)
    | 1213984 => Inv 1 (s R_RDI = key /\ s R_RSI = base /\ s R_RDX = size /\ s R_RSP = sp /\
                        s V_MEM64 = mem /\ mem Ⓠ[sp] = RET_MEMCPY /\ saved s)
    | 2231551 => Post 1 (copied mem (s V_MEM64) key base size /\ s R_RAX = key /\
                         s R_RSP = sp ⊕ 8 /\ saved s)
    (* lsearch (subroutine 2) *)
    | 2231424 => Inv 2 (s R_RDI = key /\ s R_RSI = base /\ s R_RDX = nmembp /\ s R_RCX = size /\
                        s R_R8 = C /\ s R_RSP = sp /\ s V_MEM64 = mem /\ saved s)
    | 2231496 => Inv 2 (exists i,
                   s R_RSP = sp ⊖ 72 /\ s R_R15 = key /\ s R_R14 = C /\ s R_R13 = size /\
                   s R_RBP = nmembp /\ s R_RBX = i /\ s R_R12 = elt i /\ i < nmemb /\
                   (forall j, j < i -> cmp key (elt j) <> 0%Z) /\ slots (s V_MEM64))
    | 2231543 => Inv 2 (s R_RSP = sp ⊖ 72 /\ s R_RAX = nmemb ⊗ size /\
                   s R_RDI = base /\ s R_RDX = size /\ s R_RSI = key /\ s R_RBP = nmembp /\
                   (forall i, i < nmemb -> cmp key (elt i) <> 0%Z) /\ slots (s V_MEM64))
    | 2231576 => Post 2 (s R_RSP = sp /\ saved s /\ result_ok s)
    | _ => NoInv
    end.

  Definition exits0 cp := make_exits 0 (lsearch_with cp) invs.
  Definition invs0 cp := make_invs 0 (lsearch_with cp) invs.
  Definition exits1 cp := make_exits 1 (lsearch_with cp) invs.
  Definition invs1 cp := make_invs 1 (lsearch_with cp) invs.
  Definition exits2 cp := make_exits 2 (lsearch_with cp) invs.
  Definition invs2 cp := make_invs 2 (lsearch_with cp) invs.
End Invariants.

Definition lsearch_cmp_contract (cp: store -> addr -> N * stmt) (cmp:N -> N -> Z) :=
  forall s t xs' sp mem key elt rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr C, s) -> models x64typctx s ->
  s R_RDI = key -> s R_RSI = elt -> s R_RSP = sp -> s V_MEM64 = mem ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_CMP ->
  satisfies_all (lsearch_with cp)
    (invs0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp)
    (exits0 cmp sp mem key elt 0 0 rbx rbp r12 r13 r14 r15 cp) (xs'::t).

Definition lsearch_memcpy_contract (cp: store -> addr -> N * stmt) (cmp:N -> N -> Z) :=
  forall s t xs' sp mem d p n rbx rbp r12 r13 r14 r15,
  startof t xs' = (Addr P_MEMCPY, s) -> models x64typctx s ->
  s R_RDI = d -> s R_RSI = p -> s R_RDX = n -> s R_RSP = sp -> s V_MEM64 = mem ->
  saved rbx rbp r12 r13 r14 r15 s -> mem Ⓠ[sp] = RET_MEMCPY ->
  satisfies_all (lsearch_with cp)
    (invs1 cmp sp mem d p 0 n rbx rbp r12 r13 r14 r15 cp)
    (exits1 cmp sp mem d p 0 n rbx rbp r12 r13 r14 r15 cp) (xs'::t).

(* Frame bookkeeping *)
Lemma nov_byte: forall a l1 b l2 x, ~ overlap 64 a l1 b l2 -> msub 64 x a < l1 -> ~ msub 64 x b < l2.
Proof.
  intros a l1 b l2 x NO XA XB. apply NO. exists (msub 64 x a), (msub 64 x b).
  split. exact XA. split. exact XB.
  rewrite !add_msub_assoc, !(N.add_comm _ x), !add_msub_r. reflexivity.
Qed.

Lemma getmem8_agree:
  forall (M1 M2:memory) a, (forall a', msub 64 a' a < 8 -> M1 Ⓑ[a'] = M2 Ⓑ[a']) -> M1 Ⓠ[a] = M2 Ⓠ[a].
Proof.
  intros M1 M2 a H. apply getmem_frame_mem. intros a' A. rewrite <- !(getmem_1 64 LittleE). apply H, A.
Qed.

Lemma agree_slot:
  forall sp x (M m:memory) v, 8 <= x <= 80 -> agree (fr sp) 80 M m -> agree (fr sp) 80 (M [Ⓠ sp ⊖ x := v]) m.
Proof.
  intros. apply agree_setwin; try assumption; try (change (2^64) with 18446744073709551616; lia).
  clear - H. unfold fr, msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* *nmembp lies outside the frame, so it reads the same as in the entry memory. *)
Lemma nm_agree:
  forall sp (M m:memory) p, agree (fr sp) 80 M m -> ~ overlap 64 p 8 (fr sp) 80 -> M Ⓠ[p] = m Ⓠ[p].
Proof.
  intros sp M m p AG NO. apply getmem8_agree. intros a' A. apply AG. exact (nov_byte _ _ _ _ _ NO A).
Qed.

Lemma toZ32_zero: forall y, y < 2^32 -> (toZ 32 y = 0%Z <-> y = 0).
Proof.
  intros y Y. split; intro H.
  - destruct (N.lt_ge_cases y (2^31)) as [L|L].
      rewrite (proj1 (toZ_nonneg 32 y)) in H by (rewrite N.mod_small; assumption).
      rewrite N.mod_small in H by assumption. lia.
      assert (NEG: Z.lt (toZ 32 y) 0).
        apply Z.nle_gt. intro H1. apply toZ_sign in H1. rewrite N.mod_small in H1 by assumption. simpl in H1. lia.
      lia.
  - subst. reflexivity.
Qed.

(* Two 8-byte frame slots at different offsets below sp don't overlap. *)
Lemma slot_disj: forall sp x y, x <= 80 -> y <= 80 -> (x + 8 <= y \/ y + 8 <= x) ->
  ~ overlap 64 (sp ⊖ x) 8 (sp ⊖ y) 8.
Proof.
  intros sp x y X Y D [i [j [I [J E]]]]. unfold msub in E.
  change (2^64) with 18446744073709551616 in *.
  rewrite (N.mod_small x), (N.mod_small y) in E by lia. lia.
Qed.

Ltac slot_nov := apply slot_disj; lia.

(* A byte or slot that msub puts outside a range doesn't overlap it. *)
Lemma add_msub_mod: forall a b, (a + msub 64 b a) mod 2^64 = b mod 2^64.
Proof. intros. rewrite add_msub_assoc, N.add_comm, add_msub_r. reflexivity. Qed.

Lemma byte_nov: forall b a, ~ msub 64 b a < 8 -> ~ overlap 64 b 1 a 8.
Proof.
  intros b a H [i [j [I [J E]]]]. apply H. replace i with 0 in E by lia. rewrite N.add_0_r in E.
  rewrite <- (msub_mod_l 64 64 b) by reflexivity. rewrite E, msub_mod_l, N.add_comm, add_msub_r by reflexivity.
  rewrite N.mod_small; [exact J | change (2^64) with 18446744073709551616; lia].
Qed.

Lemma copied_out8:
  forall M1 M2 d p n a, copied M1 M2 d p n -> (forall a', msub 64 a' a < 8 -> ~ msub 64 a' d < n) ->
  M2 Ⓠ[a] = M1 Ⓠ[a].
Proof. intros M1 M2 d p n a [_ OUT] H. apply getmem8_agree. intros a' A. apply OUT, H, A. Qed.

(* A frame slot is not in the new element (DSTF). *)
Lemma slot_not_dst:
  forall sp d n x a', (forall j, j < n -> ~ inwin (fr sp) 80 (d ⊕ j)) -> 8 <= x <= 80 ->
  msub 64 a' (sp ⊖ x) < 8 -> ~ msub 64 a' d < n.
Proof.
  intros sp d n x a' DF X A I. apply (DF _ I). unfold inwin.
  rewrite add_msub_mod, msub_mod_l by reflexivity.
  clear - X A. unfold fr, msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* A frame slot doesn't overlap *nmembp (NOV). *)
Lemma slot_nm: forall sp p x, 8 <= x <= 80 -> ~ overlap 64 p 8 (fr sp) 80 -> ~ overlap 64 (sp ⊖ x) 8 p 8.
Proof.
  intros sp p x X NO [i [j [I [J E]]]]. apply NO. exists j, (80 - x + i).
  split. exact J. split. lia. rewrite <- E. clear - X. unfold fr, msub.
  rewrite !N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small x), (N.mod_small 80) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Lemma rsp80: forall sp, sp ⊖ 80 ⊕ 8 = sp ⊖ 72.
Proof.
  intro sp. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small 80), (N.mod_small 72) by (change (2^64) with 18446744073709551616; lia).
  f_equal. change (2^64) with 18446744073709551616. lia.
Qed.

Ltac frame_read :=
  repeat match goal with
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a ?v) ?a] =>
      rewrite (getmem_setmem 64 LittleE 8 m a v) by discriminate
  | |- context [getmem 64 LittleE 8 (setmem 64 LittleE 8 ?m ?a2 ?v) ?a1] =>
      rewrite (getmem_noverlap 64 LittleE LittleE 8 8 m a1 a2 v) by slot_nov
  end.

Theorem lsearch_correct:
  forall cp cmp s t xs' sp mem key base nmembp size
         (WT: welltyped_code cp) (CMP: lsearch_cmp_contract cp cmp)
         (MEMCPY: lsearch_memcpy_contract cp cmp)
         (ENTRY: startof t xs' = (Addr 2231424, s))
         (MDL: models x64typctx s)
         (RDI: s R_RDI = key) (RSI: s R_RSI = base) (RDX: s R_RDX = nmembp) (RCX: s R_RCX = size)
         (R8: s R_R8 = C) (SP: s R_RSP = sp) (MEM: s V_MEM64 = mem)
         (SPB: sp < 2^64) (NNB: mem Ⓠ[nmembp] < 2^64 - 1)
         (NOV: ~ overlap 64 nmembp 8 (fr sp) 80)
         (NZ: forall i, i < nmemb mem nmembp -> elt base size i <> 0)
         (KEYF: forall j, j < size -> ~ inwin (fr sp) 80 (key ⊕ j))
         (DSTF: forall j, j < size -> ~ inwin (fr sp) 80 (elt base size (nmemb mem nmembp) ⊕ j))
         (DNM: ~ overlap 64 nmembp 8 (elt base size (nmemb mem nmembp)) size),
  satisfies_all (lsearch_with cp)
    (invs2 cmp sp mem key base nmembp size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (exits2 cmp sp mem key base nmembp size (s R_RBX) (s R_RBP) (s R_R12) (s R_R13) (s R_R14) (s R_R15) cp)
    (xs'::t).
Proof.
  intros.
  assert (SZB: size < 2^64) by (rewrite <- RCX; apply (MDL R_RCX 64), eq_refl).
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply lsearch_with_welltyped, WT. intro MDL1.
  set (rbx0 := s R_RBX) in *. set (rbp0 := s R_RBP) in *. set (r120 := s R_R12) in *.
  set (r130 := s R_R13) in *. set (r140 := s R_R14) in *. set (r150 := s R_R15) in *.
  clearbody rbx0 rbp0 r120 r130 r140 r150.
  clear - PRE MDL1 WT CMP MEMCPY SPB NNB NOV NZ KEYF DSTF DNM SZB. rename t1 into t. rename s1 into s. rename MDL1 into MDL.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as (KEY & BASE & NM & SZ & R8 & SP & MEM & RBX & RBP & R12 & R13 & R14 & R15).
    assert (BB: base < 2^64) by (rewrite <- BASE; apply (MDL R_RSI 64), eq_refl).
    assert (Bs := conj (MDL R_RBX 64 eq_refl) (conj (MDL R_RBP 64 eq_refl) (conj (MDL R_R12 64 eq_refl)
                  (conj (MDL R_R13 64 eq_refl) (conj (MDL R_R14 64 eq_refl) (MDL R_R15 64 eq_refl)))))).
    rewrite RBX, RBP, R12, R13, R14, R15 in Bs. destruct Bs as (B1 & B2 & B3 & B4 & B5 & B6).
    repeat x64_step.
    all: assert (A0: agree (fr sp) 80 (mem [Ⓠ sp ⊖ 8 := r150] [Ⓠ sp ⊖ 16 := r140] [Ⓠ sp ⊖ 24 := r130]
                     [Ⓠ sp ⊖ 32 := r120] [Ⓠ sp ⊖ 40 := rbp0] [Ⓠ sp ⊖ 48 := rbx0]) mem)
           by (repeat apply agree_slot; try lia; apply agree_refl).
    all: rewrite (nm_agree _ _ _ _ A0 NOV) in *.
    all: assert (SL: slots sp mem base rbx0 rbp0 r120 r130 r140 r150
                   (mem [Ⓠ sp ⊖ 8 := r150] [Ⓠ sp ⊖ 16 := r140] [Ⓠ sp ⊖ 24 := r130]
                     [Ⓠ sp ⊖ 32 := r120] [Ⓠ sp ⊖ 40 := rbp0] [Ⓠ sp ⊖ 48 := rbx0] [Ⓠ sp ⊖ 64 := base]))
           by (unfold slots; frame_read;
               rewrite !(N.mod_small _ (2^(8*8))) by (change (2^(8*8)) with (2^64); assumption);
               repeat split; try reflexivity; apply agree_slot; [lia | exact A0]).
    + (* *nmembp = 0: straight to the append *)
      apply N.eqb_eq in BC.
      do 6 (split; [reflexivity|]). split. intros i I. unfold nmemb in I. lia. exact SL.
    + apply N.eqb_neq in BC. exists 0.
      do 6 (split; [reflexivity|]).
      split. unfold elt. rewrite N.mul_0_l, N.add_0_r, N.mod_small by exact BB. reflexivity.
      split. unfold nmemb. lia.
      split. intros j J. lia. exact SL.
  - (* loop head: call the comparator *)
    destruct PRE as (i & RSP & R15 & R14 & R13 & RBP & RBX & R12 & IN & PREV & SL).
    destruct SL as (F1 & F2 & F3 & F4 & F5 & F6 & FB & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lsearch_with_welltyped, WT. intro MDL1.
    eapply (perform_call 0). reflexivity.
    intros. eapply CMP; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (RAXc & RSPc & MEMc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lsearch_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    assert (AG': agree (fr sp) 80 (s' V_MEM64) mem) by (rewrite MEMc; apply agree_slot; [lia | exact AG]).
    assert (FN: s' V_MEM64 Ⓠ[nmembp] = nmemb mem nmembp) by (apply (nm_agree _ _ _ _ AG' NOV)).
    assert (SL': slots sp mem base rbx0 rbp0 r120 r130 r140 r150 (s' V_MEM64)).
    { unfold slots. rewrite MEMc. frame_read. repeat split; try assumption. rewrite <- MEMc. exact AG'. }
    rewrite RBX in RBXc. rewrite RBP in RBPc. rewrite R13 in R13c.
    clear - RAXc RSPc RBXc RBPc R12c R13c R14c R15c MDL' FN SL' IN PREV SPB NNB NOV NZ t'.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    destruct SL' as (F1 & F2 & F3 & F4 & F5 & F6 & FB & AG).
    repeat x64_step.
    all: rewrite ?FN in *.
    all: assert (I1: 1 ⊕ i = i + 1) by
           (rewrite N.mod_small; [lia | unfold nmemb in IN; change (2^64) with 18446744073709551616 in *; lia]).
    + (* found, but at address 0: excluded by NZ *)
      exfalso. apply N.eqb_eq in BC1. exact (NZ i IN BC1).
    + (* found: return elt i *)
      apply N.eqb_eq in BC.
      assert (CZ: cmp key (elt base size i) = 0%Z) by (rewrite <- RAXc, BC; reflexivity).
      split. reflexivity.
      split. unfold saved. cbn [update iseq vareq]. rewrite F1, F2, F3, F4, F5, F6. repeat split; reflexivity.
      left. exists i. cbn [update iseq vareq].
      split. exact IN. split. reflexivity. split. exact CZ. split. exact PREV. exact AG.
    + (* *nmembp <= i after a match: impossible, *nmembp is unchanged *)
      exfalso. unfold nmemb in IN, BC0.
      destruct (N.ltb_spec (mem Ⓠ[nmembp]) i), (N.eqb_spec (mem Ⓠ[nmembp]) i); cbn in BC0; try discriminate; lia.
    + (* no match, more elements: next iteration *)
      apply N.eqb_neq in BC.
      assert (CNZ: cmp key (elt base size i) <> 0%Z)
        by (rewrite <- RAXc; intro Z0; apply BC; apply toZ32_zero; [apply mp2_mod_lt|exact Z0]).
      apply N.ltb_lt in BC0. rewrite I1 in BC0.
      exists (i + 1).
      split. rewrite RSPc. apply rsp80.
      do 4 (split; [assumption || reflexivity|]).
      split. exact I1.
      split. unfold elt. rewrite mp2_add_l, N.mul_add_distr_r, N.mul_1_l, N.add_assoc. reflexivity.
      split. exact BC0.
      split. intros q Q. destruct (N.lt_ge_cases q i) as [Qi|Qi]; [apply PREV, Qi|].
        assert (q = i) by lia. subst q. exact CNZ.
      exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj FB AG))))))).
    + (* no match, array exhausted: append *)
      apply N.eqb_neq in BC.
      assert (CNZ: cmp key (elt base size i) <> 0%Z)
        by (rewrite <- RAXc; intro Z0; apply BC; apply toZ32_zero; [apply mp2_mod_lt|exact Z0]).
      apply N.ltb_ge in BC0. rewrite I1 in BC0.
      split. reflexivity.
      split. reflexivity. split. exact FB.
      do 3 (split; [reflexivity|]).
      split. intros q Q. destruct (N.lt_ge_cases q i) as [Qi|Qi]; [apply PREV, Qi|].
        assert (q = i) by lia. subst q. exact CNZ.
      exact (conj F1 (conj F2 (conj F3 (conj F4 (conj F5 (conj F6 (conj FB AG))))))).
  - (* not found: call memcpy, then ++*nmembp *)
    destruct PRE as (RSP & RAX & RDI & RDX & RSI & RBP & NOF & SL).
    destruct SL as (F1 & F2 & F3 & F4 & F5 & F6 & FB & AG).
    repeat x64_step.
    set (s1 := update _ _ _).
    eapply models_after_steps. eassumption. apply lsearch_with_welltyped, WT. intro MDL1.
    eapply (perform_call 1). reflexivity.
    intros. eapply MEMCPY; try (eassumption || reflexivity).
      unfold saved. repeat split; reflexivity.
      unfold s1. cbn [update iseq vareq]. psimpl. reflexivity.
    reflexivity.
    intros. unfold s1 in PRE. psimpl in PRE.
    destruct_inv 64 PRE.
    destruct PRE as (CP & RAXc & RSPc & RBXc & RBPc & R12c & R13c & R14c & R15c).
    assert (MDL': models x64typctx s').
      eapply preservation_exec_prog; try eassumption. apply lsearch_with_welltyped, WT.
    set (t' := t2++t0++_::t) in *. clearbody s1 t'.
    set (M1 := s V_MEM64 [Ⓠ sp ⊖ 80 := 2231551]) in *.
    assert (AG1: agree (fr sp) 80 M1 mem) by (apply agree_slot; [lia | exact AG]).
    assert (GS: forall x, 8 <= x <= 80 -> s' V_MEM64 Ⓠ[sp ⊖ x] = M1 Ⓠ[sp ⊖ x]).
      intros x X. eapply copied_out8. exact CP. intros a' A. eapply slot_not_dst; eassumption.
    assert (FN': s' V_MEM64 Ⓠ[nmembp] = nmemb mem nmembp).
    { rewrite (copied_out8 _ _ _ _ _ _ CP). apply (nm_agree _ _ _ _ AG1 NOV).
      intros a' A. exact (nov_byte _ _ _ _ _ DNM A). }
    assert (G1: s' V_MEM64 Ⓠ[sp ⊖ 8] = r150) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F1).
    assert (G2: s' V_MEM64 Ⓠ[sp ⊖ 16] = r140) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F2).
    assert (G3: s' V_MEM64 Ⓠ[sp ⊖ 24] = r130) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F3).
    assert (G4: s' V_MEM64 Ⓠ[sp ⊖ 32] = r120) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F4).
    assert (G5: s' V_MEM64 Ⓠ[sp ⊖ 40] = rbp0) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F5).
    assert (G6: s' V_MEM64 Ⓠ[sp ⊖ 48] = rbx0) by (rewrite GS by lia; unfold M1; rewrite getmem_noverlap by slot_nov; exact F6).
    assert (KEYB: forall j, j < size -> s' V_MEM64 Ⓑ[elt base size (nmemb mem nmembp) ⊕ j] = mem Ⓑ[key ⊕ j]).
    { intros j J. destruct CP as [CPin _]. unfold elt. rewrite (CPin j J). apply AG1, KEYF, J. }
    assert (OUT: forall b, ~ inwin (fr sp) 80 b -> ~ msub 64 b (elt base size (nmemb mem nmembp)) < size ->
                 s' V_MEM64 Ⓑ[b] = mem Ⓑ[b]).
    { intros b W B. destruct CP as [_ CPout]. rewrite (CPout b B). apply AG1, W. }
    rewrite RBP in RBPc.
    clearbody M1.
    clear - RAXc RSPc RBPc MDL' FN' G1 G2 G3 G4 G5 G6 KEYB OUT NOF SPB NNB NOV DNM SZB t'.
    rename s' into s. rename MDL' into MDL. rename t' into t.
    repeat x64_step.
    rewrite FN' in *.
    assert (RD: forall x, 8 <= x <= 80 ->
                (s V_MEM64 [Ⓠ nmembp := 1 + nmemb mem nmembp]) Ⓠ[sp ⊖ x] = s V_MEM64 Ⓠ[sp ⊖ x])
      by (intros x X; apply getmem_noverlap, slot_nm; assumption).
    unfold saved, result_ok. psimpl.
    repeat (rewrite RD by lia). rewrite G1, G2, G3, G4, G5, G6.
    split. reflexivity.
    split. repeat split; reflexivity.
    right.
    split. exact NOF. split. reflexivity.
    split. intros j J. rewrite getmem_noverlap. apply KEYB, J.
      apply byte_nov. apply (nov_byte _ _ _ _ _ (noverlap_sym _ _ _ _ _ DNM)).
      unfold elt. rewrite msub_mod_l, N.add_comm, add_msub_r, N.mod_small by (reflexivity || lia). exact J.
    split. try rewrite getmem_setmem by discriminate. change (2^(8*8)) with (2^64).
      unfold nmemb in *. rewrite ?N.mod_small by lia. lia.
    intros b W B NM. rewrite getmem_noverlap by (apply byte_nov; exact NM). apply OUT; assumption.
Time Qed.

(* Non-vacuity of the callee contracts.  At C the witness is a comparator that
   returns 0 at once (cmp = fun _ _ => 0), as in amd64_lfind_proof.v.  At
   P_MEMCPY it jumps to itself forever: that shows the memcpy contract is not
   contradictory (no single-state trace refutes it), which is all a witness
   needs here, but it is weaker than exhibiting a terminating memcpy.  The
   real memcpy is verified separately (amd64_memcpy_proof.v and
   amd64_memcpy_loops_proof.v). *)
Definition ret0 : stmt :=
  Move R_RAX (Word 0 64) $;
  Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
  Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 8 64)) $;
  Jmp (Var R_RIP).
Definition cp0 (_:store) (a:addr) : N * stmt :=
  if a =? C then (1, ret0) else (1, Jmp (Word P_MEMCPY 64)).

Lemma cp0_welltyped: welltyped_code cp0.
Proof. intros s a. unfold cp0. destruct (a =? C); apply typchk_stmt_compute; vm_compute; exact I. Qed.

Theorem lsearch_contracts_satisfiable:
  exists cp cmp, welltyped_code cp /\ lsearch_cmp_contract cp cmp /\ lsearch_memcpy_contract cp cmp.
Proof.
  exists cp0, (fun _ _ => 0%Z). split. exact cp0_welltyped. split.
  - intros s t xs' sp mem key elt rbx rbp r12 r13 r14 r15
      ENTRY MDL RDI RSI RSP MEM [RBX [RBP [R12 [R13 [R14 R15]]]]] RET. apply prove_invs.
    simpl. rewrite ENTRY. x64_step. repeat split; assumption.
    intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply lsearch_with_welltyped, cp0_welltyped.
    intro MDL1. clear - PRE MDL1. rename t1 into t.
    destruct_inv 64 PRE.
    destruct PRE as (RDI & RSI & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
    x64_step. rewrite RET. unfold RET_CMP. x64_step.
    split. reflexivity. split. reflexivity. split. reflexivity.
    repeat split; assumption.
  - intros s t xs' sp mem d p n rbx rbp r12 r13 r14 r15
      ENTRY MDL RDI RSI RDX RSP MEM [RBX [RBP [R12 [R13 [R14 R15]]]]] RET. apply prove_invs.
    simpl. rewrite ENTRY. x64_step. repeat split; assumption.
    intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply lsearch_with_welltyped, cp0_welltyped.
    intro MDL1. clear - PRE MDL1. rename t1 into t.
    destruct_inv 64 PRE.
    destruct PRE as (RDI & RSI & RDX & RSP & MEM & RET & RBX & RBP & R12 & R13 & R14 & R15).
    x64_step. repeat split; assumption.
Qed.
