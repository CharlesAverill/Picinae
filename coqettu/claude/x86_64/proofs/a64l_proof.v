(* a64l -- convert a radix-64 ASCII string to a long (musl x86_64, C),
   composed with strchr (-> strchrnul -> strlen)

   SEMANTICS
   ---------
   musl's a64l (src/misc/a64l.c) is

       static const char digits[] =
           "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
       long a64l(const char *s)
       {
           int e;
           uint32_t x = 0;
           for (e=0; e<36 && *s; e+=6, s++) {
               const char *d = strchr(digits, *s);
               if (!d) break;
               x |= (uint32_t)(d-digits)<<e;
           }
           return (int32_t)x;
       }

   The binary keeps s in R12, e in EBP, x in R13D and digits (0x19d720) in
   RBX, and CALLs strchr (0x1659b5) once per character.  strchr's contract
   (strchr_proof.v, itself a three-level composition) is used through
   call_leaf_ni; its memory frame (stack_frame, 48 bytes below its RSP) lets
   a64l re-read its saved registers and the string afterwards.

   SPECIFICATION (man 3 a64l, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     long a64l(const char *str64);
     a64l converts a string of at most six radix-64 digits ('.' = 0,
     '/' = 1, '0'-'9' = 2-11, 'A'-'Z' = 12-37, 'a'-'z' = 38-63), least
     significant digit first, to a long; it stops at a NUL or at a character
     that is not a digit.  musl returns the 32-bit value sign-extended
     ((int32_t)x).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            a64l at 0x55c28, strchr at 0x659b5, digits at 0x9d720 (Ghidra
            image base 0x100000: 0x155c28, 0x1659b5, 0x19d720)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/a64l_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s; RSP = rsp; m = memory.  Precondition (a64l_ok): the
            table at 0x19d720 is a NUL-terminated string of length L < 2^63
            and its L+1 bytes, and the 6 bytes at s, do not overlap the 96
            bytes below rsp (a64l's frame and strchr's).
   Output:  At the RET (0x155c7b): there are j <= 6 and digit indices kf i
            such that for i < j, s[i] is nonzero and kf i is the first index
            of s[i] in the table (dig); and j = 6, or s[j] = 0, or s[j] does
            not occur in the table (nodig); RAX is the sign extension of the
            32-bit value acc kf j = OR_{i<j} ((kf i << 6i) mod 2^32).
            Nothing outside the 96 bytes below rsp changes; RSP = rsp; RBX,
            RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.a64l_amd64 CoqEtTu.programs.strchr_amd64
               CoqEtTu.programs.strchrnul_amd64 CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose.
Require Import CoqEtTu.proofs.strlen_proof CoqEtTu.proofs.strchrnul_proof CoqEtTu.proofs.strchr_proof
               CoqEtTu.proofs.index_proof.
Open Scope N.

Definition a64l_program : program := updateall2 a64l_amd64 strchr_program.

Theorem a64l_welltyped: welltyped_prog x64typctx a64l_amd64.
Proof. exact a64l_amd64.welltyped. Qed.

Lemma a64l_program_welltyped: welltyped_prog x64typctx a64l_program.
Proof.
  intros s a. unfold a64l_program, updateall2 at 1, updateall.
  destruct (strchr_program s a) as [[sz q]|] eqn:SL.
    pose proof (strchr_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply a64l_welltyped.
Qed.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

Definition tab := 0x19d720.

(* k is the first index of byte c in the table *)
Definition dig (m:memory) (c k:N) := cfree m tab c k /\ m Ⓑ[tab ⊕ k] = c.
(* c does not occur in the table *)
Definition nodig (m:memory) (c:N) := exists k, cfree m tab c k /\ m Ⓑ[tab ⊕ k] = 0.

Definition acc (kf:N -> N) (j:N) : N :=
  N.recursion 0 (fun i x => x .| ((kf i << (6*i)) mod 2^32)) j.

Lemma acc_0: forall kf, acc kf 0 = 0.
Proof. reflexivity. Qed.

Lemma acc_succ: forall kf j, acc kf (j + 1) = acc kf j .| ((kf j << (6*j)) mod 2^32).
Proof.
  intros. unfold acc. rewrite N.add_1_r, N.recursion_succ. reflexivity.
  reflexivity. intros x y E f g H. subst. reflexivity.
Qed.

Definition a64l_ok (m s rsp:N) :=
  (exists L, nilfree m tab L /\ m Ⓑ[tab ⊕ L] = 0 /\ L < 2^63 /\ ~ overlap 64 tab (L + 1) (rsp ⊖ 96) 96) /\
  ~ overlap 64 s 6 (rsp ⊖ 96) 96.

(* the loop memory: unchanged outside the 96 bytes below rsp, saved
   registers in their slots *)
Definition frm96 (s0:store) (m M:memory) :=
  (forall b, 96 <= msub 64 b (s0 R_RSP ⊖ 96) -> M Ⓑ[b] = m Ⓑ[b]) /\
  M Ⓠ[s0 R_RSP ⊖ 8] = s0 R_R13 /\ M Ⓠ[s0 R_RSP ⊖ 16] = s0 R_R12 /\
  M Ⓠ[s0 R_RSP ⊖ 24] = s0 R_RBP /\ M Ⓠ[s0 R_RSP ⊖ 32] = s0 R_RBX.

Definition cs2 (s0 s:store) := s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Definition a64l_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x155c7b => true
  | _ => false end | _ => false end.

Definition a64l_post (s0:store) (m p:N) (s:store) :=
  (exists j kf, j <= 6 /\
     (forall i, i < j -> m Ⓑ[p ⊕ i] <> 0 /\ dig m (m Ⓑ[p ⊕ i]) (kf i)) /\
     (j = 6 \/ m Ⓑ[p ⊕ j] = 0 \/ nodig m (m Ⓑ[p ⊕ j])) /\
     s R_RAX = scast 32 64 (acc kf j)) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 96 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition a64l_invs (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x155c28 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x155c41 => Some (exists j kf, j < 6 /\
                      (forall i, i < j -> m Ⓑ[p ⊕ i] <> 0 /\ dig m (m Ⓑ[p ⊕ i]) (kf i)) /\
                      frm96 s0 m (s V_MEM64) /\ s R_R12 = p ⊕ j /\ s R_RBP = 6*j /\
                      s R_R13 = acc kf j /\ s R_RBX = tab /\ s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x155c4e => Some (exists j kf, j < 6 /\
                      (forall i, i < j -> m Ⓑ[p ⊕ i] <> 0 /\ dig m (m Ⓑ[p ⊕ i]) (kf i)) /\
                      m Ⓑ[p ⊕ j] <> 0 /\ s R_RSI mod 2^8 = m Ⓑ[p ⊕ j] /\ s R_RDI = tab /\
                      frm96 s0 m (s V_MEM64) /\ s R_R12 = p ⊕ j /\ s R_RBP = 6*j /\
                      s R_R13 = acc kf j /\ s R_RBX = tab /\ s R_RSP = s0 R_RSP ⊖ 40 /\ cs2 s0 s)
  | 0x155c7b => Some (a64l_post s0 m p s)
  | _ => None
  end | _ => None end.

Lemma qslot96:
  forall rsp a b, ((a + 8 <=? b) && (b <=? 96) && (8 <=? a))%bool = true ->
  ~ overlap 64 (rsp ⊖ a) 8 (rsp ⊖ b) 8.
Proof.
  intros rsp a b H. apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H.
  destruct H as [H1 H2]. apply N.leb_le in H1, H2, H3.
  intros [x [y [X [Y E]]]]. mlia.
Qed.

Lemma frm96_init:
  forall s0 m, s0 R_R13 < 2^64 -> s0 R_R12 < 2^64 -> s0 R_RBP < 2^64 -> s0 R_RBX < 2^64 ->
  frm96 s0 m (m [Ⓠs0 R_RSP ⊖ 8 := s0 R_R13] [Ⓠs0 R_RSP ⊖ 16 := s0 R_R12]
                [Ⓠs0 R_RSP ⊖ 24 := s0 R_RBP] [Ⓠs0 R_RSP ⊖ 32 := s0 R_RBX]).
Proof.
  intros s0 m B1 B2 B3 B4. split; [|split; [|split; [|split]]].
  - intros b B.
    rewrite (stack_store_frame _ (s0 R_RSP) 32 _ b 96) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 24 _ b 96) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 16 _ b 96) by (assumption || lia).
    rewrite (stack_store_frame _ (s0 R_RSP) 8 _ b 96) by (assumption || lia).
    reflexivity.
  - rewrite getmem_noverlap by exact (qslot96 _ 8 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot96 _ 8 24 eq_refl).
    rewrite getmem_noverlap by exact (qslot96 _ 8 16 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot96 _ 16 32 eq_refl).
    rewrite getmem_noverlap by exact (qslot96 _ 16 24 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_noverlap by exact (qslot96 _ 24 32 eq_refl).
    rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
  - rewrite getmem_setmem by discriminate. apply N.mod_small. assumption.
Qed.

Lemma frm96_ra: forall s0 m M v, frm96 s0 m M -> frm96 s0 m (M [Ⓠs0 R_RSP ⊖ 48 := v]).
Proof.
  intros s0 m M v [F [S8 [S16 [S24 S32]]]]. split; [|split; [|split; [|split]]].
  - intros b B. rewrite (stack_store_frame _ (s0 R_RSP) 48 _ b 96) by (assumption || lia). apply F, B.
  - rewrite getmem_noverlap by exact (qslot96 _ 8 48 eq_refl). exact S8.
  - rewrite getmem_noverlap by exact (qslot96 _ 16 48 eq_refl). exact S16.
  - rewrite getmem_noverlap by exact (qslot96 _ 24 48 eq_refl). exact S24.
  - rewrite getmem_noverlap by exact (qslot96 _ 32 48 eq_refl). exact S32.
Qed.

Lemma outside96:
  forall x n rsp i, ~ overlap 64 x n (rsp ⊖ 96) 96 -> i < n -> 96 <= msub 64 (x ⊕ i) (rsp ⊖ 96).
Proof.
  intros x n rsp i NOV I. assert (BB: rsp ⊖ 96 < 2^64) by apply (msub_lt 64).
  set (b := rsp ⊖ 96) in *. clearbody b.
  destruct (N.le_gt_cases 96 (msub 64 (x ⊕ i) b)) as [D|D]. exact D. exfalso.
  apply NOV. exists i, (msub 64 (x ⊕ i) b). split. exact I. split. exact D. mlia.
Qed.

Lemma frm96_byte:
  forall s0 m M x n i, frm96 s0 m M -> ~ overlap 64 x n (s0 R_RSP ⊖ 96) 96 -> i < n ->
  M Ⓑ[x ⊕ i] = m Ⓑ[x ⊕ i].
Proof. intros s0 m M x n i [F _] NOV I. apply F. exact (outside96 x n _ i NOV I). Qed.

Lemma frm96_frame: forall s0 m M, frm96 s0 m M -> stack_frame m M (s0 R_RSP) 96.
Proof. intros s0 m M [F _] b B. apply F, B. Qed.

Lemma acc_lt: forall kf j, acc kf j < 2^32.
Proof.
  intros kf j. induction j using N.peano_ind.
  - reflexivity.
  - rewrite <- N.add_1_r, acc_succ. apply lor_bound. exact IHj. apply N.mod_lt. discriminate.
Qed.

Lemma acc_ext:
  forall kf kg j, (forall i, i < j -> kf i = kg i) -> acc kf j = acc kg j.
Proof.
  intros kf kg j. induction j using N.peano_ind; intro H.
  - reflexivity.
  - rewrite <- N.add_1_r, !acc_succ. rewrite IHj by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sub96_48: forall x L rsp, ~ overlap 64 x L (rsp ⊖ 96) 96 -> ~ overlap 64 x L (rsp ⊖ 48 ⊖ 48) 48.
Proof.
  intros x L rsp NOV [i [j [I [J E]]]]. apply NOV. exists i, j. split. exact I. split. lia.
  rewrite E. f_equal. f_equal. mlia.
Qed.

Lemma f96_48: forall b rsp, 96 <= msub 64 b (rsp ⊖ 96) -> 48 <= msub 64 b (rsp ⊖ 48 ⊖ 48).
Proof. intros. mlia. Qed.

Lemma slot_48: forall a rsp j, (j = 8 \/ j = 16 \/ j = 24 \/ j = 32 \/ j = 48) ->
  msub 64 a (rsp ⊖ j) < 8 -> 48 <= msub 64 a (rsp ⊖ 48 ⊖ 48).
Proof. intros a rsp j J A. destruct J as [J|[J|[J|[J|J]]]]; subst j; mlia. Qed.

(* strchr's frame keeps frm96 *)
Lemma frm96_after:
  forall s0 m M M', frm96 s0 m M -> stack_frame M M' (s0 R_RSP ⊖ 48) 48 -> frm96 s0 m M'.
Proof.
  intros s0 m M M' [F [S8 [S16 [S24 S32]]]] SF. split; [|split; [|split; [|split]]].
  - intros b B. rewrite (SF b (f96_48 b _ B)). apply F, B.
  - rewrite <- S8. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_48 a _ 8). left; reflexivity. exact A.
  - rewrite <- S16. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_48 a _ 16). right; left; reflexivity. exact A.
  - rewrite <- S24. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_48 a _ 24). right; right; left; reflexivity. exact A.
  - rewrite <- S32. apply getmem_frame_mem. intros a A. rewrite <- !getmem_1 with (e:=LittleE).
    apply SF. apply (slot_48 a _ 32). right; right; right; left; reflexivity. exact A.
Qed.

Lemma ra_after:
  forall M M' rsp v, stack_frame M M' (rsp ⊖ 48) 48 -> M Ⓠ[rsp ⊖ 48] = v -> M' Ⓠ[rsp ⊖ 48] = v.
Proof.
  intros M M' rsp v SF V. rewrite <- V. apply getmem_frame_mem. intros a A.
  rewrite <- !getmem_1 with (e:=LittleE). apply SF. apply (slot_48 a _ 48). right; right; right; right; reflexivity. exact A.
Qed.

Lemma cfree_len:
  forall m p c k L, cfree m p c k -> m Ⓑ[p ⊕ L] = 0 -> k <= L.
Proof.
  intros m p c k L CF Z. destruct (N.le_gt_cases k L) as [H|H]. exact H.
  exfalso. exact (proj1 (CF L H) Z).
Qed.

Lemma or_shift32:
  forall A k e, A < 2^32 -> (A .| ((k mod 2^32) << e)) mod 2^32 = A .| ((k << e) mod 2^32).
Proof.
  intros A k e HA. apply N.bits_inj. intro i. destruct (N.lt_ge_cases i 32) as [I|I].
  - rewrite N.mod_pow2_bits_low by exact I. rewrite !N.lor_spec. rewrite (N.mod_pow2_bits_low (k << e)) by exact I.
    f_equal. destruct (N.lt_ge_cases i e) as [E|E].
    + rewrite !N.shiftl_spec_low by exact E. reflexivity.
    + rewrite !N.shiftl_spec_high' by exact E. apply N.mod_pow2_bits_low. lia.
  - rewrite N.mod_pow2_bits_high by exact I. rewrite N.lor_spec, (N.mod_pow2_bits_high (k << e)) by exact I.
    rewrite Bool.orb_false_r. symmetry. destruct A as [|a]. reflexivity. apply N.bits_above_log2.
    apply N.log2_lt_pow2 in HA. lia. lia.
Qed.

Lemma tab_pos: forall k, tab + k <> 0.
Proof. intros. unfold tab. lia. Qed.

Lemma msub_tab: forall k, msub 32 (tab + k) tab = k mod 2^32.
Proof. intros. unfold tab, msub. change (2^32) with 4294967296 in *. lia. Qed.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Ltac pure_lia := repeat match goal with H: _ |- _ => clear H end; lia.

Theorem a64l_correct:
  forall prog s t s' x' m p
         (A64L: a64l_amd64 ⊆2 prog) (STRCHR: strchr_amd64 ⊆2 prog)
         (STRCHRNUL: strchrnul_amd64 ⊆2 prog) (STRLEN: strlen_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x155c28, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p)
         (OK: a64l_ok m p (s R_RSP)),
  satisfies_all prog (a64l_invs s m p) a64l_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p A64L STRCHR STRCHRNUL STRLEN ENTRY MDL MEM P OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (RBPB: s0 R_RBP < 2^64) by (apply (MDL R_RBP 64); reflexivity).
  assert (R12B: s0 R_R12 < 2^64) by (apply (MDL R_R12 64); reflexivity).
  assert (R13B: s0 R_R13 < 2^64) by (apply (MDL R_R13 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=a64l_program).
    unfold a64l_program, strchr_program, strchrnul_program. repeat apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold a64l_invs.
    unfold a64l_program, strchr_program, strchrnul_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p MDL MEM P OK RB RBXB RBPB R12B R13B PB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply a64l_program_welltyped. intro MDL1.
  clear - PRE MDL1 OK RB RBXB RBPB R12B R13B PB. rename t1 into t.
  destruct OK as [(L & NLT & ZLT & LB & OVT) OVS].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [P [RSP CS]]].
    repeat x64_step.
    pose proof CS as (B0 & B1 & B2 & B3 & B4 & B5). rewrite B0, B1, B2, B3.
    exists 0, (fun _ => 0). split. reflexivity.
    split. intros i I. exfalso. exact (N.nlt_0_r i I).
    split. apply frm96_init; assumption.
    split. rewrite N.add_0_r, N.mod_small by exact PB. reflexivity.
    split. reflexivity. split. reflexivity. split. reflexivity. split. reflexivity.
    unfold cs2. repeat split; reg; assumption.
  - destruct PRE as [j [kf [J6 [PRE [FR [R12 [RBP [R13 [RBX [RSP CS]]]]]]]]]].
    assert (BS: s1 V_MEM64 Ⓑ[p ⊕ j] = m Ⓑ[p ⊕ j]) by exact (frm96_byte s0 m _ p 6 j FR OVS J6).
    assert (SX: scast 8 64 (m Ⓑ[p ⊕ j]) mod 2^8 = m Ⓑ[p ⊕ j])
      by (rewrite scast_low by discriminate; apply N.mod_small, (getmem_bound 64 LittleE 1)).
    pose proof FR as [_ [T8 [T16 [T24 T32]]]].
    repeat x64_step.
    all: rewrite ?BS, ?SX in *.
    + match goal with BC: (_ =? 0) = true |- _ => apply N.eqb_eq in BC end.
      rewrite T8, T16, T24, T32, N.shiftr_0_r, N.mod_small by apply acc_lt.
      split. exists j, kf. split. clear - J6; lia. split. exact PRE. split. right. left. assumption. reflexivity.
      split. exact (frm96_frame _ _ _ FR).
      split. apply N.mod_small. exact RB.
      destruct CS as (C4 & C5). unfold callee_saved_eq. repeat split; reg; sassumption.
    + match goal with BC: (_ =? 0) = false |- _ => apply N.eqb_neq in BC end.
      exists j, kf. conj_tac.
      destruct CS as (C4 & C5). unfold cs2. repeat split; reg; assumption.
  - destruct PRE as [j [kf [J6 [PF [NZ [RSI [RDI [FR [R12 [RBP [R13 [RBX [RSP CS]]]]]]]]]]]]].
    x64_step.
    match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
    apply (models_after_steps a64l_program _ _ _ _ s2 nil _ s1 t MDL1 a64l_program_welltyped).
    intro MDL2.
    pose proof (frm96_ra _ _ _ 0x155c53 FR) as FR2.
    assert (TB: forall i, i <= L -> (s1 V_MEM64 [Ⓠs0 R_RSP ⊖ 48 := 0x155c53]) Ⓑ[tab ⊕ i] = m Ⓑ[tab ⊕ i])
      by (intros i I; apply (frm96_byte s0 m _ tab (L + 1) i FR2 OVT); lia).
    eapply (call_leaf_ni a64l_program strchr_program _ _ (strchr_invs s2 (s2 V_MEM64) tab (s2 R_RSI)) strchr_exit).
    + apply subset_updateall2.
    + intros a s t' EXIT NOCODE. unfold strchr_invs.
      unfold strchr_program, strchrnul_program, updateall2, updateall in NOCODE.
      repeat first
      [ reflexivity | discriminate EXIT | discriminate NOCODE
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros t' [x' s'] START. apply strchr_correct; first
        [ apply strchr_in_prog | apply strchrnul_in_prog | apply strlen_in_prog
        | assumption | reflexivity | (unfold s2; reg; assumption) | idtac ].
      unfold s2. reg. exists L. split.
      * intros i I. rewrite TB by (clear - I; lia). apply NLT, I.
      * split. rewrite TB by (clear; lia). exact ZLT.
        apply sub96_48, OVT.
    + intros a s t' NC. unfold a64l_invs, a64l_exit.
      unfold strchr_program, strchrnul_program, updateall2, updateall in NC.
      repeat first
      [ split | reflexivity | (exfalso; apply NC; reflexivity)
      | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    + intros [[a|i] s] t'; reflexivity.
    + intros [[a|i] s] t'; reflexivity.
    + intros a s t' X. unfold strchr_exit in X. addr_cases X; discriminate.
    + split; reflexivity.
    + intros. split; reflexivity.
    + intros a' s' t2 ENTRY' UT PRE.
      unfold get_postcondition in PRE.
      destruct (strchr_exit _) eqn:EX; [|destruct PRE].
      unfold strchr_exit in EX. addr_cases EX.
      simpl in PRE.
      apply (models_after_steps _ _ _ _ _ s' t2 _ s1 t MDL1 a64l_program_welltyped).
      intro MDL3.
      destruct PRE as [[k [CF RES]] [SF [RSP' CS']]].
      unfold s2 in CF, RES, SF, RSP', CS'.
      rewrite ?update_updated in CF, RES, SF.
      rewrite !update_frame in RSP' by discriminate. rewrite update_updated in RSP'.
      rewrite ?update_frame in CF, RES by discriminate.
      rewrite ?RSI in CF, RES.

      assert (KL: k <= L).
      { apply (cfree_len _ tab (m Ⓑ[p ⊕ j]) k L CF). rewrite TB by (clear; lia). exact ZLT. }
      assert (CFm: cfree m tab (m Ⓑ[p ⊕ j]) k)
        by (intros i I; rewrite <- (TB i) by (clear - I KL; lia); apply CF, I).
      pose proof (frm96_after _ _ _ _ FR2 SF) as FR3.
      pose proof (ra_after _ _ _ _ SF ltac:(rewrite getmem_setmem by discriminate; reflexivity)) as RA.
      destruct CS' as (C0 & C1 & C2 & C3 & C4 & C5). rewrite !update_frame in C0, C1, C2, C3, C4, C5 by discriminate.
      rewrite (TB k KL) in RES.
      assert (TK: tab ⊕ k = tab + k) by (apply N.mod_small; unfold tab; change (2^64) with 18446744073709551616; clear - KL LB; change (2^63) with 9223372036854775808 in LB; lia).
      destruct RES as [[HK RAXv]|[HK [_ RAXv]]].
      * rewrite TK in RAXv.
        set (kf' := fun i => if i =? j then k else kf i).
        assert (ACCj: acc kf' j = acc kf j) by (apply acc_ext; intros i I; unfold kf'; destruct (N.eqb_spec i j) as [E|E]; [subst i; exfalso; exact (N.lt_irrefl _ I) | reflexivity]).
        assert (KJ: kf' j = k) by (unfold kf'; rewrite N.eqb_refl; reflexivity).
        assert (PF': forall i, i < j + 1 -> m Ⓑ[p ⊕ i] <> 0 /\ dig m (m Ⓑ[p ⊕ i]) (kf' i)).
        { intros i I. unfold kf'. destruct (N.eqb_spec i j) as [->|NE].
          - split. exact NZ. split. exact CFm. exact HK.
          - apply PF. clear - I NE; lia. }
        assert (R13': (s1 R_R13 .| msub 32 (tab + k) (s1 R_RBX) << s1 R_RBP mod 32) mod 2^32 = acc kf' (j + 1)).
        { rewrite R13, RBX, RBP, msub_tab.
          rewrite (N.mod_small (6*j)) by (clear - J6; lia).
          rewrite acc_succ, ACCj, KJ. apply or_shift32, acc_lt. }
        pose proof FR3 as [_ [T8 [T16 [T24 T32]]]].
        x64_step. rewrite RA. repeat x64_step.
        -- match goal with BC: (tab + k =? 0) = true |- _ => apply N.eqb_eq in BC; exfalso; exact (tab_pos k BC) end.
        -- match goal with BC: (_ =? 30) = true |- _ => apply N.eqb_eq in BC; rename BC into B30 end.
           rewrite ?RBP, (N.mod_small (6*j)) in B30 by (clear - J6; lia).
           assert (J5: j = 5) by (clear - B30; lia).
           rewrite R13', N.shiftr_0_r, N.mod_small by apply acc_lt.
           rewrite T8, T16, T24, T32.
           split. exists (j + 1), kf'. split. clear - J5; lia. split. exact PF'.
             split. left. clear - J5; lia. reflexivity.
           split. exact (frm96_frame _ _ _ FR3).
           split. apply N.mod_small. exact RB.
           destruct CS as (B4 & B5). unfold callee_saved_eq. repeat split; reg; first [sassumption | (rewrite ?C4, ?C5; sassumption)].
        -- match goal with BC: (_ =? 30) = false |- _ => apply N.eqb_neq in BC; rename BC into B30 end.
           rewrite ?RBP, (N.mod_small (6*j)) in B30 by (clear - J6; lia).
           assert (J5: j + 1 < 6) by (clear - B30 J6; lia).
           exists (j + 1), kf'. split. exact J5. split. exact PF'. split. exact FR3.
           split. rewrite R12, N.add_mod_idemp_r by discriminate. f_equal. pure_lia.
           split. rewrite RBP, N.mod_small by (clear - J6; lia). clear; lia.
           split. exact R13'. split. exact RBX. split. reflexivity.
           destruct CS as (B4 & B5). unfold cs2. reg. rewrite ?C4, ?C5. repeat split; assumption.
      * pose proof FR3 as [_ [T8 [T16 [T24 T32]]]].
        x64_step. rewrite RA. repeat x64_step.
        rewrite R13, N.shiftr_0_r, N.mod_small by apply acc_lt.
        rewrite T8, T16, T24, T32.
        split. exists j, kf. split. clear - J6; lia. split. exact PF.
          split. right. right. exists k. split. exact CFm. exact HK. reflexivity.
        split. exact (frm96_frame _ _ _ FR3).
        split. apply N.mod_small. exact RB.
        destruct CS as (B4 & B5). unfold callee_saved_eq. repeat split; reg; first [sassumption | (rewrite ?C4, ?C5; sassumption)].
Qed.
