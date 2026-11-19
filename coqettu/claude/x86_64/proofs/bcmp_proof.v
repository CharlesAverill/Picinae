(* bcmp -- compare byte sequences (musl x86_64, C), a tail call into memcmp

   SEMANTICS
   ---------
   musl's bcmp (src/string/bcmp.c) is

       int bcmp(const void *s1, const void *s2, size_t n)
       {
           return memcmp(s1, s2, n);
       }

   compiled to a single JMP memcmp (0x134480).  memcmp's contract
   (memcmp_proof.v) is used through tail_leaf (lib/x64_tail.v): bcmp's exits
   are memcmp's RETs.

   SPECIFICATION (man 3 bcmp, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     int bcmp(const void s1[.n], const void s2[.n], size_t n);
     bcmp compares the two byte sequences s1 and s2 of length n.  If they
     are equal, and in particular if n is zero, bcmp returns 0; otherwise it
     returns a nonzero result.  (bcmp_nonzero: musl's result is in fact
     memcmp's signed byte difference.)

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            bcmp at 0x658a0, memcmp at 0x34480 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/bcmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s1, RSI = s2, RDX = n; m = memory.  No precondition.
   Output:  At memcmp's RETs (0x1344c0, 0x1344c3), which return to bcmp's
            caller: memcmp_result m s1 s2 n RAX (RAX = 0 and the n bytes are
            equal, or RAX is the 32-bit difference of the first differing
            bytes); memory unchanged; RSP = rsp; RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.bcmp_amd64 CoqEtTu.programs.memcmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.memcmp_proof.
Open Scope N.

Definition bcmp_program : program := updateall2 bcmp_amd64 memcmp_amd64.

Theorem bcmp_welltyped: welltyped_prog x64typctx bcmp_amd64.
Proof. exact bcmp_amd64.welltyped. Qed.

Lemma bcmp_program_welltyped: welltyped_prog x64typctx bcmp_program.
Proof.
  intros s a. unfold bcmp_program, updateall2, updateall.
  destruct (memcmp_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (memcmp_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply bcmp_welltyped.
Qed.

Definition bcmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1344c0 | 0x1344c3 => true
  | _ => false end | _ => false end.

Definition bcmp_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1658a0 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1344c0 | 0x1344c3 => Some (memcmp_post s0 m l r n s)
  | _ => None
  end | _ => None end.

Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

Theorem bcmp_correct:
  forall prog s t s' x' m l r n
         (BCMP: bcmp_amd64 ⊆2 prog) (MEMCMP: memcmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x1658a0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n),
  satisfies_all prog (bcmp_invs s m l r n) bcmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n BCMP MEMCMP ENTRY MDL MEM L R Nn.
  eapply satisfies_all_pmono with (p1:=bcmp_program).
    unfold bcmp_program. apply updateall2_lub; assumption.
    intros a s1 t1 EXIT NOCODE. unfold bcmp_invs.
    unfold bcmp_program, updateall2, updateall in NOCODE.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r n MDL MEM L R Nn START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply bcmp_program_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [L [R [Nn [RSP CS]]]]].
  x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::_) => set (s2 := S) end.
  apply (models_after_steps bcmp_program _ _ _ _ s2 nil _ s1 t MDL1 bcmp_program_welltyped).
  intro MDL2.
  eapply (tail_leaf_ni bcmp_program memcmp_amd64 _ _ (memcmp_invs s2 (s2 V_MEM64) l r n) memcmp_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold memcmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros t' [x' s'] START. apply memcmp_correct; first
      [ apply pf2sub_refl | assumption | reflexivity | (unfold s2; reg; assumption) ].
  - intros a s t' NC X2. unfold bcmp_invs, bcmp_exit. unfold memcmp_exit in X2.
    repeat first
    [ split | reflexivity | (exfalso; apply NC; reflexivity) | discriminate X2
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  - intros a s t' X2. unfold bcmp_exit, bcmp_invs, memcmp_invs. unfold memcmp_exit in X2.
    repeat first
    [ discriminate X2
    | (split; [reflexivity|]; unfold post_or_true, true_inv; intro POST)
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
    all: destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    all: unfold memcmp_post, callee_saved_eq in POST |- *; unfold s2 in POST.
    all: rewrite ?update_frame in POST by discriminate.
    all: rewrite MEM, RSP, B0, B1, B2, B3, B4, B5 in POST.
    all: exact POST.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold memcmp_exit in X. addr_cases X; discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.

(* bcmp's contract: zero exactly when the n bytes agree *)
Corollary bcmp_nonzero:
  forall m l r n v, memcmp_result m l r n v -> (v = 0 <-> eq_prefix m l r n).
Proof.
  intros m l r n v [[EQ V]|[K [KN [EQ [NE V]]]]].
  - split; intro; assumption.
  - split.
    + intro V0. exfalso. apply NE. subst v. unfold msub in V0.
      pose proof (getmem_bound 64 LittleE 1 m (l ⊕ K)). pose proof (getmem_bound 64 LittleE 1 m (r ⊕ K)).
      set (x := m Ⓑ[l ⊕ K]) in *. set (y := m Ⓑ[r ⊕ K]) in *. clearbody x y.
      change (2^(1*8)) with 256 in *. change (2^32) with 4294967296 in *.
      rewrite (N.mod_small y) in V0 by lia.
      apply N.Div0.mod_divides in V0. destruct V0 as [q Q]. nia.
    + intro E. exfalso. apply NE. apply E. exact KN.
Qed.
