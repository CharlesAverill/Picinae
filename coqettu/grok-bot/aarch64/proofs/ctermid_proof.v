(* ctermid -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (tail-calls strcpy)

   SEMANTICS
   ---------
   musl's src/unistd/ctermid.c:
       char *ctermid(char *s) { return s ? strcpy(s, "/dev/tty") : "/dev/tty"; }
   compiled to
       cbz x0, L; adrp x1, 0x9f000; add x1, x1, #0x980; b strcpy;
       L: adrp x0, 0x9f000; add x0, x0, #0x980; ret.
   The literal "/dev/tty" is in .rodata at ELF 0x9f980 (Ghidra 0x19f980):
   bytes 2f 64 65 76 2f 74 74 79 00 in the binary.

   SPECIFICATION (man 3 ctermid, Linux man-pages 6.9.1)
   ----------------------------------------------------
     SYNOPSIS
            #include <stdio.h>
            char *ctermid(char *s);
     DESCRIPTION
            ctermid() returns a string which is the pathname for the current
            controlling terminal for this process.  If s is NULL, a static
            buffer is used, otherwise s points to a buffer used to hold the
            terminal pathname.  The symbolic constant L_ctermid is the
            maximum number of characters in the returned pathname.
     RETURN VALUE
            The pointer to the pathname.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            ctermid at 0x68c94 (ELF vaddr); 0x168c94 in Ghidra (image base 0x100000)
            strcpy at 0x5eccc (ELF vaddr); 0x15eccc in Ghidra
            stpcpy at 0x5e950 (ELF vaddr); 0x15e950 in Ghidra
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/ctermid_armv8.v (and the strcpy/stpcpy lifts).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s = d; SP = sp; X30 = raddr; X29 = x29; X19 = x19; memory m.
   Output:  Two theorems, split on the argument:
            - ctermid_null_partial_correctness (d = 0): if the RET (0x168cac)
              is reached, X0 = 0x19f980 (the "/dev/tty" literal), memory = m,
              SP = sp, X30 = raddr.
            - ctermid_partial_correctness (d <> 0): ctermid satisfies exactly
              strcpy's invariant set and postcondition (proofs/strcpy_proof.v)
              for strcpy(d, 0x19f980): at strcpy's RET (0x15ecec) X0 = d and
              memory is the byte copy of the NUL-terminated string at
              0x19f980 to d (over strcpy's saved frame; see strcpy_post).
              The three instructions before the tail branch are peeled with
              GrokTail.step_satisfies_all, the branch with
              tailcall_satisfies_all; no assumption is made about the bytes
              at 0x19f980.
            ctermid itself writes no memory and no callee-saved register
            (the ctermid_preserves theorems).
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import ctermid_armv8.
From Grok.lifted Require strcpy_armv8 stpcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokTail.
From Grok.proofs Require strcpy_proof.
Import ARM8Notations.
Open Scope N.

(* ---------------------------------------------------------------------- *)
(* Frame theorems (ctermid alone)                                          *)

Theorem ctermid_nwc: ∀ s2 s1, ctermid_armv8 s1 = ctermid_armv8 s2.
Proof. reflexivity. Qed.

Theorem ctermid_welltyped: welltyped_prog arm8typctx ctermid_armv8.
Proof. Picinae_typecheck. Qed.

Theorem ctermid_preserves_memory:
  forall_endstates ctermid_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem ctermid_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates ctermid_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem ctermid_preserves_x30:
  forall_endstates ctermid_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Case s = NULL: returns the static buffer 0x19f980 (Ghidra address).     *)

Section NullInvariants.
  Variables (sp mem raddr : N).
  Definition null_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x168c94 => Inv 0 (s R_X0 = 0 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | 0x168cac => Post 0 (s R_X0 = 0x19f980 /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr)
    | _ => NoInv
    end.
  Definition ctermid_null_exits := make_exits 0 ctermid_armv8 null_invs.
  Definition ctermid_null_invs := make_invs 0 ctermid_armv8 null_invs.
End NullInvariants.

Theorem ctermid_null_partial_correctness:
  ∀ prog s sp mem raddr t xs'
    (PROG: ctermid_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x168c94, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = 0),
  satisfies_all prog (ctermid_null_invs sp mem raddr) (ctermid_null_exits sp mem raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=ctermid_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold ctermid_null_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply ctermid_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as (X0 & MEM & SP & X30).
  repeat arm8_step.
  all: try (rewrite X0 in BC; discriminate BC).
  all: repeat split; try reflexivity; try assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* Case s <> NULL: strcpy(s, buf) as a tail call, via step_satisfies_all.  *)

Ltac xinv := repeat match goal with
 | H: exec_stmt _ _ (Seq _ _) _ _ _ |- _ => inversion H; subst; clear H
 | H: exec_stmt _ _ (Move _ _) _ _ _ |- _ => inversion H; subst; clear H
 | H: exec_stmt _ _ (If _ _ _) _ _ _ |- _ => inversion H; subst; clear H
 | H: exec_stmt _ _ Nop _ _ _ |- _ => inversion H; subst; clear H
 | H: exec_stmt _ _ (Jmp _) _ _ _ |- _ => inversion H; subst; clear H
 | H: eval_exp _ _ _ _ _ |- _ => inversion H; subst; clear H
end.

Lemma cbz_nz: ∀ s0 sz q s c1 s1 x1, ctermid_armv8 s0 0x168c94 = Some (sz,q) ->
  s R_X0 <> 0 -> exec_stmt archtyps s q c1 s1 x1 -> x1 = None /\ ∀ v, reset_temps s s1 v = s v.
Proof.
  intros s0 sz q s c1 s1 x1 LU NZ XS. cbv [ctermid_armv8] in LU. inversion LU; subst; clear LU.
  xinv.
  rewrite update_updated in TYP. inversion TYP; subst; clear TYP.
  rewrite update_updated in XS. cbn [eval_binop] in XS.
  destruct (N.eqb_spec (s R_X0) 0) as [E0|E0]; [contradiction|].
  cbn in XS. xinv. split. reflexivity.
  intro v. unfold reset_temps, reset_vars.
  destruct v; try reflexivity.
  all: rewrite update_frame; [reflexivity | discriminate].
Qed.

Lemma step_models: ∀ p a s sz q c1 s1 x1, welltyped_prog archtyps p -> p s a = Some (sz,q) ->
  models archtyps s -> exec_stmt archtyps s q c1 s1 x1 -> models archtyps (reset_temps s s1).
Proof.
  intros p a s sz q c1 s1 x1 WP LU M XS. specialize (WP s a). rewrite LU in WP. destruct WP as [c2 TS].
  assert (M1: models archtyps s1) by (eapply pres_frame_exec_stmt; eassumption).
  intros v w H. unfold reset_temps, reset_vars. rewrite H. apply M1, H.
Qed.

Lemma add_x1: ∀ s0 sz q s c1 s1 x1, ctermid_armv8 s0 0x168c9c = Some (sz,q) ->
  exec_stmt archtyps s q c1 s1 x1 ->
  x1 = None /\ reset_temps s s1 R_X1 = (s R_X1 + 2432) mod 2^64 /\ (∀ v, In v (R_X0 :: V_MEM64 :: R_SP :: R_X30 :: R_X29 :: R_X19 :: nil) -> reset_temps s s1 v = s v).
Proof.
  intros s0 sz q s c1 s1 x1 LU XS. cbv [ctermid_armv8] in LU. inversion LU; subst; clear LU.
  xinv.
  repeat match goal with H: _ = Some ?w |- _ => is_var w; cbn in H; inversion H; subst; clear H end.
  split. reflexivity. split.
  unfold reset_temps, reset_vars. cbn. reflexivity.
  intros v IN. repeat (destruct IN as [<-|IN]; [unfold reset_temps, reset_vars; cbn; reflexivity|]). destruct IN.
Qed.

Definition ct_pre (mem d sp raddr x29 x19 : N) (s:store) :=
  models arm8typctx s /\ s R_X0 = d /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
  s R_X29 = x29 /\ s R_X19 = x19.

Ltac ct_q a := let v := eval cbv in (ctermid_armv8 (fun _ => 0) a) in
  match v with Some (_, ?q) => exact q end.

Theorem ctermid_partial_correctness:
  ∀ prog s sp mem raddr d x29 x19 t xs'
    (P2: ctermid_armv8 ⊆2 prog)
    (P1: strcpy_armv8.strcpy_armv8 ⊆2 prog) (P0: stpcpy_armv8.stpcpy_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x168c94, s))
    (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr)
    (X0: s R_X0 = d) (X29: s R_X29 = x29) (X19: s R_X19 = x19)
    (NZ: d <> 0),
  satisfies_all prog (strcpy_proof.invs1 sp mem raddr d 0x19f980 x29 x19)
                     (strcpy_proof.exits1 sp mem raddr d 0x19f980 x29 x19) (xs'::t).
Proof.
  intros.
  set (I := strcpy_proof.invs1 sp mem raddr d 0x19f980 x29 x19).
  set (X := strcpy_proof.exits1 sp mem raddr d 0x19f980 x29 x19).
  (* cbz x0: falls through since d <> 0 *)
  apply (step_satisfies_all prog I X)
    with (a0 := 0x168c94) (a1 := 0x168c98) (sz := 4) (q := ltac:(ct_q 0x168c94))
         (P := ct_pre mem d sp raddr x29 x19) (Q := ct_pre mem d sp raddr x29 x19) (s := s).
  1,2: intros [[a|i] s1] t1 t2; reflexivity.
  1,2,3: try reflexivity; intros; reflexivity.
  intro s1. apply P2. reflexivity.
  2: { intros s1 t1 xs1 START1 PQ.
  (* adrp x1 *)
  apply (step_satisfies_all prog I X)
    with (a0 := 0x168c98) (a1 := 0x168c9c) (sz := 4) (q := ltac:(ct_q 0x168c98))
         (P := ct_pre mem d sp raddr x29 x19)
         (Q := fun s => ct_pre mem d sp raddr x29 x19 s /\ s R_X1 = 0x19f000) (s := s1).
  1,2: intros [[a|i] s2] t2 t3; reflexivity.
  1,2,3: try reflexivity; intros; reflexivity.
  intro s2. apply P2. reflexivity.
  2: { intros s2 t2 xs2 START2 PQ2.
  (* add x1, x1, #0x980 *)
  apply (step_satisfies_all prog I X)
    with (a0 := 0x168c9c) (a1 := 0x168ca0) (sz := 4) (q := ltac:(ct_q 0x168c9c))
         (P := fun s => ct_pre mem d sp raddr x29 x19 s /\ s R_X1 = 0x19f000)
         (Q := fun s => ct_pre mem d sp raddr x29 x19 s /\ s R_X1 = 0x19f980) (s := s2).
  1,2: intros [[a|i] s3] t3 t4; reflexivity.
  1,2,3: try reflexivity; intros; reflexivity.
  intro s3. apply P2. reflexivity.
  2: { intros s3 t3 xs3 START3 PQ3.
  (* b strcpy *)
  apply (tailcall_satisfies_all prog I X)
    with (a0 := 0x168ca0) (a1 := 0x15eccc)
         (P := fun s => ct_pre mem d sp raddr x29 x19 s /\ s R_X1 = 0x19f980) (s := s3).
  1,2: intros [[a|i] s4] t4 t5; reflexivity.
  1,2,3: try reflexivity; intros; reflexivity.
  intro s4. apply P2. reflexivity.
  intros s4 s5 EQ ((M & H1 & H2 & H3 & H4 & H5 & H6) & H7). unfold ct_pre. rewrite <- !EQ.
    repeat split; try assumption. intros v w CV. rewrite <- EQ. exact (M v w CV).
  intros s4 t4 xs4 START4 ((M & H1 & H2 & H3 & H4 & H5 & H6) & H7).
    eapply strcpy_proof.strcpy_partial_correctness; eassumption.
  exact START3. exact PQ3. }
  (* STEP for add *)
  intros s3 c1 s4 x1 ((M & H1 & H2 & H3 & H4 & H5 & H6) & H7) XS.
  destruct (add_x1 s3 4 _ s3 c1 s4 x1 eq_refl XS) as (-> & RX1 & KEEP).
  split. reflexivity.
  assert (MU := step_models ctermid_armv8 0x168c9c s3 4 _ c1 s4 None ctermid_welltyped eq_refl M XS).
  unfold ct_pre. rewrite RX1, H7. rewrite !KEEP by (cbn; tauto). repeat split; assumption.
  exact START2. exact PQ2. }
  (* STEP for adrp *)
  intros s2 c1 s3 x1 (M & H1 & H2 & H3 & H4 & H5 & H6) XS.
  assert (MU := step_models ctermid_armv8 0x168c98 s2 4 _ c1 s3 x1 ctermid_welltyped eq_refl M XS).
  cbv in XS. inversion XS; subst. inversion E; subst. split. reflexivity.
  unfold ct_pre. repeat rewrite (reset_move _ R_X1 _ 64) by reflexivity.
  repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].
  repeat split; try assumption; try reflexivity.
  exact START1. exact PQ. }
  (* STEP for cbz *)
  intros s1 c1 s2 x1 (M & H1 & H2 & H3 & H4 & H5 & H6) XS.
  assert (NZ1: s1 R_X0 <> 0) by (rewrite H1; exact NZ).
  assert (MU := step_models ctermid_armv8 0x168c94 s1 4 _ c1 s2 x1 ctermid_welltyped eq_refl M XS).
  destruct (cbz_nz s1 4 _ s1 c1 s2 x1 eq_refl NZ1 XS) as [-> EQ].
  split. reflexivity.
  unfold ct_pre. rewrite !EQ. repeat split; assumption.
  exact ENTRY.
  unfold ct_pre. repeat split; assumption.
Qed.
