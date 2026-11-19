(* getenv: program (getenv + strncmp + __strchrnul + strlen), frame, environment helpers and the level-indexed invariant family.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in getenv_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
From Stdlib Require Import FunctionalExtensionality.
Require Import Picinae_armv8.
From Grok.lifted Require getenv_armv8 strncmp_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require strchrnul_proof strncmp_proof.
Import ARM8Notations.
Open Scope N.

Definition gv_prog : program :=
  updateall2 (updateall2 getenv_armv8.getenv_armv8 strncmp_armv8.strncmp_armv8) strchrnul_proof.strchrnul_prog.

(* getenv's 48-byte frame: X29, X30 at sp-48/-40, X19, X20 at sp-32/-24, X21 at sp-16 *)
Definition gv_frame (sp mem raddr x19 x20 x21 x29 : N) :=
  mem [Ⓠ sp ⊖ 48 := x29] [Ⓠ sp ⊖ 40 := raddr] [Ⓠ sp ⊖ 16 := x21] [Ⓠ sp ⊖ 32 := x19] [Ⓠ sp ⊖ 24 := x20].

(* __environ: GOT slot 0x1bffa8 holds &__environ *)
Definition gv_env (m:memory) := m Ⓠ[m Ⓠ[0x1bffa8]].
Definition env_entry (m:memory) (E j:N) := m Ⓠ[E + 8 * j].
Definition gv_match (m:memory) (name e l:N) := mem_eq m name e l /\ m Ⓑ[e + l] = 0x3d.
Definition gv_skip (m:memory) (name E l j:N) :=
  ∀ i, i < j -> env_entry m E i ≠ 0 /\ ¬ gv_match m name (env_entry m E i) l.

Section Invariants.
  Variables (sp mem raddr x19 x20 x21 x29 name L q k19 : N).
  Definition gv_M := gv_frame sp mem raddr x19 x20 x21 x29.
  Definition gv_KC := (R_X21, name) :: nil.
  Definition gv_KS := (R_X19, k19) :: (R_X20, L) :: (R_X21, name) :: nil.
  Definition gv_post (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29 /\
    s V_MEM64 = gv_M /\
    ((s R_X0 = 0 /\ (L = 0 \/ gv_M Ⓑ[name + L] ≠ 0 \/ gv_env gv_M = 0 \/
                     ∃ J, gv_skip gv_M name (gv_env gv_M) L J /\ env_entry gv_M (gv_env gv_M) J = 0)) \/
     (∃ j, gv_skip gv_M name (gv_env gv_M) L j /\ env_entry gv_M (gv_env gv_M) j ≠ 0 /\
           gv_match gv_M name (env_entry gv_M (gv_env gv_M) j) L /\
           s R_X0 = env_entry gv_M (gv_env gv_M) j ⊕ (L + 1))).
  Definition gv_loop (s:store) :=
    ∃ j, s R_X19 = gv_env gv_M ⊕ (8 * j) /\ s R_X20 = L /\ s R_X21 = name /\
         0 < L /\ gv_M Ⓑ[name + L] = 0 /\ gv_env gv_M ≠ 0 /\ gv_skip gv_M name (gv_env gv_M) L j /\
         s V_MEM64 = gv_M /\ s R_SP = sp ⊖ 48.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x11ff88 => Inv 3 (s R_X0 = name /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         s R_X19 = x19 /\ s R_X20 = x20 /\ s R_X21 = x21 /\ s R_X29 = x29)
    | 0x11ffdc => Inv 3 (gv_loop s)
    | 0x11ffd4 => Post 3 (gv_post s)
    | 0x15f110 | 0x15f11c | 0x15f140 =>
        strncmp_proof.invs (sp ⊖ 48) gv_M 0x11fff0 name q L T
          (fun n P => Inv (n + 2) (P /\ keepl_st gv_KS s)) (fun n P => Post (n + 2) (P /\ keepl_st gv_KS s)) NoInv s a
    | 0x15ebf4 | 0x15ec00 | 0x15ec58 | 0x15ec8c | 0x15ec40 | 0x15eca0
    | 0x15efa8 | 0x15efb4 | 0x15efd8 | 0x15eff4 | 0x15f000 =>
        strchrnul_proof.invs (sp ⊖ 48) gv_M 0x11ffa4 name 0x3d (sp ⊖ 48) T
          (fun n P => Inv n (P /\ keepl_st gv_KC s)) (fun n P => Post n (P /\ keepl_st gv_KC s)) NoInv s a
    | _ => NoInv
    end.
  Definition gv_exits3 := make_exits 3 gv_prog invs.
  Definition gv_invs3 := make_invs 3 gv_prog invs.
  Definition gv_exits2 := make_exits 2 gv_prog invs.
  Definition gv_invs2 := make_invs 2 gv_prog invs.
  Definition gv_exits1 := make_exits 1 gv_prog invs.
  Definition gv_invs1 := make_invs 1 gv_prog invs.
End Invariants.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma gv_contains3: getenv_armv8.getenv_armv8 ⊆2 gv_prog.
Proof.
  intros s a insn SC. unfold gv_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall,
    strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8, strncmp_armv8.strncmp_armv8.
  contains_tac SC.
Qed.
Lemma gv_contains2: strncmp_armv8.strncmp_armv8 ⊆2 gv_prog.
Proof.
  intros s a insn SC. unfold gv_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall,
    strlen_armv8.strlen_armv8, strchrnul_armv8.strchrnul_armv8.
  contains_tac SC.
Qed.
Lemma gv_contains1: strchrnul_proof.strchrnul_prog ⊆2 gv_prog.
Proof. apply subset_updateall2. Qed.

Theorem gv_prog_welltyped: welltyped_prog arm8typctx gv_prog.
Proof.
  intros s a. unfold gv_prog, updateall2, updateall.
  destruct (strchrnul_proof.strchrnul_prog s a) as [[sz q]|] eqn:T0.
    pose proof (strchrnul_proof.strchrnul_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
  destruct (strncmp_armv8.strncmp_armv8 s a) as [[sz q]|] eqn:T1.
    pose proof (strncmp_armv8.welltyped s a) as WT. rewrite T1 in WT. exact WT.
    apply getenv_armv8.welltyped.
Qed.

Lemma gv_prog_mono: ∀ prog, getenv_armv8.getenv_armv8 ⊆2 prog -> strncmp_armv8.strncmp_armv8 ⊆2 prog ->
  strchrnul_armv8.strchrnul_armv8 ⊆2 prog -> strlen_armv8.strlen_armv8 ⊆2 prog -> gv_prog ⊆2 prog.
Proof.
  intros prog P3 P2 P1 P0 s a insn H. unfold gv_prog, strchrnul_proof.strchrnul_prog, updateall2, updateall in H.
  destruct (strlen_armv8.strlen_armv8 s a) eqn:E0; [inversion H; subst; apply P0; exact E0|].
  destruct (strchrnul_armv8.strchrnul_armv8 s a) eqn:E1; [inversion H; subst; apply P1; exact E1|].
  destruct (strncmp_armv8.strncmp_armv8 s a) eqn:E2; [inversion H; subst; apply P2; exact E2|].
  apply P3; exact H.
Qed.
