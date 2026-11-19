(* wcstok: program (wcstok + wcsspn + wcscspn + wcschr + wcslen), frame and the level-indexed invariant family.
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in wcstok_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require wcstok_armv8 wcsspn_armv8 wcscspn_armv8 wcschr_armv8 wcslen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokKeep.
From Grok.proofs Require wcslen_proof wcsspn_proof wcscspn_proof.
Import ARM8Notations.
Open Scope N.

Definition wt_prog : program :=
  updateall2 (updateall2 wcstok_armv8.wcstok_armv8 wcsspn_proof.wcsspn_prog) wcscspn_proof.wcscspn_prog.

(* the string wcstok scans: s itself, or the saved position *p when s is null *)
Definition wt_str (mem:memory) (s0 p:N) := if s0 =? 0 then mem Ⓠ[p] else s0.

(* wcstok's 48-byte frame: X29, X30 at sp-48/-40, X19, X20 at sp-32/-24, X21, X22 at sp-16/-8 *)
Definition wt_frame (sp mem raddr x19 x20 x21 x22 x29 : N) :=
  mem [Ⓠ sp - 48 := x29] [Ⓠ sp - 40 := raddr] [Ⓠ sp - 32 := x19] [Ⓠ sp - 24 := x20]
      [Ⓠ sp - 16 := x21] [Ⓠ sp - 8 := x22].

Definition wt_pre (sp mem s0 sep p Ls Lc : N) :=
  96 <= sp /\ sp < 2^64 /\ p + 8 <= sp - 48 /\
  (wt_str mem s0 p ≠ 0 ->
     let s := wt_str mem s0 p in
     wcslen_proof.wcs_nilfree mem s Ls /\ mem Ⓓ[s + 4*Ls] = 0 /\ Ls < 2^61 /\
     wcslen_proof.wcs_nilfree mem sep Lc /\ mem Ⓓ[sep + 4*Lc] = 0 /\ 0 < sep /\
     s + 4*Ls + 4 <= sp - 96 /\ sep + 4*Lc + 4 <= sp - 96).

Section Invariants.
  Variables (sp mem raddr x19 x20 x21 x22 x29 s0 sep p Ls Lc k ph : N).
  Definition wt_s := wt_str mem s0 p.
  Definition wt_M1 := wt_frame sp mem raddr x19 x20 x21 x22 x29.
  (* memory after wcsspn returns (its frame written below ours) *)
  Definition wt_W1 := wcsspn_proof.sspn_frame (sp - 48) wt_M1 0x160164 wt_s sep p (sp - 48).
  (* possible memories after wcscspn returns *)
  Definition wt_W2 (W:memory) :=
    W = wt_W1 \/ W = wcscspn_proof.cspn_frame (sp - 48) wt_W1 0x16017c wt_s sep p (sp - 48).
  Definition wt_KC := (R_X22, wt_s + 4*k) :: nil.

  (* SPN/CSPN in the result use the caller's original memory *)
  Definition wt_post (st:store) :=
    st R_SP = sp /\ st R_X30 = raddr /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\
    st R_X22 = x22 /\ st R_X29 = x29 /\
    ((wt_s = 0 /\ st R_X0 = 0 /\ st V_MEM64 = wt_M1) \/
     (∃ k0, k0 <= Ls /\ wcsspn_proof.spn mem wt_s sep Lc k0 /\ mem Ⓓ[wt_s + 4*k0] = 0 /\
            st R_X0 = 0 /\ st V_MEM64 = wt_W1 [Ⓠ p := 0]) \/
     (∃ k0 j W, k0 + j <= Ls /\ wcsspn_proof.spn mem wt_s sep Lc k0 /\ mem Ⓓ[wt_s + 4*k0] ≠ 0 /\
            ¬ wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s + 4*k0]) /\
            wcscspn_proof.cspn mem (wt_s + 4*k0) sep Lc j /\ st R_X0 = wt_s + 4*k0 /\ wt_W2 W /\
            ((mem Ⓓ[wt_s + 4*(k0+j)] = 0 /\ st V_MEM64 = W [Ⓠ p := 0]) \/
             (wcsspn_proof.winset mem sep Lc (mem Ⓓ[wt_s + 4*(k0+j)]) /\
              st V_MEM64 = W [Ⓓ wt_s + 4*(k0+j) := 0] [Ⓠ p := wt_s + 4*(k0+j) + 4])))).

  Definition wt_spn_invs := wcsspn_proof.invs (sp - 48) wt_M1 0x160164 wt_s sep wt_s sep p (sp - 48) Ls Lc.
  Definition wt_cspn_invs :=
    wcscspn_proof.invs (sp - 48) wt_W1 0x16017c (wt_s + 4*k) sep wt_s sep p (sp - 48) (Ls - k) Lc.

  (* ph (0 for the wcsspn call, 1 for the wcscspn call) makes the other
     callee's return points unusable as exits of a call *)
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (st:store) (a:addr) : T :=
    match a with
    | 0x16013c => Inv 2 (st R_X0 = s0 /\ st R_X1 = sep /\ st R_X2 = p /\ st V_MEM64 = mem /\ st R_SP = sp /\
                         st R_X30 = raddr /\ st R_X19 = x19 /\ st R_X20 = x20 /\ st R_X21 = x21 /\
                         st R_X22 = x22 /\ st R_X29 = x29)
    | 0x1601a8 => Post 2 (wt_post st)
    | 0x15fe6c | 0x15fe90 | 0x15feb8 =>
        wt_spn_invs T (fun n P => Inv (n + 1) P) (fun n P => Post (n + 1) (P /\ ph = 0)) NoInv st a
    | 0x15fb44 | 0x15fb70 | 0x15fc18 | 0x15fc24 | 0x15fbcc | 0x15fc34 =>
        wt_cspn_invs T (fun n P => Inv (n + 1) (P /\ keepl_st wt_KC st))
                       (fun n P => Post (n + 1) ((P /\ keepl_st wt_KC st) /\ ph = 1)) NoInv st a
    (* wcschr's loop, shared by both callees *)
    | 0x15fae0 => Inv 1 (wt_spn_invs Prop (fun _ P => P) (fun _ P => P) False st a \/
                         (wt_cspn_invs Prop (fun _ P => P) (fun _ P => P) False st a /\ keepl_st wt_KC st))
    | _ => NoInv
    end.
  Definition wt_exits2 := make_exits 2 wt_prog invs.
  Definition wt_invs2 := make_invs 2 wt_prog invs.
  Definition wt_exits1 := make_exits 1 wt_prog invs.
  Definition wt_invs1 := make_invs 1 wt_prog invs.
End Invariants.

Ltac contains_tac SC :=
  repeat first
  [ exact SC | discriminate SC | (rewrite SC; reflexivity)
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].

Lemma wt_contains2: wcstok_armv8.wcstok_armv8 ⊆2 wt_prog.
Proof.
  intros s a insn SC. unfold wt_prog, wcscspn_proof.wcscspn_prog, wcsspn_proof.wcsspn_prog, updateall2, updateall,
    wcscspn_armv8.wcscspn_armv8, wcsspn_armv8.wcsspn_armv8, wcschr_armv8.wcschr_armv8, wcslen_armv8.wcslen_armv8.
  contains_tac SC.
Qed.
Ltac wt_unf := unfold wt_prog, wcscspn_proof.wcscspn_prog, wcsspn_proof.wcsspn_prog, updateall2, updateall,
    wcstok_armv8.wcstok_armv8, wcscspn_armv8.wcscspn_armv8, wcsspn_armv8.wcsspn_armv8,
    wcschr_armv8.wcschr_armv8, wcslen_armv8.wcslen_armv8.

Lemma wt_contains_spn: wcsspn_proof.wcsspn_prog ⊆2 wt_prog.
Proof. intros s a insn SC. wt_unf. unfold wcsspn_proof.wcsspn_prog, updateall2, updateall,
    wcsspn_armv8.wcsspn_armv8, wcschr_armv8.wcschr_armv8 in SC. contains_tac SC. Qed.

Lemma wt_contains_cspn: wcscspn_proof.wcscspn_prog ⊆2 wt_prog.
Proof. apply subset_updateall2. Qed.

Theorem wt_prog_welltyped: welltyped_prog arm8typctx wt_prog.
Proof.
  intros s a. unfold wt_prog, updateall2 at 1, updateall.
  destruct (wcscspn_proof.wcscspn_prog s a) as [[sz q]|] eqn:T0.
    pose proof (wcscspn_proof.wcscspn_prog_welltyped s a) as WT. rewrite T0 in WT. exact WT.
  unfold updateall2, updateall.
  destruct (wcsspn_proof.wcsspn_prog s a) as [[sz q]|] eqn:T1.
    pose proof (wcsspn_proof.wcsspn_prog_welltyped s a) as WT. rewrite T1 in WT. exact WT.
    apply wcstok_armv8.welltyped.
Qed.

Lemma wt_prog_mono: ∀ prog, wcstok_armv8.wcstok_armv8 ⊆2 prog -> wcsspn_armv8.wcsspn_armv8 ⊆2 prog ->
  wcscspn_armv8.wcscspn_armv8 ⊆2 prog -> wcschr_armv8.wcschr_armv8 ⊆2 prog -> wcslen_armv8.wcslen_armv8 ⊆2 prog ->
  wt_prog ⊆2 prog.
Proof.
  intros prog P4 P3 P2 P1 P0 s a insn H. unfold wt_prog, updateall2 at 1, updateall in H.
  destruct (wcscspn_proof.wcscspn_prog s a) eqn:E0.
    inversion H; subst. apply (wcscspn_proof.wcscspn_prog_mono prog P2 P1 P0). exact E0.
  unfold updateall2, updateall in H.
  destruct (wcsspn_proof.wcsspn_prog s a) eqn:E1.
    inversion H; subst. apply (wcsspn_proof.wcsspn_prog_mono prog P3 P1). exact E1.
  apply P4; exact H.
Qed.
