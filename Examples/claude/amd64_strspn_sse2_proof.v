(* strspn -- length of the initial segment of a string made of accepted bytes

   SEMANTICS
   ---------
   strspn(s, accept) returns the number of leading bytes of s that occur in
   accept.  This is __strspn_sse2, the implementation glibc's strspn IFUNC
   selects on x86-64 CPUs without SSE4.2 (despite its name it uses no SIMD).
   It zeroes a 256-byte table on the stack (REP STOSQ), stores c at entry c
   for every byte c of accept, then scans s while table[c] & c is nonzero.
   Both string loops are unrolled four times.

   SPECIFICATION (man 3 strspn, Linux man-pages 5.10, Ubuntu 22.04)
   -----------------------------------------------------------------

     size_t strspn(const char *s, const char *accept);

     The strspn() function calculates the length (in bytes) of the initial
     segment of s which consists entirely of bytes in accept.

     The strspn() function returns the number of bytes in the initial segment
     of s which consist only of bytes from accept.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            __strspn_sse2 at 0x1c4780 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see strspn_sse2_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = accept, RSP = sp; m = memory on entry.  Neither
            string (up to and including its NUL) lies in the 256 bytes below
            sp, which the function uses as scratch.
   Output:  At the RET, RAX = n with spn m s accept n (amd64_cstring.v): the
            first n bytes of s are nonzero bytes of accept and byte n is not.
            RSP = sp.  Memory agrees with m outside [sp-256, sp).
 *)

Require Import Picinae_amd64.
Require Import strspn_sse2_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_cstring.
Import ListNotations.
Open Scope N.

Theorem strspn_sse2_nwc: forall s2 s1, strspn_sse2_amd64 s1 = strspn_sse2_amd64 s2.
Proof. reflexivity. Qed.

Theorem strspn_sse2_welltyped: welltyped_prog x64typctx strspn_sse2_amd64.
Proof. Picinae_typecheck. Qed.

Theorem strspn_sse2_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates strspn_sse2_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* A store inside the window, on the right-hand memory. *)
Lemma agree_setwin_r:
  forall lo len M1 M2 L a v, 0 < L -> L <= 2^64 -> len <= 2^64 -> msub 64 a lo + L <= len ->
  agree lo len M1 M2 -> agree lo len M1 (setmem 64 LittleE L M2 a v).
Proof.
  intros lo len M1 M2 L a v L0 LL LN W A b B. rewrite (A b B). symmetry.
  apply (agree_setwin lo len M2 M2 L a v L0 LL LN W (agree_refl lo len M2) b B).
Qed.

Section Invariants.
  Variables (m:memory) (s r sp:N).
  Definition T := sp ⊖ 256.

  (* Bytes r[0..L) are nonzero. *)
  Definition nz (L:N) := forall i, i < L -> m Ⓑ[r ⊕ i] <> 0.

  (* After the accept bytes r[0..L) are entered: entry c is c or 0, and is c
     (for nonzero c) exactly when c occurs among them. *)
  Definition tbl_ok (mem:memory) (L:N) :=
    forall c, c < 256 ->
      (mem Ⓑ[T ⊕ c] = 0 \/ mem Ⓑ[T ⊕ c] = c) /\
      (0 < c -> (mem Ⓑ[T ⊕ c] = c <-> exists i, i < L /\ m Ⓑ[r ⊕ i] = c)).

  (* Bytes s[0..k) are nonzero and accepted. *)
  Definition scanned (k:N) := forall i, i < k -> m Ⓑ[s ⊕ i] <> 0 /\ inset m r (m Ⓑ[s ⊕ i]).

  Definition fill_inv (u:N) (st:store) :=
    exists j, st R_RAX = r ⊕ 4*j /\ st R_RSP = T /\ st R_RDX = s /\
              st R_RCX < 256 /\ nz (4*j+u) /\
              agree T 256 m (st V_MEM64) /\ tbl_ok (st V_MEM64) (4*j+u).

  Definition scan_inv (u:N) (st:store) :=
    exists k L, st R_RAX = s ⊕ 4*k /\ st R_RSP = T /\ st R_RDX = s /\
                st R_RCX < 256 /\ slen m r L /\ scanned (4*k+u) /\
                agree T 256 m (st V_MEM64) /\ tbl_ok (st V_MEM64) L.

  Definition strspn_exit (t:trace) :=
    match t with (Addr 1853478,_)::_ => true | _ => false end.

  Definition strspn_invs (t:trace) :=
    match t with (Addr a,st)::_ => match a with
    | 1853312 => Some (st V_MEM64 = m /\ st R_RDI = s /\ st R_RSI = r /\ st R_RSP = sp)
    (* REP STOSQ: k quadwords of the table are zero *)
    | 1853340 => Some (exists k, k <= 32 /\ st R_RCX = 32 - k /\ st R_RDI = T ⊕ 8*k /\
                       st R_RAX = 0 /\ st R_DF = 0 /\ st R_RSP = T /\ st R_RDX = s /\ st R_RSI = r /\
                       agree T 256 m (st V_MEM64) /\
                       forall j, j < 8*k -> st V_MEM64 Ⓑ[T ⊕ j] = 0)
    (* filling the table from accept: one cut before each unrolled byte t,
       with bytes r[0..4j+t) entered *)
    | 1853360 => Some (fill_inv 0 st)
    | 1853369 => Some (fill_inv 1 st)
    | 1853380 => Some (fill_inv 2 st)
    | 1853391 => Some (fill_inv 3 st)
    (* scanning s: one cut before each unrolled byte u, s[0..4k+u) accepted *)
    | 1853428 => Some (scan_inv 0 st)
    | 1853435 => Some (scan_inv 1 st)
    | 1853443 => Some (scan_inv 2 st)
    | 1853451 => Some (scan_inv 3 st)
    | 1853478 => Some (spn m s r (st R_RAX) /\ st R_RSP = sp /\ agree T 256 m (st V_MEM64))
    | _ => None
    end | _ => None end.
End Invariants.

(* Reading accept (or s) through the current memory gives the original bytes
   up to and including the first NUL. *)
Lemma read_str:
  forall m mem lo p k a, agree lo 256 m mem -> strfree lo 256 m p ->
  (forall i, i < k -> m Ⓑ[p ⊕ i] <> 0) -> a mod 2^64 = (p + k) mod 2^64 ->
  mem Ⓑ[a] = m Ⓑ[p ⊕ k].
Proof.
  intros m mem lo p k a AG SF NZ A. rewrite <- getmem_mod_l, A.
  symmetry. apply AG, SF, NZ.
Qed.

Lemma tbl_upd:
  forall m r sp mem L c, tbl_ok m r sp mem L -> m Ⓑ[r ⊕ L] = c -> c < 256 ->
  tbl_ok m r sp (setmem 64 LittleE 1 mem (T sp + c) c) (L+1).
Proof.
  intros m r sp mem L c TB RC C b B. rewrite byte_setmem_cases by lia.
  assert (E: msub 64 (T sp ⊕ b) (T sp + c) = if c <=? b then b - c else 2^64 + b - c).
  { destruct (N.leb_spec c b); apply msub_add_l; change (2^64) with 18446744073709551616 in *; try lia;
    rewrite N.mod_mod by discriminate; f_equal; lia. }
  rewrite E. destruct (TB b B) as [Z EQ].
  assert (EQ': 0 < b -> ((exists i, i < L + 1 /\ m Ⓑ[r ⊕ i] = b) <-> (b = c \/ exists i, i < L /\ m Ⓑ[r ⊕ i] = b))).
  { intro B0. split.
    - intros [i [I H]]. destruct (N.eq_dec i L). subst i. left. congruence. right. exists i. split. lia. exact H.
    - intros [H|[i [I H]]]. subst b. exists L. split. lia. exact RC. exists i. split. lia. exact H. }
  assert (NE: b <> c -> 0 < b -> ((exists i, i < L /\ m Ⓑ[r ⊕ i] = b) <-> (b = c \/ exists i, i < L /\ m Ⓑ[r ⊕ i] = b))).
  { intros NE B0. split. intro HH. right. exact HH. intros [HH|HH]. contradiction. exact HH. }
  destruct (N.leb_spec c b) as [H|H]; [destruct (N.ltb_spec (b - c) 1) as [H1|H1]|].
  - assert (b = c) by lia. subst b. replace (c - c) with 0 by lia. cbn [N.mul N.add].
    rewrite xbits_0_i, N.mod_small by (change (2^8) with 256; exact C).
    split. right. reflexivity. intro C0. rewrite EQ' by exact C0. split; intros _. left. reflexivity. reflexivity.
  - assert (b <> c) by lia. split. exact Z. intro B0. rewrite EQ' by exact B0. rewrite EQ by exact B0. apply NE; assumption.
  - replace (2^64 + b - c <? 1) with false by (symmetry; apply N.ltb_ge; change (2^64) with 18446744073709551616; lia).
    assert (b <> c) by lia. split. exact Z. intro B0. rewrite EQ' by exact B0. rewrite EQ by exact B0. apply NE; assumption.
Qed.

(* Storing the NUL (c = 0) leaves the table valid for the same prefix. *)
Lemma tbl_upd0:
  forall m r sp mem L, tbl_ok m r sp mem L -> tbl_ok m r sp (setmem 64 LittleE 1 mem (T sp + 0) 0) L.
Proof.
  intros m r sp mem L TB b B. rewrite byte_setmem_cases by lia. rewrite N.add_0_r.
  destruct (N.ltb_spec (msub 64 (T sp ⊕ b) (T sp)) 1) as [H|H].
  - rewrite xbits_0_l. assert (b = 0).
    { rewrite (msub_add_l _ _ b) in H. lia. change (2^64) with 18446744073709551616. lia. apply N.mod_mod. discriminate. }
    subst b. split. left. reflexivity. intro. lia.
  - apply TB, B.
Qed.

(* The table write at T + c stays inside the frame. *)
Lemma agree_tbl:
  forall m mem sp c v, c < 256 -> agree (T sp) 256 m mem ->
  agree (T sp) 256 m (setmem 64 LittleE 1 mem (T sp + c) v).
Proof.
  intros m mem sp c v C AG.
  apply agree_setwin_r; [lia | change (2^64) with 18446744073709551616; lia
                        | change (2^64) with 18446744073709551616; lia | | exact AG].
  rewrite (msub_add_l (T sp + c) (T sp) c); [lia | change (2^64) with 18446744073709551616; lia | reflexivity].
Qed.

(* Fill-loop segment for byte u (u = 0..2) of an unrolled iteration: either
   accept[4j+u] is the NUL (go to the scan) or it is entered in the table. *)
Lemma spn_mod: forall m s r n, spn m s r n -> spn m s r (n mod 2^64).
Proof.
  intros m s r n [P E]. pose proof (N.mod_le n (2^64) ltac:(discriminate)). split.
  - intros k K. apply P. lia.
  - rewrite N.add_mod_idemp_r by discriminate. exact E.
Qed.

(* The scan's test: table[c] & c is nonzero exactly for accepted bytes. *)
Lemma tbl_test:
  forall m r sp mem L c, tbl_ok m r sp mem L -> slen m r L -> c < 256 ->
  ((mem Ⓑ[T sp + c] .& c =? 0) = false <-> c <> 0 /\ inset m r c).
Proof.
  intros m r sp mem L c TB [PRE END] C. rewrite <- getmem_mod_l.
  destruct (TB c C) as [Z EQ].
  assert (IN: c <> 0 -> (inset m r c <-> exists i, i < L /\ m Ⓑ[r ⊕ i] = c)).
  { intro C0. split.
    - intros [j [J P]]. exists j. split; [|exact J].
      destruct (N.lt_ge_cases j L) as [H|H]. exact H. exfalso.
      destruct (N.eq_dec j L) as [E|E]. subst j. congruence. apply (P L). lia. exact END.
    - intros [i [I H]]. exists i. split. exact H. intros k K. apply PRE. lia. }
  destruct (N.eq_dec c 0) as [C0|C0].
  - subst c. rewrite N.land_0_r. split; intro H; [discriminate | tauto].
  - rewrite IN by exact C0. rewrite <- EQ by lia. destruct Z as [Z|Z]; rewrite Z.
    + rewrite N.land_0_l. split; intro H. discriminate. destruct H as [_ H]. exfalso. lia.
    + rewrite N.land_diag. split; intro H. split. exact C0. reflexivity. apply N.eqb_neq. exact C0.
Qed.

Ltac fill_mid m r sp u u1 :=
  match goal with AG: agree _ _ _ ?M, SFR: strfree _ _ _ r, NZ: nz _ _ (4*?j+_) |- _ =>
    erewrite (read_str m M (T sp) r (4*j+u) _ AG SFR NZ) in *; [|f_equal; lia ..];
    change (2^8) with 256 in *;
    first
    [ match goal with BC: (_ =? 0) = true, RDX: _ R_RDX = ?s, MDL1: models _ _ |- _ =>
        apply N.eqb_eq in BC;
        assert (SB: s < 2^64) by (rewrite <- RDX; apply (MDL1 R_RDX 64); reflexivity);
        exists 0, (4*j+u); split; [rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact SB; reflexivity|];
        split; [assumption|]; split; [reflexivity|]; split; [rewrite BC; lia|];
        split; [split; [exact NZ | exact BC]|];
        split; [intros i I; lia|]; split; [exact AG | assumption] end
    | match goal with BC: (_ =? 0) = false |- _ =>
        apply N.eqb_neq in BC;
        exists j; split; [reflexivity|]; split; [reflexivity|]; split; [assumption|];
        split; [apply (getmem_bound 64 LittleE 1)|];
        split; [ let i := fresh "i" in let I := fresh "I" in let H := fresh "H" in
                 intros i I; destruct (N.lt_ge_cases i (4*j+u)) as [H|H];
                 [apply NZ, H | replace i with (4*j+u) by lia; exact BC] |];
        split; [apply agree_tbl; [apply (getmem_bound 64 LittleE 1) | exact AG]|];
        replace (4*j+u1) with (4*j+u+1) by lia;
        apply tbl_upd; [assumption | reflexivity | apply (getmem_bound 64 LittleE 1)] end ]
  end.

(* Scan segment for byte u: the byte at s + 4k + u (address form a) is
   accepted (continue) or not (return 4k + u). *)
Lemma ret_rsp: forall sp, sp < 2^64 -> 2^8 ⊕ T sp = sp.
Proof.
  intros sp SPB. unfold T. rewrite N.add_comm. change (2^8) with 256.
  rewrite msub_add. apply N.mod_small, SPB.
Qed.

(* Scan segment for byte u: the byte at address a = s + 4k + u is accepted
   (continue with k' and u', where 4k' + u' = 4k + u + 1) or not (return
   4k + u). *)
Ltac scan_mid m r s sp u a kn un :=
  match goal with AG: agree _ _ _ ?M, SFS: strfree _ _ _ s, SC: scanned _ _ _ (4*?k+_),
                  TB: tbl_ok _ _ _ _ ?L, SL: slen _ _ ?L, SPB: sp < _ |- _ =>
    let NZS := fresh "NZS" in let CB := fresh "CB" in
    assert (NZS: forall i, i < 4*k+u -> m Ⓑ[s ⊕ i] <> 0) by (intros i I; apply (SC i I));
    rewrite (read_str m M (T sp) s (4*k+u) a AG SFS NZS) in * by (f_equal; lia);
    assert (CB: m Ⓑ[s ⊕ (4*k+u)] < 256) by apply (getmem_bound 64 LittleE 1);
    first
    [ match goal with BC: (_ =? 0) = true |- _ =>
        let NOT := fresh "NOT" in
        assert (NOT: ~ (m Ⓑ[s ⊕ (4*k+u)] <> 0 /\ inset m r (m Ⓑ[s ⊕ (4*k+u)])))
          by (let H := fresh "H" in intro H; apply (tbl_test m r sp M L _ TB SL CB) in H; congruence);
        match goal with |- spn _ _ _ ?x /\ _ => replace x with ((4*k+u) mod 2^64) by (f_equal; lia) end;
        split; [apply spn_mod; split; [exact SC | exact NOT]|];
        split; [apply ret_rsp, SPB | change (2^8) with 256; exact AG] end
    | match goal with BC: (_ =? 0) = false |- _ =>
        apply (tbl_test m r sp M L _ TB SL CB) in BC;
        change (2^8) with 256 in *;
        exists kn, L; split; [f_equal; lia|]; split; [reflexivity|]; split; [assumption|];
        split; [exact CB|]; split; [exact SL|];
        split; [ let i := fresh "i" in let I := fresh "I" in let H := fresh "H" in
                 intros i I; destruct (N.lt_ge_cases i (4*k+u)) as [H|H];
                 [apply SC; lia | replace i with (4*k+u) by lia; exact BC] |];
        split; [exact AG | exact TB] end ]
  end.

Theorem strspn_sse2_correct:
  forall st t s' x' m s r sp
         (ENTRY: startof t (x',s') = (Addr 1853312, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (S: st R_RDI = s) (R: st R_RSI = r) (RSP: st R_RSP = sp)
         (SFS: strfree (T sp) 256 m s) (SFR: strfree (T sp) 256 m r),
  satisfies_all strspn_sse2_amd64 (strspn_invs m s r sp) strspn_exit ((x',s')::t).
Proof.
  intros.
  assert (SPB: sp < 2^64) by (rewrite <- RSP; apply (MDL R_RSP 64); reflexivity).
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply strspn_sse2_welltyped. intro MDL1.
  clear - PRE MDL1 SFS SFR SPB. rename t1 into t.
  destruct_inv 64 PRE.

  (* entry: SUB RSP, MOV ECX 0x20, CLD *)
  1: { destruct PRE as [MEM [SRDI [RSI RSP]]]. repeat x64_step.
    exists 0. unfold T. rewrite N.mul_0_r, N.add_0_r, N.mod_small by apply msub_lt.
    repeat split; try reflexivity; try assumption. lia.
    rewrite MEM. apply agree_refl. intros j J. lia. }

  (* REP STOSQ.  x64_step can't split the If nested in its Seq, so step by hand. *)
  1: { destruct PRE as [k [K [RCX [RDI [RAX [DF [RSP [RDX [RSI [AG Z]]]]]]]]]].
    eapply NIStep; [reflexivity|reflexivity|]. intros c s0 x XS. ISA_step_and_simplify XS.
    destruct (32 - k =? 0) eqn:BC.
    all: repeat (ISA_step_and_simplify XS).
    all: destruct XS as [XS ?]; subst x; rewrite XS; clear XS; try clear s0; try rewrite exitof_some.
    all: repeat x64_step.
    - apply N.eqb_eq in BC. assert (k = 32) by lia. subst k.
      assert (RB: r < 2^64) by (rewrite <- RSI; apply (MDL1 R_RSI 64); reflexivity).
      exists 0. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact RB.
      split. reflexivity. split. assumption. split. assumption. split. lia. split. intros i I; lia.
      split. exact AG.
      intros b B. rewrite Z by lia. split. left. reflexivity. intro C0. split. lia. intros [i [I _]]. lia.
    - apply N.eqb_neq in BC.
      assert (TB: T sp < 2^64) by apply msub_lt.
      exists (k+1). split. lia. split.
        unfold msub. change (2^64) with 18446744073709551616. rewrite (N.mod_small 1) by lia.
        replace (32 - k + (18446744073709551616 - 1)) with ((32 - (k+1)) + 1 * 18446744073709551616) by lia.
        rewrite N.mod_add by discriminate. apply N.mod_small. lia.
      split. f_equal. lia.
      split. reflexivity. split. reflexivity. split. assumption. split. assumption. split. assumption. split.
      + change (2^8) with 256. intros b B. rewrite (AG b B). symmetry. rewrite byte_setmem_cases by lia.
        destruct (N.ltb_spec (msub 64 b (T sp + 8 * k)) 8) as [I|I]; [|reflexivity].
        exfalso. apply B. unfold inwin.
        assert (E: msub 64 b (T sp) = msub 64 b (T sp + 8*k) + 8*k).
        { apply msub_add_l. change (2^64) with 18446744073709551616. lia.
          rewrite (N.add_comm _ (8*k)), N.add_assoc, add_msub. reflexivity. }
        lia.
      + intros j J. rewrite byte_setmem_cases by lia.
        assert (E: msub 64 (T sp ⊕ j) (T sp + 8 * k) = if 8*k <=? j then j - 8*k else 2^64 + j - 8*k).
        { destruct (N.leb_spec (8*k) j); apply msub_add_l; change (2^64) with 18446744073709551616 in *; try lia;
          rewrite N.mod_mod by discriminate; f_equal; lia. }
        rewrite E. destruct (N.leb_spec (8*k) j).
        * replace (j - 8*k <? 8) with true by (symmetry; apply N.ltb_lt; lia). apply xbits_0_l.
        * replace (2^64 + j - 8*k <? 8) with false by (symmetry; apply N.ltb_ge; change (2^64) with 18446744073709551616; lia).
          apply Z. lia. }

  (* filling the table, bytes 0-2 of an iteration *)
  1: { destruct PRE as [j [RAX [RSP [RDX [RCX [NZ [AG TB]]]]]]]. repeat x64_step. all: fill_mid m r sp 0 1. }
  1: { destruct PRE as [j [RAX [RSP [RDX [RCX [NZ [AG TB]]]]]]]. repeat x64_step. all: fill_mid m r sp 1 2. }
  1: { destruct PRE as [j [RAX [RSP [RDX [RCX [NZ [AG TB]]]]]]]. repeat x64_step. all: fill_mid m r sp 2 3. }

  (* byte 3: stored before it is tested *)
  1: { destruct PRE as [j [RAX [RSP [RDX [RCX [NZ [AG TB]]]]]]]. repeat x64_step.
    all: erewrite (read_str m (s1 V_MEM64) (T sp) r (4*j+3) _ AG SFR NZ) in *; [|f_equal; lia ..].
    all: change (2^8) with 256 in *.
    - apply N.eqb_eq in BC. rewrite BC.
      assert (SB: s < 2^64) by (rewrite <- RDX; apply (MDL1 R_RDX 64); reflexivity).
      exists 0, (4*j+3). split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by exact SB. reflexivity.
      split. reflexivity. split. reflexivity. split. lia.
      split. split. exact NZ. exact BC.
      split. intros i I. lia. split. apply agree_tbl. lia. exact AG. apply tbl_upd0. exact TB.
    - apply N.eqb_neq in BC.
      exists (j+1). split. f_equal. lia. split. reflexivity. split. assumption. split. apply (getmem_bound 64 LittleE 1).
      split. intros i I. destruct (N.lt_ge_cases i (4*j+3)). apply NZ, H. replace i with (4*j+3) by lia. exact BC.
      split. apply agree_tbl. apply (getmem_bound 64 LittleE 1). exact AG.
      replace (4*(j+1)+0) with (4*j+3+1) by lia. apply tbl_upd. exact TB. reflexivity. apply (getmem_bound 64 LittleE 1). }

  (* scanning s, bytes 0-3 *)
  1: { destruct PRE as [k [L [RAX [RSP [RDX [RCX [SL [SC [AG TB]]]]]]]]]. repeat x64_step.
       all: scan_mid m r s sp 0 (s + 4*k) k 1. }
  1: { destruct PRE as [k [L [RAX [RSP [RDX [RCX [SL [SC [AG TB]]]]]]]]]. repeat x64_step.
       all: scan_mid m r s sp 1 (1 + s + 4*k) k 2. }
  1: { destruct PRE as [k [L [RAX [RSP [RDX [RCX [SL [SC [AG TB]]]]]]]]]. repeat x64_step.
       all: scan_mid m r s sp 2 (2 + s + 4*k) k 3. }
  1: { destruct PRE as [k [L [RAX [RSP [RDX [RCX [SL [SC [AG TB]]]]]]]]]. repeat x64_step.
       all: scan_mid m r s sp 3 (3 + s + 4*k) (k+1) 0. }
Qed.
