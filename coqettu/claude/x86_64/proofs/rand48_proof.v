(* __rand48_step nrand48 lrand48 jrand48 mrand48 -- 48-bit linear congruential
   generator (musl x86_64, C)

   SEMANTICS
   ---------
   musl (src/prng/__rand48_step.c, nrand48.c, lrand48.c, jrand48.c,
   mrand48.c):

       uint64_t __rand48_step(unsigned short *xi, unsigned short *lc)
       {
           uint64_t a, x;
           x = xi[0] | xi[1]+0U<<16 | xi[2]+0ULL<<32;
           a = lc[0] | lc[1]+0U<<16 | lc[2]+0ULL<<32;
           x = a*x + lc[3];
           xi[0] = x; xi[1] = x>>16; xi[2] = x>>32;
           return x & 0xffffffffffffull;
       }
       long nrand48(unsigned short s[3]) { return __rand48_step(s, __seed48+3) >> 17; }
       long lrand48(void) { return nrand48(__seed48); }
       long jrand48(unsigned short s[3]) { return (int32_t)(__rand48_step(s, __seed48+3) >> 16); }
       long mrand48(void) { return jrand48(__seed48); }

   __rand48_step is hidden (Ghidra: FUN_0015c18f); it loads x as a dword
   and a word, and stores it back the same way.  nrand48/jrand48 CALL it
   (call_leaf_ni); lrand48/mrand48 JMP to them with xi = __seed48 (tail_leaf).

   SPECIFICATION (man 3 drand48, Linux man-pages 6.9.1, paraphrased)
   ----------------------------------------------------------------
     The functions generate pseudo-random numbers with the linear
     congruential algorithm X(n+1) = (a X(n) + c) mod 2^48.  nrand48 and
     lrand48 return nonnegative long integers uniformly distributed over
     [0, 2^31); jrand48 and mrand48 return signed long integers uniformly
     distributed over [-2^31, 2^31).  nrand48 and jrand48 use the caller's
     X stored in s; lrand48 and mrand48 use the internal buffer; a and c come
     from the internal buffer (__seed48+3 = 0x1a436e, set by lcong48).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            __rand48_step at 0x5c18f, nrand48 at 0x5c222, lrand48 at
            0x5c23b, jrand48 at 0x5c247, mrand48 at 0x5c262, __seed48 at
            0xa4368 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/FUN_0015c18f_amd64.v and
            programs/{nrand48,lrand48,jrand48,mrand48}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   __rand48_step: RDI = xi, RSI = lc.  With X = ld48 m xi, A = ld48 m lc,
            C = the word at lc+6 and v = C + X*A (r48v): RAX = v mod 2^48,
            the dword at xi is v mod 2^32, the word at xi+4 is (v>>32) mod
            2^16, every other byte unchanged (r48_out).
   nrand48/jrand48: RDI = s, with lc = 0x1a436e; precondition: s's 6 bytes
            and lc's 8 bytes are outside the 16 bytes below rsp.  RAX =
            (v mod 2^48) >> 17, resp. the sign extension of the low 32 bits
            of (v mod 2^48) >> 16; s is updated as above; nothing else
            outside the 16 bytes below rsp changes.
   lrand48/mrand48: the same with s = 0x1a4368.
   All: RSP = rsp, RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.FUN_0015c18f_amd64 CoqEtTu.programs.nrand48_amd64 CoqEtTu.programs.lrand48_amd64
               CoqEtTu.programs.jrand48_amd64 CoqEtTu.programs.mrand48_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_compose CoqEtTu.lib.x64_tail.
Require Import CoqEtTu.proofs.divs_proof.
Open Scope N.

Ltac mlia := unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.
Ltac reg := repeat first [rewrite update_updated | rewrite update_frame by discriminate].

(* 48-bit value stored as a dword and a word *)
Definition ld48 (m:memory) (a:N) := m Ⓦ[4 + a] << 32 .| m Ⓓ[a].

(* the next state before reduction mod 2^48 *)
Definition r48v (m:memory) (xi lc:N) := m Ⓦ[6 + lc] + ld48 m xi * ld48 m lc.

Definition r48_out (M m:memory) (xi lc:N) :=
  M Ⓓ[xi] = r48v m xi lc mod 2^32 /\ M Ⓦ[4 + xi] = (r48v m xi lc >> 32) mod 2^16 /\
  (forall b, 6 <= msub 64 b xi -> M Ⓑ[b] = m Ⓑ[b]).

Lemma mod32_prod: forall C xh xl ah al, xl < 2^32 -> al < 2^32 ->
  (C + xl * al) mod 2^32 = (C + (xh << 32 .| xl) * (ah << 32 .| al)) mod 2^32.
Proof.
  intros C xh xl ah al XL AL. rewrite !lor_shl by assumption.
  replace (C + (xh * 2^32 + xl) * (ah * 2^32 + al)) with
          (C + xl * al + (xh * (ah * 2^32 + al) + xl * ah) * 2^32) by ring.
  symmetry. apply N.mod_add. discriminate.
Qed.

Lemma r48_mem_out: forall (m:memory) xi lc,
  r48_out (m [Ⓓxi := m Ⓦ[6 + lc] + m Ⓓ[xi] * m Ⓓ[lc]] [Ⓦ4 + xi := r48v m xi lc >> 32]) m xi lc.
Proof.
  intros. split; [|split].
  - rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia).
    rewrite getmem_setmem by discriminate. unfold r48v, ld48. apply mod32_prod; apply getmem_bound.
  - rewrite getmem_setmem by discriminate. reflexivity.
  - intros b B. rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia).
    rewrite getmem_noverlap by (intros [x [y [X [Y E]]]]; mlia). reflexivity.
Qed.

Definition r48_exit (t:trace) :=
  match t with (Addr a,_)::_ => a =? 0x15c1ce | _ => false end.

Definition r48_invs (s0:store) (m xi lc:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? 0x15c18f then Some (s V_MEM64 = m /\ s R_RDI = xi /\ s R_RSI = lc /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if a =? 0x15c1ce then Some (s R_RAX = r48v m xi lc mod 2^48 /\ r48_out (s V_MEM64) m xi lc /\
                                     s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Theorem rand48_step_correct:
  forall prog s t s' x' m xi lc
         (P: FUN_0015c18f_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c18f, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (XI: s R_RDI = xi) (LC: s R_RSI = lc),
  satisfies_all prog (r48_invs s m xi lc) r48_exit ((x',s')::t).
Proof.
  intros.
  eapply satisfies_all_pmono; [eassumption| |].
  { intros a s1 t1 EXIT NOCODE; unfold r48_invs, r48_exit in *.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact FUN_0015c18f_amd64.welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [XI' [LC' [RSP CS]]]].
  repeat x64_step.
  split. reflexivity. split. apply r48_mem_out. conj_tac.
Qed.

Definition LC48 := 0x1a436e.
Definition SEED48 := 0x1a4368.

Definition r48_out16 (M m:memory) (xi lc rsp:N) :=
  M Ⓓ[xi] = r48v m xi lc mod 2^32 /\ M Ⓦ[4 + xi] = (r48v m xi lc >> 32) mod 2^16 /\
  (forall b, 16 <= msub 64 b (rsp ⊖ 16) -> 6 <= msub 64 b xi -> M Ⓑ[b] = m Ⓑ[b]).

Definition n48_ok (xi rsp:N) := ~ overlap 64 xi 6 (rsp ⊖ 16) 16 /\ ~ overlap 64 LC48 8 (rsp ⊖ 16) 16.

Lemma nov8: forall x n a k len, ~ overlap 64 x n (a ⊖ 16) 16 -> k + len <= n ->
  ~ overlap 64 (k + x) len (a ⊖ 16) 8.
Proof. intros x n a k len H K [i [j [I [J E]]]]. apply H. exists (k + i), j. split. lia. split. lia. rewrite <- E. f_equal. lia. Qed.

Lemma nov8_0: forall x n a len, ~ overlap 64 x n (a ⊖ 16) 16 -> len <= n -> ~ overlap 64 x len (a ⊖ 16) 8.
Proof. intros x n a len H K [i [j [I [J E]]]]. apply H. exists i, j. split. lia. split. lia. exact E. Qed.

Lemma r48v_frame: forall (m:memory) xi lc a v, ~ overlap 64 xi 6 (a ⊖ 16) 16 -> ~ overlap 64 lc 8 (a ⊖ 16) 16 ->
  r48v (m [Ⓠa ⊖ 16 := v]) xi lc = r48v m xi lc.
Proof.
  intros m xi lc a v X L. unfold r48v, ld48.
  rewrite (getmem_noverlap _ _ _ _ _ _ (6 + lc)) by exact (nov8 _ _ _ 6 2 L ltac:(lia)).
  rewrite (getmem_noverlap _ _ _ _ _ _ (4 + xi)) by exact (nov8 _ _ _ 4 2 X ltac:(lia)).
  rewrite (getmem_noverlap _ _ _ _ _ _ xi) by exact (nov8_0 _ _ _ 4 X ltac:(lia)).
  rewrite (getmem_noverlap _ _ _ _ _ _ (4 + lc)) by exact (nov8 _ _ _ 4 2 L ltac:(lia)).
  rewrite (getmem_noverlap _ _ _ _ _ _ lc) by exact (nov8_0 _ _ _ 4 L ltac:(lia)).
  reflexivity.
Qed.

Lemma ra_kept: forall (M M1:memory) xi a, ~ overlap 64 xi 6 (a ⊖ 16) 16 ->
  (forall b, 6 <= msub 64 b xi -> M Ⓑ[b] = M1 Ⓑ[b]) -> M Ⓠ[a ⊖ 16] = M1 Ⓠ[a ⊖ 16].
Proof.
  intros M M1 xi a X F. apply getmem_frame_mem. intros b B.
  rewrite <- !getmem_1 with (e:=LittleE). apply F.
  destruct (N.le_gt_cases 6 (msub 64 b xi)) as [H|H]. exact H. exfalso.
  apply X. exists (msub 64 b xi), (msub 64 b (a ⊖ 16)). split. exact H. split. lia. mlia.
Qed.

Lemma frame16: forall (m:memory) rsp v b, 16 <= msub 64 b (rsp ⊖ 16) -> (m [Ⓠrsp ⊖ 16 := v]) Ⓑ[b] = m Ⓑ[b].
Proof. intros. apply (stack_store_frame _ rsp 16 _ b 16); [lia | reflexivity | assumption]. Qed.

Definition n48_exit (r:N) (t:trace) :=
  match t with (Addr a,_)::_ => a =? r | _ => false end.

(* nrand48 (e = entry, r = RET) *)
Definition n48_invs (e r:N) (f:N -> N) (s0:store) (m xi:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s V_MEM64 = m /\ s R_RDI = xi /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ n48_ok xi (s0 R_RSP))
    else if a =? r then Some (s R_RAX = f (r48v m xi LC48 mod 2^48) /\ r48_out16 (s V_MEM64) m xi LC48 (s0 R_RSP) /\
                              s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Definition nrand48_program : program := updateall2 nrand48_amd64 FUN_0015c18f_amd64.

Lemma nrand48_program_welltyped: welltyped_prog x64typctx nrand48_program.
Proof.
  intros s a. unfold nrand48_program, updateall2, updateall.
  destruct (FUN_0015c18f_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (FUN_0015c18f_amd64.welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply nrand48_amd64.welltyped.
Qed.

Theorem nrand48_correct:
  forall prog s t s' x' m xi
         (P1: nrand48_amd64 ⊆2 prog) (P2: FUN_0015c18f_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c222, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (XI: s R_RDI = xi) (OK: n48_ok xi (s R_RSP)),
  satisfies_all prog (n48_invs 0x15c222 0x15c23a (fun x => x >> 17) s m xi) (n48_exit 0x15c23a) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m xi P1 P2 ENTRY MDL MEM XI OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=nrand48_program).
  { unfold nrand48_program. apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold n48_invs, n48_exit in *.
    unfold nrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. split. exact MEM. split. exact XI. split. reflexivity.
    split. apply callee_saved_eq_refl. exact OK.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact nrand48_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [XI' [RSP [CS [OVx OVl]]]]].
  x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps nrand48_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 nrand48_program_welltyped).
  intro MDL2.
  assert (S2M: s2 V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := 0x15c232]) by (unfold s2; reg; first [sreflexivity | (rewrite MEM'; sreflexivity)]).
  assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 16) by (unfold s2; reg; reflexivity).
  eapply (call_leaf_ni nrand48_program FUN_0015c18f_amd64 _ _ (r48_invs s2 (s2 V_MEM64) xi LC48) r48_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold r48_invs, r48_exit in *.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity].
  - intros t' [x'' s''] START'. apply rand48_step_correct; first
      [ apply pf2sub_refl | reflexivity | exact START' | exact MDL2
      | (unfold s2; reg; first [reflexivity | exact XI']) ].
  - intros a s t' NC. unfold n48_invs, n48_exit.
    destruct (N.eqb_spec a 0x15c222) as [->|_]; [exfalso; apply NC; reflexivity|].
    destruct (N.eqb_spec a 0x15c23a) as [->|_]; [exfalso; apply NC; reflexivity|].
    split; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold r48_exit in X. apply N.eqb_eq in X. subst a. discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
  - intros a' sx t2 ENTRY' UT2 PRE2.
    unfold get_postcondition in PRE2.
    destruct (r48_exit _) eqn:EX; [|destruct PRE2].
    unfold r48_exit in EX. apply N.eqb_eq in EX. subst a'.
    simpl in PRE2.
    rewrite app_assoc.
    apply (models_after_steps _ _ _ _ _ sx (t2 ++ tm) _ ss1 tt1 MDL1 nrand48_program_welltyped).
    intro MDL3.
    destruct PRE2 as [RAXv [[O1 [O2 O3]] [RSP' CS']]].
    rewrite S2M in RAXv, O1, O2, O3. rewrite S2R in RSP'.
    pose proof (r48v_frame m xi LC48 (s0 R_RSP) 0x15c232 OVx OVl) as RF.
    rewrite RF in RAXv. rewrite RF in O1. rewrite RF in O2.
    assert (RA: sx V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x15c232).
    { rewrite (ra_kept _ _ xi _ OVx O3). rewrite getmem_setmem by discriminate. reflexivity. }
    destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
    unfold s2 in D0, D1, D2, D3, D4, D5. rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
    x64_step. try rewrite RA. repeat x64_step.
    split. reflexivity.
    split. split. exact O1. split. exact O2.
      intros b B1 B2. rewrite (O3 b B2).
      exact (frame16 m (s0 R_RSP) 0x15c232 b B1).
    split. reflexivity.
    destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    unfold callee_saved_eq; repeat split; reg; rewrite ?D0, ?D1, ?D2, ?D3, ?D4, ?D5; reg; sassumption.
Qed.

Definition jrand48_program : program := updateall2 jrand48_amd64 FUN_0015c18f_amd64.

Lemma jrand48_program_welltyped: welltyped_prog x64typctx jrand48_program.
Proof.
  intros s a. unfold jrand48_program, updateall2, updateall.
  destruct (FUN_0015c18f_amd64 s a) as [[sz q]|] eqn:SL.
    pose proof (FUN_0015c18f_amd64.welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply jrand48_amd64.welltyped.
Qed.

Theorem jrand48_correct:
  forall prog s t s' x' m xi
         (P1: jrand48_amd64 ⊆2 prog) (P2: FUN_0015c18f_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c247, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (XI: s R_RDI = xi) (OK: n48_ok xi (s R_RSP)),
  satisfies_all prog (n48_invs 0x15c247 0x15c261 (fun x => scast 32 64 ((x >> 16) mod 2^32)) s m xi) (n48_exit 0x15c261) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m xi P1 P2 ENTRY MDL MEM XI OK.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=jrand48_program).
  { unfold jrand48_program. apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold n48_invs, n48_exit in *.
    unfold jrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. split. exact MEM. split. exact XI. split. reflexivity.
    split. apply callee_saved_eq_refl. exact OK.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact jrand48_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [XI' [RSP [CS [OVx OVl]]]]].
  x64_step. x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps jrand48_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 jrand48_program_welltyped).
  intro MDL2.
  assert (S2M: s2 V_MEM64 = m [Ⓠs0 R_RSP ⊖ 16 := 0x15c257]) by (unfold s2; reg; first [sreflexivity | (rewrite MEM'; sreflexivity)]).
  assert (S2R: s2 R_RSP = s0 R_RSP ⊖ 16) by (unfold s2; reg; reflexivity).
  eapply (call_leaf_ni jrand48_program FUN_0015c18f_amd64 _ _ (r48_invs s2 (s2 V_MEM64) xi LC48) r48_exit).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold r48_invs, r48_exit in *.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity].
  - intros t' [x'' s''] START'. apply rand48_step_correct; first
      [ apply pf2sub_refl | reflexivity | exact START' | exact MDL2
      | (unfold s2; reg; first [reflexivity | exact XI']) ].
  - intros a s t' NC. unfold n48_invs, n48_exit.
    destruct (N.eqb_spec a 0x15c247) as [->|_]; [exfalso; apply NC; reflexivity|].
    destruct (N.eqb_spec a 0x15c261) as [->|_]; [exfalso; apply NC; reflexivity|].
    split; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold r48_exit in X. apply N.eqb_eq in X. subst a. discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
  - intros a' sx t2 ENTRY' UT2 PRE2.
    unfold get_postcondition in PRE2.
    destruct (r48_exit _) eqn:EX; [|destruct PRE2].
    unfold r48_exit in EX. apply N.eqb_eq in EX. subst a'.
    simpl in PRE2.
    rewrite app_assoc.
    apply (models_after_steps _ _ _ _ _ sx (t2 ++ tm) _ ss1 tt1 MDL1 jrand48_program_welltyped).
    intro MDL3.
    destruct PRE2 as [RAXv [[O1 [O2 O3]] [RSP' CS']]].
    rewrite S2M in RAXv, O1, O2, O3. rewrite S2R in RSP'.
    pose proof (r48v_frame m xi LC48 (s0 R_RSP) 0x15c257 OVx OVl) as RF.
    rewrite RF in RAXv. rewrite RF in O1. rewrite RF in O2.
    assert (RA: sx V_MEM64 Ⓠ[s0 R_RSP ⊖ 16] = 0x15c257).
    { rewrite (ra_kept _ _ xi _ OVx O3). rewrite getmem_setmem by discriminate. reflexivity. }
    destruct CS' as (D0 & D1 & D2 & D3 & D4 & D5).
    unfold s2 in D0, D1, D2, D3, D4, D5. rewrite !update_frame in D0, D1, D2, D3, D4, D5 by discriminate.
    x64_step. try rewrite RA.
    remember (r48v m xi LC48) as V eqn:EV in *.
    repeat x64_step.
    subst V.
    split. rewrite N.shiftr_0_r. reflexivity.
    split. split. exact O1. split. exact O2.
      intros b B1 B2. rewrite (O3 b B2).
      exact (frame16 m (s0 R_RSP) 0x15c257 b B1).
    split. reflexivity.
    destruct CS as (B0 & B1 & B2 & B3 & B4 & B5).
    unfold callee_saved_eq; repeat split; reg; rewrite ?D0, ?D1, ?D2, ?D3, ?D4, ?D5; reg; sassumption.
Qed.

(* lrand48 / mrand48: LEA RDI,[__seed48]; JMP nrand48 / jrand48 *)
Definition l48_invs (e r:N) (f:N -> N) (s0:store) (m:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\ n48_ok SEED48 (s0 R_RSP))
    else if a =? r then Some (s R_RAX = f (r48v m SEED48 LC48 mod 2^48) /\ r48_out16 (s V_MEM64) m SEED48 LC48 (s0 R_RSP) /\
                              s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Lemma nrand48_in: nrand48_amd64 ⊆2 nrand48_program.
Proof.
  intros s a insn SC. unfold nrand48_program, updateall2, updateall.
  destruct (FUN_0015c18f_amd64 s a) eqn:F; [|exact SC].
  exfalso. revert SC F. unfold nrand48_amd64, FUN_0015c18f_amd64.
  repeat first [ discriminate | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Lemma jrand48_in: jrand48_amd64 ⊆2 jrand48_program.
Proof.
  intros s a insn SC. unfold jrand48_program, updateall2, updateall.
  destruct (FUN_0015c18f_amd64 s a) eqn:F; [|exact SC].
  exfalso. revert SC F. unfold jrand48_amd64, FUN_0015c18f_amd64.
  repeat first [ discriminate | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
Qed.

Definition lrand48_program : program := updateall2 lrand48_amd64 nrand48_program.

Lemma lrand48_program_welltyped: welltyped_prog x64typctx lrand48_program.
Proof.
  intros s a. unfold lrand48_program, updateall2 at 1, updateall.
  destruct (nrand48_program s a) as [[sz q]|] eqn:SL.
    pose proof (nrand48_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply lrand48_amd64.welltyped.
Qed.

Theorem lrand48_correct:
  forall prog s t s' x' m
         (P0: lrand48_amd64 ⊆2 prog) (P1: nrand48_amd64 ⊆2 prog) (P2: FUN_0015c18f_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c23b, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (OK: n48_ok SEED48 (s R_RSP)),
  satisfies_all prog (l48_invs 0x15c23b 0x15c23a (fun x => x >> 17) s m) (n48_exit 0x15c23a) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m P0 P1 P2 ENTRY MDL MEM OK.
  eapply satisfies_all_pmono with (p1:=lrand48_program).
  { unfold lrand48_program, nrand48_program. repeat apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold l48_invs, n48_exit in *.
    unfold lrand48_program, nrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. split. exact MEM. split. reflexivity.
    split. apply callee_saved_eq_refl. exact OK.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact lrand48_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [RSP [CS OK']]].
  x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps lrand48_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 lrand48_program_welltyped).
  intro MDL2.
  assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM').
  assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
  assert (C02: callee_saved_eq s0 s2) by
    (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
  eapply (tail_leaf_ni lrand48_program nrand48_program _ _
            (n48_invs 0x15c222 0x15c23a (fun x => x >> 17) s2 (s2 V_MEM64) SEED48) (n48_exit 0x15c23a)).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold n48_invs, n48_exit in *.
    unfold nrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity].
  - intros t' [x'' s''] START'. apply nrand48_correct;
      [ exact nrand48_in | apply subset_updateall2 | exact START' | exact MDL2 | reflexivity
      | (unfold s2; reg; reflexivity) | (rewrite S2R; exact OK') ].
  - intros a s t' NC X2. unfold l48_invs, n48_exit in *.
    destruct (N.eqb_spec a 0x15c23b) as [->|_]; [exfalso; apply NC; reflexivity|].
    destruct (N.eqb_spec a 0x15c23a) as [->|_]; [discriminate X2|].
    split; reflexivity.
  - intros a s t' X2. unfold n48_exit in X2. apply N.eqb_eq in X2. subst a.
    cbv beta iota delta [l48_invs n48_invs n48_exit N.eqb Pos.eqb post_or_true true_inv].
    split. reflexivity.
    intros [RAXv [O [RSP' CS']]]. rewrite S2M in RAXv, O. rewrite S2R in O, RSP'.
    split. exact RAXv. split. exact O. split. exact RSP'.
    exact (callee_saved_eq_trans _ _ _ C02 CS').
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold n48_exit in X. apply N.eqb_eq in X. subst a. discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.

Definition mrand48_program : program := updateall2 mrand48_amd64 jrand48_program.

Lemma mrand48_program_welltyped: welltyped_prog x64typctx mrand48_program.
Proof.
  intros s a. unfold mrand48_program, updateall2 at 1, updateall.
  destruct (jrand48_program s a) as [[sz q]|] eqn:SL.
    pose proof (jrand48_program_welltyped s a) as WT. rewrite SL in WT. exact WT.
    apply mrand48_amd64.welltyped.
Qed.

Theorem mrand48_correct:
  forall prog s t s' x' m
         (P0: mrand48_amd64 ⊆2 prog) (P1: jrand48_amd64 ⊆2 prog) (P2: FUN_0015c18f_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15c262, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (OK: n48_ok SEED48 (s R_RSP)),
  satisfies_all prog (l48_invs 0x15c262 0x15c261 (fun x => scast 32 64 ((x >> 16) mod 2^32)) s m) (n48_exit 0x15c261) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m P0 P1 P2 ENTRY MDL MEM OK.
  eapply satisfies_all_pmono with (p1:=mrand48_program).
  { unfold mrand48_program, jrand48_program. repeat apply updateall2_lub; assumption. }
  { intros a s1 t1 EXIT NOCODE; unfold l48_invs, n48_exit in *.
    unfold mrand48_program, jrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  apply prove_invs.
  simpl. rewrite START. x64_step. split. exact MEM. split. reflexivity.
    split. apply callee_saved_eq_refl. exact OK.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption. exact mrand48_program_welltyped. intro MDL1.
  destruct_inv 64 PRE.
  destruct PRE as [MEM' [RSP [CS OK']]].
  x64_step. x64_step.
  match goal with |- nextinv _ _ _ _ ((Addr _, ?S)::?T1 ++ _) => set (s2 := S); set (tm := T1) end.
  apply (models_after_steps mrand48_program _ _ _ _ s2 tm _ ss1 tt1 MDL1 mrand48_program_welltyped).
  intro MDL2.
  assert (S2M: s2 V_MEM64 = m) by (unfold s2; reg; exact MEM').
  assert (S2R: s2 R_RSP = s0 R_RSP) by (unfold s2; reg; exact RSP).
  assert (C02: callee_saved_eq s0 s2) by
    (destruct CS as (B0 & B1 & B2 & B3 & B4 & B5); unfold s2; repeat split; reg; assumption).
  eapply (tail_leaf_ni mrand48_program jrand48_program _ _
            (n48_invs 0x15c247 0x15c261 (fun x => scast 32 64 ((x >> 16) mod 2^32)) s2 (s2 V_MEM64) SEED48) (n48_exit 0x15c261)).
  - apply subset_updateall2.
  - intros a s t' EXIT NOCODE. unfold n48_invs, n48_exit in *.
    unfold jrand48_program, updateall2, updateall in NOCODE.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity].
  - intros t' [x'' s''] START'. apply jrand48_correct;
      [ exact jrand48_in | apply subset_updateall2 | exact START' | exact MDL2 | reflexivity
      | (unfold s2; reg; reflexivity) | (rewrite S2R; exact OK') ].
  - intros a s t' NC X2. unfold l48_invs, n48_exit in *.
    destruct (N.eqb_spec a 0x15c262) as [->|_]; [exfalso; apply NC; reflexivity|].
    destruct (N.eqb_spec a 0x15c261) as [->|_]; [discriminate X2|].
    split; reflexivity.
  - intros a s t' X2. unfold n48_exit in X2. apply N.eqb_eq in X2. subst a.
    cbv beta iota delta [l48_invs n48_invs n48_exit N.eqb Pos.eqb post_or_true true_inv].
    split. reflexivity.
    intros [RAXv [O [RSP' CS']]]. rewrite S2M in RAXv, O. rewrite S2R in O, RSP'.
    split. exact RAXv. split. exact O. split. exact RSP'.
    exact (callee_saved_eq_trans _ _ _ C02 CS').
  - intros [[a|i] s] t'; reflexivity.
  - intros [[a|i] s] t'; reflexivity.
  - intros a s t' X. unfold n48_exit in X. apply N.eqb_eq in X. subst a. discriminate.
  - split; reflexivity.
  - intros. split; reflexivity.
Qed.
