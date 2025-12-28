Require Import tmr_ft.
Require Import Picinae_riscv.
Import RVFaultTolerance.
Import RISCVNotations.
Require Import NArith.
Require Import List.
Require Import Lia ZifyN ZifyBool.

Import ListNotations.
Open Scope N_scope.

Section Invariants.
    Variable mem : memory.
    Variable raddr : addr.
    Variable in_a in_b : addr.
    Variable len : N.
    Variable s0 s1 s2 s3 s4 sp : N.

    Definition k_equal (p1 p2 : addr) (k : N) (mem : memory) : Prop :=
        forall (i : N),
            i < k ->
            mem Ⓑ[p1 + i] = mem Ⓑ[p2 + i].

    (* The output of CRYPTO_memcmp is zero if and only if the two
       memory regions match up to `len` bytes *)
    Definition postcondition (s : store)
            (altret : option riscvvar) 
            (altmem : option memory): Prop :=
        s (match altret with None => R_A0 | Some x => x end) = 0 
            <-> 
        k_equal in_a in_b len
          (match altmem with None => mem | Some x => x end).

    Definition ssize : N := 32.

    Definition noverlaps (sp : addr) :=
        ~ overlap 32 in_a len (sp ⊖ ssize) ssize /\
        ~ overlap 32 in_b len (sp ⊖ ssize) ssize.

    Definition stack (s : store) :=
        s V_MEM32 = mem[Ⓓ sp ⊖ 4 :=  raddr]
                       [Ⓓ sp ⊖ 8 :=  s0]
                       [Ⓓ sp ⊖ 12 := s1]
                       [Ⓓ sp ⊖ 16 := s2]
                       [Ⓓ sp ⊖ 20 := s3]
                       [Ⓓ sp ⊖ 24 := s4].

    Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        match a with
        (* CRYPTO_memcmp *)
        | 0x10170 => Inv 0
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
              s V_MEM32 = mem /\
              s R_RA = raddr /\
              s R_S0 = s0 /\ s R_S1 = s1 /\ s R_S2 = s2 /\
                s R_S3 = s3 /\ s R_S4 = s4 /\
             s R_SP = sp /\
             s V_MEM32 = mem)
        | 0x10180 => Inv 0
            (exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              ((s R_A0 = 0) <-> k_equal in_a in_b k mem) /\
              s R_RA = raddr /\
              s R_S0 = s0 /\ s R_S1 = s1 /\ s R_S2 = s2 /\
                s R_S3 = s3 /\ s R_S4 = s4 /\
              s R_SP = sp /\
              s V_MEM32 = mem
            )
        | 0x1019c | 0x101a4 => Post 0 
            (postcondition s None None /\ 
             s R_RA = raddr /\
             s R_S0 = s0 /\ s R_S1 = s1 /\ s R_S2 = s2 /\
                s R_S3 = s3 /\ s R_S4 = s4 /\
             s R_SP = sp /\
             s V_MEM32 = mem)

        (* passwords_match_tmr *)
        | 0x101a8 => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
             s R_S0 = s0 /\ s R_S1 = s1 /\ s R_S2 = s2 /\
             s R_S3 = s3 /\ s R_S4 = s4 /\ s R_SP = sp /\
             s R_RA = raddr /\
              s V_MEM32 = mem /\ noverlaps (s R_SP))
        | 0x10208 => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
             s R_S0 = in_a /\ s R_S1 = in_b /\ s R_S2 = len /\
             postcondition s (Some R_S3) (Some (s V_MEM32)) /\
             noverlaps (s R_SP ⊕ ssize) /\
             stack s)
        | 0x1021c => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\ 
             s R_S0 = in_a /\ s R_S1 = in_b /\ s R_S2 = len /\
             postcondition s (Some R_S4) (Some (s V_MEM32)) /\
             postcondition s (Some R_S3) (Some (s V_MEM32)) /\
             noverlaps (s R_SP ⊕ ssize) /\
             stack s)
        | 0x10220 => Inv 1
            (postcondition s (Some R_S4) (Some (s V_MEM32)) /\
             postcondition s (Some R_S3) (Some (s V_MEM32)) /\
             postcondition s None (Some (s V_MEM32)) /\
             stack s)
        | 0x102b0 | 0x102b4 => Post 1 (
            s R_A0 = 1 <-> k_equal in_a in_b len (s V_MEM32)
        )
        | _ => NoInv
        end.

    Definition tmr_ft : program := lift_riscv tmr_ft.

    Definition exits0 := make_exits 0 tmr_ft invs.
    Definition invs0 := make_invs 0 tmr_ft invs.

    Definition exits1 := make_exits 1 tmr_ft invs.
    Definition invs1 := make_invs 1 tmr_ft invs.
End Invariants.

Lemma k_equal_inv : forall mem a b k,
    k_equal a b (1 + k) mem ->
    k_equal a b k mem.
Proof.
    intros. unfold k_equal in *.
    intros. apply H. lia.
Qed.

Lemma k_equal_step : forall mem a b k,
    k_equal a b k mem ->
    mem Ⓑ[a + k] = mem Ⓑ[b + k] ->
    k_equal a b (1 + k) mem.
Proof.
    intros. unfold k_equal in *.
    intros. assert (i = k \/ i < k) by lia. destruct H2.
        subst. assumption.
    now apply H.
Qed.

Lemma or_xor_zero : forall a b c,
    a .| b .^ c = 0 ->
    a = 0 /\ b = c.
Proof.
    intros.
    replace a with 0 in * by (symmetry; eapply N.lor_eq_0_l, H).
    split. reflexivity.
    psimpl in H.
    now apply N.lxor_eq.
Qed.

(* Proof in fault-free context *)
Theorem crypto_memcmp_correctness:
  forall s mem t xs' in_a in_b len raddr s0 s1 s2 s3 s4 sp
         (ENTRY: startof t xs' = (Addr 0x10170, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (RA: s R_RA = raddr)
         (S0: s R_S0 = s0)
         (S1: s R_S1 = s1)
         (S2: s R_S2 = s2)
         (S3: s R_S3 = s3)
         (S4: s R_S4 = s4)
         (SP: s R_SP = sp),
  satisfies_all tmr_ft (invs0 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (exits0 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (xs'::t).
Proof using.
    Local Ltac step := time r5_step.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. repeat split; assumption.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s5 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & Mem & Saved). {
    step.
    - (* len = 0 *)
        (* apply N.eqb_eq in BC. *)
        repeat step. repeat split; auto; intuition.
            unfold k_equal. lia.
    - (* len <> 0 *)
        repeat step.
        exists 0. psimpl; repeat split; auto; intuition.
        lia. apply (models_var R_A2) in MDL. rewrite <- A2. apply MDL.
        unfold k_equal. lia.
    }

    (* Loop *)
    destruct PRE as (k & Mem & A5 & A1 & A2 & Bound & Eq & Saved). {
    repeat step.
    - (* in_a + k + 1 <> in_a + len, loop *)
        exists (k ⊕ 1). psimpl. repeat split; auto;
            try solve [intuition]. lia.
        -- unfold k_equal. intros.
           apply or_xor_zero in H. destruct H.
           assert (i < k \/ i = k) by lia. destruct H2.
               now apply Eq.
           now subst.
        -- intros. rewrite N.mod_small in H by lia.
           pose proof (k_equal_inv _ _ _ _ H). apply Eq in H0.
           specialize (H k ltac:(lia)).
           now rewrite H, N.lxor_nilpotent, H0.
    - (* in_a + k + 1 = in_a + len, break *)
        assert (1 + k = len) by lia. subst len.
        repeat split; auto; try solve [intuition]; intro.
        -- apply or_xor_zero in H. destruct H. rewrite H in *.
           apply k_equal_step.
              now apply Eq.
              now rewrite H0.
        -- replace (s R_A0) with 0. psimpl.
           apply N.lxor_eq_0_iff.
           symmetry. apply H. lia.
           apply k_equal_inv in H. apply Eq in H.
           now rewrite H.
    }
Qed.

(* Proof in fault-free environment *)
Theorem tmr_ft_correctness:
  forall s mem t xs' in_a in_b len raddr s0 s1 s2 s3 s4 sp
         (ENTRY: startof t xs' = (Addr 0x101a8, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (RA: s R_RA = raddr)
         (S0: s R_S0 = s0)
         (S1: s R_S1 = s1)
         (S2: s R_S2 = s2)
         (S3: s R_S3 = s3)
         (S4: s R_S4 = s4)
         (SP: s R_SP = sp)
         (NVL: noverlaps in_a in_b len sp),
  satisfies_all tmr_ft (invs1 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (exits1 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp) (xs'::t).
Proof.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. rewrite SP.
    repeat (split; auto).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s5 into s. rename a1 into a.

    destruct_inv 32 PRE.

    Ltac riscv_call thm :=
        let MDL1 := fresh "MDL1" in
        let s1 := fresh "s1" in
        set (s1 := update _ _ _);
        eapply models_after_steps;
        [assumption|apply lift_riscv_welltyped|];
        intro MDL1; eapply (perform_call 0);
        [reflexivity|intros;
                     eapply thm; 
                     try reflexivity; eauto|reflexivity|];
        let a := fresh "a" in
        let s' := fresh "s'" in
        let t2 := fresh "t2" in
        intros
            a' s' t2 ENTRY XP UT PRE
        ; unfold s1 in PRE; psimpl in PRE;
        let MDL' := fresh "MDL'" in
        assert (models rvtypctx s') as MDL' by
            (eapply preservation_exec_prog;
             eauto using lift_riscv_welltyped);
        unfold archtyps in *;
        match goal with
        | [|- context[?t2 ++ ?t0 ++ (Addr ?x, ?s) :: ?t]] =>
            let t' := fresh "t'" in
            set (t' := t2++t0++(Addr x, s)::t) in *; clearbody s1;
            let MDL := fresh "MDL" in
            rename MDL' into MDL;
            destruct_inv 32 PRE
        end.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & S3 & S4 & SP & RA & Mem & NVL). {
    do 20 step.

    (* Dummy hyp to make it easier to use the above tactic *)
    eassert (ST: stack mem raddr s0 s1 s2 s3 s4 sp 
        (update s V_MEM32 _)).
        unfold stack; now psimpl.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer1 & RA' & S0' & S1' & S2' & S3' & S4' & SP' & Mem');
        unfold postcondition in Answer1; repeat step;
        repeat (split; [reflexivity|]); split; [
            unfold postcondition; split; intro; [
                apply Answer1 in H; intros a ALen;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite Mem';
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer1; intros a ALen;
                specialize (H a ALen);
                rewrite Mem' in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; split; [unfold noverlaps in *; psimpl; 
            now rewrite SP', <- SP
        |unfold stack; psimpl; now rewrite Mem']).
    }

    (* To second call *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & Answer1 & NVL & ST). {
    step.

    (* Formal goal for riscv_call*)
    match goal with
    | [|- context[?x :: ?y :: ?t]] =>
        change (x :: y :: t) with
            (x :: nil ++ y :: t)
    end.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer2 & RA & S0' & S1' & S2' & S3 & S4 & SP & MEM);
        unfold postcondition in Answer2; repeat step;
        repeat (split; [solve[reflexivity||auto]|]); split; [
            unfold postcondition; split; intro; [
                apply Answer2 in H; intros a ALen;
                rewrite A2 in H;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite MEM;
                rewrite A0, A1 in H;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer2; intros a ALen;
                rewrite A2 in ALen;
                specialize (H a ALen);
                rewrite MEM in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                rewrite A0, A1;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; split; [
          unfold postcondition;
          psimpl; rewrite S3, MEM; apply Answer1
        |]; split; [unfold noverlaps in *; psimpl; 
          psimpl in NVL; now rewrite SP|];
          unfold stack; psimpl; rewrite MEM; apply ST).
    }

    (* To third call *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & Answer1 & Answer2 & NVL & ST). {
    step.

    match goal with
    | [|- context[?x :: ?y :: ?t]] =>
        change (x :: y :: t) with
            (x :: nil ++ y :: t)
    end.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer3 & RA & S0' & S1' & S2' & S3 & S4 & SP & MEM);
        repeat step; unfold postcondition in *; psimpl; split;
        [rewrite S4, MEM; apply Answer1|]; split;
        [rewrite S3, MEM; apply Answer2|]; split; [
            split; intro; [
                apply Answer3 in H; intros a ALen;
                rewrite A2 in H;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite MEM;
                rewrite A0, A1 in H;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer3; intros a ALen;
                rewrite A2 in ALen;
                specialize (H a ALen);
                rewrite MEM in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                rewrite A0, A1;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; unfold stack; psimpl; rewrite MEM; apply ST).
    }

    (* Postcondition *)
    destruct PRE as (Answer1 & Answer2 & Answer3 & ST).
    repeat step. unfold stack in ST. split; intro.
    - unfold postcondition in *.
      destruct (N.eq_dec (s R_S4) 0),
               (N.eq_dec (s R_S3) 0),
               (N.eq_dec (s R_A0) 0);
        ((now apply Answer1) || (now apply Answer2) || (now apply Answer3) || idtac).
      repeat (let E := fresh "E" in
              destruct (N.ltb 0 _) eqn:E in H; [|lia]).
      psimpl in H. discriminate.
    - unfold postcondition in *.
      destruct (N.eq_dec (s R_S4) 0),
               (N.eq_dec (s R_S3) 0),
               (N.eq_dec (s R_A0) 0);
        try rewrite e; try rewrite e0; try rewrite e1; psimpl;
        auto.
      apply Answer2 in H. contradiction.
      apply Answer1 in H. contradiction.
      apply Answer2 in H. contradiction.
      apply Answer1 in H. contradiction.
Qed.

Section FaultTolerantInvariants.
    Variable mem : memory.
    Variable raddr : addr.
    Variable in_a in_b : addr.
    Variable len : N.
    Variable s0 s1 s2 s3 s4 sp : N.

    (* When running CRYPTO_memcmp, there are three distinct possibilities:
        1. s FC = 0, no fault occurs, s' FC = 0
        2. s FC = 1, no fault occurs, s' FC = 1
        3. s FC = 1,  a fault occurs, s' FC = 0

        When running passwords_match_tmr, after each call, these cases must
        each be analyzed. I predict this will hurt automation.
    *)

    (* These values are always preserved because CRYPTO_memcmp
       never touches them *)
    Definition safe_regs (s : store) :=
        s R_RA = raddr /\
        s R_S0 = s0 /\ s R_S1 = s1 /\ s R_S2 = s2 /\
        s R_S3 = s3 /\ s R_S4 = s4 /\
        s R_SP = sp /\
        s V_MEM32 = mem.

    Definition ft_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
        let postcondition := postcondition mem in_a in_b len in
        let noverlaps := noverlaps in_a in_b len in
        let stack := stack mem raddr s0 s1 s2 s3 s4 sp in
        match a with
        (* CRYPTO_memcmp *)
        | 0x10170 => Inv 0
            (s V_FC <= 1 /\
             s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
             safe_regs s)
        | 0x10180 => Inv 0
            (safe_regs s /\
             (* Cases 1, 2 *)
             ((s V_FC <= 1 /\ exists k,
              s V_MEM32 = mem /\
              s R_A5 = in_a ⊕ k /\
              s R_A1 = in_b ⊕ k /\
              s R_A2 = in_a ⊕ len /\
              k < len < 2^32 /\
              ((s R_A0 = 0) <-> k_equal in_a in_b k mem) /\
              safe_regs s) \/
             (* Case 3 *)
              s V_FC = 0)
            )
        | 0x1019c | 0x101a4 => Post 0 
            (safe_regs s /\
             (* Cases 1, 2 *)
             ((s V_FC <= 1 /\ postcondition s None None) \/
             (* Case 3 *)
             s V_FC = 0))

        (* passwords_match_tmr *)
        | 0x101a8 => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
             safe_regs s /\ noverlaps (s R_SP) /\
             s V_FC = 1)
        | 0x101f4 => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
             s R_S0 = in_a /\ s R_S1 = in_b /\ s R_S2 = len /\
             noverlaps (s R_SP ⊕ ssize) /\ stack s /\
             s V_FC <= 1)
        | 0x10208 => Inv 1
            (safe_regs s /\ noverlaps (s R_SP ⊕ ssize) /\
             (* Cases 1, 2 *)
             ((s V_FC <= 1 /\
               s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\
               s R_S0 = in_a /\ s R_S1 = in_b /\ s R_S2 = len /\
               postcondition s (Some R_S3) (Some (s V_MEM32))) \/
               (* Case 3 *)
               s V_FC = 0))
        | 0x1021c => Inv 1
            (s R_A0 = in_a /\ s R_A1 = in_b /\ s R_A2 = len /\ 
             s R_S0 = in_a /\ s R_S1 = in_b /\ s R_S2 = len /\
             postcondition s (Some R_S4) (Some (s V_MEM32)) /\
             postcondition s (Some R_S3) (Some (s V_MEM32)) /\
             noverlaps (s R_SP ⊕ ssize) /\
             stack s)
        | 0x10220 => Inv 1
            (postcondition s (Some R_S4) (Some (s V_MEM32)) /\
             postcondition s (Some R_S3) (Some (s V_MEM32)) /\
             postcondition s None (Some (s V_MEM32)) /\
             stack s)
        | 0x102b0 | 0x102b4 => Post 1 (
            s R_A0 = 1 <-> k_equal in_a in_b len (s V_MEM32)
        )
        | _ => NoInv
        end.

    Definition tmr_fault : program := inject_fault tmr_ft.

    Definition ft_exits0 := make_exits 0 tmr_fault ft_invs.
    Definition ft_invs0 := make_invs 0 tmr_fault ft_invs.

    Definition ft_exits1 := make_exits 1 tmr_fault ft_invs.
    Definition ft_invs1 := make_invs 1 tmr_fault ft_invs.
End FaultTolerantInvariants.

(* Proof in fault-aware context *)
Theorem crypto_memcmp_correctness_ft:
  forall s mem t xs' in_a in_b len raddr s0 s1 s2 s3 s4 sp
         (ENTRY: startof t xs' = (Addr 0x10170, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (RA: s R_RA = raddr)
         (S0: s R_S0 = s0)
         (S1: s R_S1 = s1)
         (S2: s R_S2 = s2)
         (S3: s R_S3 = s3)
         (S4: s R_S4 = s4)
         (SP: s R_SP = sp)
         (FC: s V_FC <= 1),
  satisfies_all tmr_fault 
                       (ft_invs0 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (ft_exits0 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (xs'::t).
Proof using.
    Local Ltac step ::= 
        match goal with
        | [s' : store, FC : ?s' V_FC <= 1 |- _] =>
            let H := fresh "H" in
            assert (s' V_FC = 0 \/ s' V_FC = 1) as H by lia;
            clear FC; destruct H
        | _ => idtac
        end;
        time r5_step;
        repeat match goal with
        | [n : N, BC : ?n mod 2 = _ |- _] => clear BC n
        | [s' : store, n : N, 
            BC : (if 0 <? ?s' V_FC then ?n mod 2 else 0) = _ |- _] => clear BC n
        | [H: ?x = ?x |- _] => clear H
        end;
        try discriminate.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step; repeat split; auto; lia. 

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply inject_fault_lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s5 into s. rename a1 into a.

    destruct_inv 32 PRE.

    (* Intro *)
    destruct PRE as (FC & A0 & A1 & A2 & Safe). {
    Local Ltac solve_inv MDL A2 :=
        exists 0; psimpl; repeat split; auto;
            [lia|
            apply (models_var R_A2) in MDL; rewrite <- A2; apply MDL
            |lia|unfold k_equal; lia].
    step.
    - (* len = 0, fault *)
        repeat step; split;
        [unfold safe_regs in *; now psimpl
        |left; split; [lia|]];
        unfold postcondition; psimpl;
            unfold k_equal; split; lia.
    - (* len <> 0, fault *)
        repeat step; split;
        [unfold safe_regs in *; now psimpl
        |left; split; [lia|]];
        exists 0; psimpl; unfold safe_regs in Safe;
        repeat split; try solve [intuition];
        unfold k_equal; try lia;
        apply (models_var R_A2) in MDL; simpl in MDL; lia.
    - (* no fault *) 
        repeat step;
            (split; 
            [unfold safe_regs in *; now psimpl
            |solve [now right]||left]);
            split; [reflexivity|];
            unfold postcondition; psimpl;
            split; intro; unfold k_equal; lia.
    - (* no fault *) 
        repeat step;
            (split; 
            [unfold safe_regs in *; now psimpl
            |solve [now right]||left]);
            split; [reflexivity|];
            exists 0; psimpl; unfold safe_regs in *;
            repeat split; try solve [intuition];
            unfold k_equal; try lia;
            apply (models_var R_A2) in MDL; simpl in MDL; lia.
    - (* no fault *) 
        repeat step;
            (split; 
            [unfold safe_regs in *; now psimpl
            |solve [now right]||left]).
    }

    (* Loop *)
    destruct PRE as (Safe & [PRE|PRE]).
    destruct PRE as (FC & k & Mem & A5 & A1 & A2 & Bound & Eq). {
    Local Ltac solve_inv' k Eq :=
        let X := fresh "X" in
        let Y := fresh "Y" in
        let Z := fresh "Z" in
        let W := fresh "W" in
        let Inv := fresh "Inv" in
        let i := fresh "i" in
        exists (k ⊕ 1); psimpl; unfold safe_regs in *; psimpl;
        repeat split; try solve [intuition];
        [lia
        |unfold k_equal; intros X i Z; apply or_xor_zero in X; destruct X;
            assert (i < k \/ i = k) as Y by lia; destruct Y;
            [now apply Eq|now subst]
        |repeat split; intros W; rewrite N.mod_small in W by lia;
            pose proof (k_equal_inv _ _ _ _ W) as Inv; apply Eq in Inv;
            specialize (W k ltac:(lia));
            now rewrite W, N.lxor_nilpotent, Inv].
    Local Ltac solve_post k len s Eq :=
        let X := fresh "H" in
        let i := fresh "i" in
        let ILen := fresh "ilen" in
        let KLen := fresh "klen" in
        assert (1 + k = len) as KLen by lia;
        subst len;
        split; intro X;
            [apply k_equal_step;
              apply or_xor_zero in X; destruct X;
              [apply Eq; assumption|now symmetry]
            |replace (s R_A0) with 0; psimpl;
              [apply N.lxor_eq_0_iff; symmetry; apply X; lia
              |apply k_equal_inv in X; symmetry; apply Eq, X]
            ].
    repeat step;
        (split; 
         [unfold safe_regs in *; now psimpl
         |(now right) || (left; split; [lia|])]).
        solve_inv' k Eq.
        solve_post k len s Eq.
    }

    repeat step; (split;
        [unfold safe_regs in *; now psimpl
        |now right]).
Qed.

(* Proof in fault-free environment *)
Theorem tmr_ft_correctness:
  forall s mem t xs' in_a in_b len raddr s0 s1 s2 s3 s4 sp
         (ENTRY: startof t xs' = (Addr 0x101a8, s))
         (MDL: models rvtypctx s)
         (MEM: s V_MEM32 = mem)
         (A0: s R_A0 = in_a)
         (A1: s R_A1 = in_b)
         (LEN: s R_A2 = len)
         (RA: s R_RA = raddr)
         (S0: s R_S0 = s0)
         (S1: s R_S1 = s1)
         (S2: s R_S2 = s2)
         (S3: s R_S3 = s3)
         (S4: s R_S4 = s4)
         (SP: s R_SP = sp)
         (NVL: noverlaps in_a in_b len sp),
  satisfies_all tmr_ft (invs1 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp)
                       (exits1 mem raddr in_a in_b len s0 s1 s2 s3 s4 sp) (xs'::t).
Proof.
    intros. apply prove_invs.

    simpl. rewrite ENTRY. step. rewrite SP.
    repeat (split; auto).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; try (eassumption || apply lift_riscv_welltyped).
    clear - PRE MDL. rename t1 into t. rename s5 into s. rename a1 into a.

    destruct_inv 32 PRE.

    Ltac riscv_call thm :=
        let MDL1 := fresh "MDL1" in
        let s1 := fresh "s1" in
        set (s1 := update _ _ _);
        eapply models_after_steps;
        [assumption|apply lift_riscv_welltyped|];
        intro MDL1; eapply (perform_call 0);
        [reflexivity|intros;
                     eapply thm; 
                     try reflexivity; eauto|reflexivity|];
        let a := fresh "a" in
        let s' := fresh "s'" in
        let t2 := fresh "t2" in
        intros
            a' s' t2 ENTRY XP UT PRE
        ; unfold s1 in PRE; psimpl in PRE;
        let MDL' := fresh "MDL'" in
        assert (models rvtypctx s') as MDL' by
            (eapply preservation_exec_prog;
             eauto using lift_riscv_welltyped);
        unfold archtyps in *;
        match goal with
        | [|- context[?t2 ++ ?t0 ++ (Addr ?x, ?s) :: ?t]] =>
            let t' := fresh "t'" in
            set (t' := t2++t0++(Addr x, s)::t) in *; clearbody s1;
            let MDL := fresh "MDL" in
            rename MDL' into MDL;
            destruct_inv 32 PRE
        end.

    (* Intro *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & S3 & S4 & SP & RA & Mem & NVL). {
    do 20 step.

    (* Dummy hyp to make it easier to use the above tactic *)
    eassert (ST: stack mem raddr s0 s1 s2 s3 s4 sp 
        (update s V_MEM32 _)).
        unfold stack; now psimpl.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer1 & RA' & S0' & S1' & S2' & S3' & S4' & SP' & Mem');
        unfold postcondition in Answer1; repeat step;
        repeat (split; [reflexivity|]); split; [
            unfold postcondition; split; intro; [
                apply Answer1 in H; intros a ALen;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite Mem';
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer1; intros a ALen;
                specialize (H a ALen);
                rewrite Mem' in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; split; [unfold noverlaps in *; psimpl; 
            now rewrite SP', <- SP
        |unfold stack; psimpl; now rewrite Mem']).
    }

    (* To second call *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & Answer1 & NVL & ST). {
    step.

    (* Formal goal for riscv_call*)
    match goal with
    | [|- context[?x :: ?y :: ?t]] =>
        change (x :: y :: t) with
            (x :: nil ++ y :: t)
    end.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer2 & RA & S0' & S1' & S2' & S3 & S4 & SP & MEM);
        unfold postcondition in Answer2; repeat step;
        repeat (split; [solve[reflexivity||auto]|]); split; [
            unfold postcondition; split; intro; [
                apply Answer2 in H; intros a ALen;
                rewrite A2 in H;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite MEM;
                rewrite A0, A1 in H;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer2; intros a ALen;
                rewrite A2 in ALen;
                specialize (H a ALen);
                rewrite MEM in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                rewrite A0, A1;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; split; [
          unfold postcondition;
          psimpl; rewrite S3, MEM; apply Answer1
        |]; split; [unfold noverlaps in *; psimpl; 
          psimpl in NVL; now rewrite SP|];
          unfold stack; psimpl; rewrite MEM; apply ST).
    }

    (* To third call *)
    destruct PRE as (A0 & A1 & A2 & S0 & S1 & S2 & Answer1 & Answer2 & NVL & ST). {
    step.

    match goal with
    | [|- context[?x :: ?y :: ?t]] =>
        change (x :: y :: t) with
            (x :: nil ++ y :: t)
    end.

    (* Call CRYPTO_memcmp *)
    riscv_call crypto_memcmp_correctness;
        (destruct PRE as (Answer3 & RA & S0' & S1' & S2' & S3 & S4 & SP & MEM);
        repeat step; unfold postcondition in *; psimpl; split;
        [rewrite S4, MEM; apply Answer1|]; split;
        [rewrite S3, MEM; apply Answer2|]; split; [
            split; intro; [
                apply Answer3 in H; intros a ALen;
                rewrite A2 in H;
                specialize (H a ALen);
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL]);
                rewrite MEM;
                rewrite A0, A1 in H;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])
            | psimpl; apply Answer3; intros a ALen;
                rewrite A2 in ALen;
                specialize (H a ALen);
                rewrite MEM in H;
                repeat (rewrite getmem_noverlap in H; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL
                ]);
                rewrite A0, A1;
                now repeat (rewrite getmem_noverlap; [|
                    ((apply (noverlap_shrink _ in_a len);
                        [psimpl; lia|]) ||
                    (apply (noverlap_shrink _ in_b len);
                        [psimpl; lia|]));
                    apply noverlap_symmetry,
                        (noverlap_shrink _ (s5 R_SP ⊖ 32) 32);
                        [psimpl; lia|];
                    apply noverlap_symmetry; now destruct NVL])]
        |]; unfold stack; psimpl; rewrite MEM; apply ST).
    }

    (* Postcondition *)
    destruct PRE as (Answer1 & Answer2 & Answer3 & ST).
    repeat step. unfold stack in ST. split; intro.
    - unfold postcondition in *.
      destruct (N.eq_dec (s R_S4) 0),
               (N.eq_dec (s R_S3) 0),
               (N.eq_dec (s R_A0) 0);
        ((now apply Answer1) || (now apply Answer2) || (now apply Answer3) || idtac).
      repeat (let E := fresh "E" in
              destruct (N.ltb 0 _) eqn:E in H; [|lia]).
      psimpl in H. discriminate.
    - unfold postcondition in *.
      destruct (N.eq_dec (s R_S4) 0),
               (N.eq_dec (s R_S3) 0),
               (N.eq_dec (s R_A0) 0);
        try rewrite e; try rewrite e0; try rewrite e1; psimpl;
        auto.
      apply Answer2 in H. contradiction.
      apply Answer1 in H. contradiction.
      apply Answer2 in H. contradiction.
      apply Answer1 in H. contradiction.
Qed.
