Require Import Picinae_core.
Require Import NArith.
Require Import List.
Require Export FunctionalExtensionality.
Require Export Lia.
Open Scope list_scope.

Tactic Notation "specialize" hyp(H) "by" tactic(tac) := 
    let P' := fresh "P" in 
    match type of H with
    | ?P -> ?Q => assert P as P' by tac; specialize (H P'); clear P'
    end.

Module Type Timing.
    Parameter store : Type.
    Parameter stmt : Type.
    Parameter empty_store : store.
End Timing.

Module Type TimingProgram (T : Timing).
    Export T.
    Parameter time_of_addr : store -> addr -> N.
End TimingProgram.

Module MakeTimingContents (T : Timing) (TP : TimingProgram T).
    Export T.
    Export TP.
    
    Definition size_stmt : Type := N * stmt.

    Definition program : Type :=
        store -> addr -> option size_stmt.

    Definition timed_program : Type :=
        store -> addr -> option (nat * size_stmt).

    Definition program_bounded {X : Type} (p : store -> addr -> option X) (a : addr) :=
        forall store a', a < a' -> p store a' = None.

    Definition store_invariance {X : Type} (p : store -> addr -> option X) :=
        forall a s s', p s a = p s' a.

    Definition program_well_formed (p : program) (max : addr) :=
        program_bounded p max /\ store_invariance p.

    Definition timed_program_well_formed (p : timed_program) (max : addr) :=
        program_bounded p max /\ (
            forall a s, a <= max -> p s a = None \/ exists instr, p s a = Some (N.to_nat (time_of_addr s a), instr)
        ) /\ store_invariance p.

    Definition program_list : Type :=
        list (addr * option (size_stmt)).

    Fixpoint max_addr_in_program_list (p : program_list) (default : addr) : addr :=
        match p with
        | nil => default
        | (a, i) :: t => max_addr_in_program_list t (N.max a default)
        end.

    Fixpoint list_of_program (p : program) s (max_addr : nat) : program_list :=
        match max_addr with 
        | O => (0, p s 0) :: nil
        | S n' => (N.of_nat max_addr, p s (N.of_nat max_addr)) :: 
            (list_of_program p s n')
        end.

    Definition update_prog (old_prog : program) (a : addr) (newval : option (size_stmt)) : program :=
        fun s a' => if N.eqb a a' then newval else old_prog s a'.

    Definition update_timed_prog (old_prog : timed_program) (a : addr) (newval : option (nat * size_stmt)) : timed_program :=
        fun s a' => if N.eqb a a' then newval else old_prog s a'.

    Fixpoint program_of_list (l : program_list) : program :=
        match l with 
        | nil => fun _ _ => None    
        | h :: t => update_prog (program_of_list t) (fst h) (snd h)
        end.

    Fixpoint list_of_timed_program (p : timed_program) s (max_addr : nat) : program_list :=
        match max_addr with 
        | O => match p s 0 with Some (time, ins) => (0, Some ins) :: nil | None => nil end
        | S n' => match p s (N.of_nat max_addr) with Some (time, ins) => 
            (N.of_nat max_addr, Some ins) :: (list_of_timed_program p s n')
            | None => list_of_timed_program p s n'
            end
        end.

    Fixpoint timed_program_of_list (l : program_list) : timed_program :=
        match l with
        | nil => fun _ _ => None
        | (ad, ins) :: t => match ins with Some s =>
            update_timed_prog (timed_program_of_list t) ad (Some (N.to_nat (time_of_addr empty_store ad), s))
            | None => timed_program_of_list t
            end
        end.

    Definition timed_program_of_program p s (max_addr : N) : timed_program :=
        let instrs := list_of_program p s (N.to_nat max_addr) in 
        let fix helper (l : list (N * option (size_stmt))) : timed_program :=
        match l with 
        | nil => fun _ _ => None
        | (ad, ins) :: t => match ins with Some s =>
            update_timed_prog (helper t) ad (Some (N.to_nat (time_of_addr empty_store ad), s))
            | None => helper t end
        end in helper instrs.

    Definition program_of_timed_program p s (max_addr : N) : program :=
        let instrs := list_of_timed_program p s (N.to_nat max_addr) in 
        let fix helper (l : list (N * option (size_stmt))) : program :=
        match l with
        | nil => fun _ _ => None
        | (ad, ins) :: t => update_prog (helper t) ad ins
        end in helper instrs.

    Definition timed_conversion_safe (p : program) (bound : N) :=
        forall (s : store),
            program_of_timed_program (timed_program_of_program p s bound) s bound = p.

    (* Insert at index pos, or append if pos > len l *)
    Fixpoint insert {X : Type} (l : list X) (item : X) (pos : nat) : list X :=
        match pos with
        | O => item :: l
        | S pos' => match l with 
            | nil => item :: nil
            | h :: t => h :: (insert t item pos')
            end
        end.

    Definition insert_instr (p : program) (max_addr : nat) (st : store) (s : option (size_stmt)) (pos : N) : program :=
        program_of_list (insert (list_of_program p st max_addr) (pos, s) (N.to_nat pos)).

    Definition insert_instr_into_timed (p : timed_program) (max_addr : N) (st : store) (s : option (size_stmt)) (pos : N) : timed_program :=
        let p' := program_of_timed_program p st max_addr in
        timed_program_of_program (insert_instr p' (N.to_nat max_addr) st s pos) st max_addr.

    Definition insert_timed_instr (p : timed_program) (max_addr : N) (st : store) (s : option (nat * size_stmt)) (pos : N) : timed_program :=
        match s with None => p | Some s => insert_instr_into_timed p max_addr st (Some (snd s)) pos end.

    Lemma update_noverlap : forall p a n1 n2,
        update_prog (update_prog p a n1) a n2 = update_prog p a n2.
    Proof.
        intros. apply functional_extensionality. intro s.
        apply functional_extensionality. intro a'. unfold update_prog. destruct (a =? a'); reflexivity.
    Qed.

    Lemma program_access_exceeds_bounds : forall {X : Type} p s a max,
        @program_bounded X p (N.of_nat max) ->
        (N.of_nat max < a) -> p s a = None.
    Proof. intros. apply (H s _ H0). Qed.

    Lemma list_of_timed_program_preserves_bound : forall max p s,
        Forall (fun item => fst item <= N.of_nat max) (list_of_timed_program p s max).
    Proof.
        induction max; intros; simpl; destruct (p s _); try (destruct p0; apply Forall_cons; simpl; try lia);
            try apply Forall_nil; replace (N.pos _) with (N.succ (N.of_nat max)) by lia;
            (eapply Forall_impl; cycle 1; [apply IHmax|idtac]); intros; simpl in H; lia.
    Qed.

    Lemma list_of_program_preserves_bound : forall max p s,
        Forall (fun item => fst item <= N.of_nat max) (list_of_program p s max).
    Proof.
        induction max; intros; simpl.
        - apply Forall_cons. simpl. lia. apply Forall_nil.
        - replace (N.pos _) with (N.succ (N.of_nat max)) by lia. apply Forall_cons.
            simpl. lia.
            eapply Forall_impl; cycle 1; [apply IHmax|idtac]; intros; simpl in H; lia.
    Qed.

    Lemma max_addr_in_plist_default_min : forall l a,
        a <= max_addr_in_program_list l a.
    Proof.
        induction l; intros; simpl.
        - lia.
        - destruct a. destruct (N.le_ge_cases a a0).
            -- rewrite N.max_r; auto.
            -- rewrite N.max_l. apply N.le_trans with a; auto. assumption.
    Qed.

    Lemma max_addr_in_plist_le_trans : forall l a b,
        a <= b -> max_addr_in_program_list l a <= max_addr_in_program_list l b.
    Proof.
        induction l; intros; simpl. assumption.
        destruct a. apply IHl. destruct (N.le_ge_cases a a0).
        - rewrite N.max_r by assumption.
            pose proof (N.le_trans _ _ _ H0 H).
            rewrite N.max_r by lia.
            assumption.
        - rewrite N.max_l by assumption.
            destruct (N.le_ge_cases a b).
            -- rewrite N.max_r; assumption.
            -- rewrite N.max_l; lia.
    Qed.

    Lemma program_of_list_preserves_bound : forall l,
        program_bounded (program_of_list l) (max_addr_in_program_list l 0).
    Proof.
        induction l; simpl; intros s a' Bound.
        - reflexivity.
        - destruct a. rewrite N.max_0_r in Bound. simpl in *. unfold update_prog.
            pose proof (max_addr_in_plist_default_min l a).
            pose proof (N.le_lt_trans _ _ _ H Bound).
            pose proof (N.lt_neq _ _ H0). apply N.eqb_neq in H1.
            rewrite H1. apply (IHl s a').
            apply N.le_lt_trans with (max_addr_in_program_list l a); auto.
            apply max_addr_in_plist_le_trans. lia.
    Qed.

    Lemma timed_program_of_program_share_bound : forall p s max,
        program_bounded p max ->
        program_bounded (timed_program_of_program p s max) max.
    Proof.
        intros p s max H s' a bound. pose proof (list_of_program_preserves_bound (N.to_nat max) p s).
        unfold timed_program_of_program.
        induction (list_of_program p s (N.to_nat max)) as [| [ad ins] l IHl].
        - reflexivity.
        - destruct ins. unfold update_timed_prog at 1. rewrite IHl; inversion H0; subst.
            -- simpl in H3. rewrite N2Nat.id in H3.
                pose proof (N.le_lt_trans _ _ _ H3 bound).
                pose proof (N.lt_neq _ _ H1). apply N.eqb_neq in H2. rewrite H2. reflexivity.
            -- apply H4.
            -- apply IHl. inversion H0. apply H4.
    Qed.  

    Lemma program_of_timed_program_share_bound : forall p s max,
        program_bounded p max ->
        program_bounded (program_of_timed_program p s max) max.
    Proof.
        intros p s max H s' a bound. pose proof (list_of_timed_program_preserves_bound (N.to_nat max) p s).
        unfold program_of_timed_program.
        induction (list_of_timed_program p s (N.to_nat max)) as [| [ad ins] l IHl].
        - reflexivity.
        - unfold update_prog at 1. rewrite IHl; inversion H0; subst.
            -- simpl in H3. rewrite N2Nat.id in H3.
                pose proof (N.le_lt_trans _ _ _ H3 bound).
                pose proof (N.lt_neq _ _ H1). apply N.eqb_neq in H2. rewrite H2. reflexivity.
            -- apply H4.
    Qed.

    (* Lemma timed_untimed_convert : forall max p s,
        timed_program_well_formed p max ->
        timed_program_of_program (program_of_timed_program p s max) s max = p.
    Proof.
        intros. induction max; simpl in *.
        - destruct H as [Bound [Format StoreInv]]. 
            pose proof (program_of_timed_program_share_bound p s 0 Bound).
            pose proof (timed_program_of_program_share_bound (program_of_timed_program p s 0) s 0 H).
            simpl in H, H0.
            apply functional_extensionality. intro s'.
            apply functional_extensionality. intro a.
            destruct (N.eq_0_gt_0_cases a).
            -- subst. unfold program_of_timed_program, list_of_timed_program.
                destruct (p s 0) eqn:E.
                + destruct p0. unfold timed_program_of_program, list_of_program.
                    unfold update_timed_prog, update_prog. simpl.
                    specialize (Format 0 s'). specialize Format by lia.
                    rewrite (StoreInv 0 s s') in *.
                    destruct Format. 
                        rewrite E in H1; inversion H1.
                        destruct H1. rewrite H1 in E. inversion E; subst.
                        now rewrite H1.
                + rewrite (StoreInv 0 s s') in *. rewrite E.
                    unfold timed_program_of_program, list_of_program. simpl.
    Abort. *)

    Lemma program_list_conversion_safe : forall max p s,
        program_well_formed p (N.of_nat max) ->
        program_of_list (list_of_program p s max) = p.
    Proof.
        intros. destruct H as [Bound StoreInv].
        induction max; intros; simpl in *.
        - unfold update_prog. 
            apply functional_extensionality. intro s'.
            apply functional_extensionality. intro a.
            destruct (0 =? a) eqn:E. apply N.eqb_eq in E. subst. apply StoreInv.
            specialize (Bound s' a). apply N.eqb_neq in E. specialize Bound by lia.
            now rewrite Bound.
        - replace (N.pos _) with (N.succ (N.of_nat max)) by lia. unfold update_prog.
            apply functional_extensionality. intro s'.
            apply functional_extensionality. intro a.
            destruct (N.succ _ =? a) eqn:E. apply N.eqb_eq in E. subst. apply StoreInv.
            rewrite IHmax. reflexivity.
    Abort.

    Ltac prog_eq_helper max Hbounded :=
        let Hmax_le := fresh "H" in
        match goal with
        [s : store, a : addr |- 
            program_of_timed_program 
                (timed_program_of_program ?prog ?empty_store ?n)
            ?empty_store ?n ?s ?a = ?prog ?s ?a
        ] => 
            do 37 (destruct a as [| a _] using N.peano_ind; [reflexivity|idtac]);
            repeat rewrite <- N.add_1_r;
            repeat (rewrite <- N.add_assoc; simpl (1 + _));
            let s' := fresh "s" in 
            let a' := fresh "a" in
            assert (forall s' a', 37 <= a' -> prog s' a' = None) as Hmax_le
                by (intros; apply (Hbounded s' a'); lia);
            rewrite Hmax_le; [idtac|lia]; clear Hmax_le;
            apply program_of_timed_program_share_bound; [idtac|lia];
            apply timed_program_of_program_share_bound, Hbounded
        end.

    Ltac prove_bounded :=
        let p := fresh "p" in
        let a := fresh "a" in
        let s := fresh "s" in
        match goal with
        [|- program_bounded ?prog ?bound] =>
            try unfold bound;
            intros s a; intros;
            destruct a as [| p]; [lia|idtac];
            repeat (destruct p; auto); lia
        end.

End MakeTimingContents.
