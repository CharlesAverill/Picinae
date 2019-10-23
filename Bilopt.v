Require Import Picinae_core.
Require Import Index.
Require Import NArith.

Module Type bilopt (ARCH : Architecture) (PIC : PICINAE_CORE ARCH).
  Import PIC.

  Definition explicate_fallthroughs (prog : program) st n : option stmt :=
    match prog st n with
    | None => None
    | Some (size,stmt) => Some (Seq stmt (Jmp (Word (n+size) (2^(n+size)))))
    end.

  Definition exp_fallthrough_sz (prog : program) altsz : program :=
    fun st n =>
      option_map (pair (altsz st n)) (explicate_fallthroughs prog st n).

  Theorem exp_fallthrough_szirrel prog altsz altsz' :
    forall h a s n s' e,
    exec_prog h (exp_fallthrough_sz prog altsz) a s n s' e
    -> exec_prog h (exp_fallthrough_sz prog altsz') a s n s' e.
    intros h a s n.
    generalize dependent s.
    generalize dependent a.
    generalize dependent h.
    unfold exp_fallthrough_sz,explicate_fallthroughs.
    induction n; intros h a s s' e H.
    {
      inversion H.
      constructor.
    }
    {
      inversion H; subst.
      {
        destruct prog eqn:HP; [|discriminate].
        destruct p.
        simpl in *.
        inversion LU; subst.
        destruct x1; simpl in *; subst; [|inversion XS;inversion XS0].
        econstructor; try eassumption + reflexivity; auto.
        rewrite HP.
        simpl.
        reflexivity.
      }
      {
        destruct prog eqn:HP; [|discriminate].
        destruct p.
        inversion LU; subst.
        inversion XS; subst; [|inversion XS0].
        eapply XAbort; [rewrite HP;reflexivity|].
        constructor.
        assumption.
      }
    }
  Qed.

  Theorem exp_fall_exp'' (prog : program) altsz h a s n s' e :
    exec_prog h prog a s n s' e
    -> exec_prog h (exp_fallthrough_sz prog altsz) a s n s' e.
    pose (f := fun st n =>
                 match prog st n with None => 0 | Some (sz,_) => sz end).
    intro H.
    eapply (exp_fallthrough_szirrel _ f).
    unfold f.
    clear f altsz.
    generalize dependent e.
    generalize dependent s'.
    generalize dependent s.
    generalize dependent a.
    generalize dependent h.
    induction n; intros h a s s' e H; [inversion H; constructor|].
    inversion H; subst.
    {
      Check XStep.
      eapply (XStep _ _ _ _ _ _ _ _ (Some (exitof (a + sz) x1))).
      {
        unfold exp_fallthrough_sz,explicate_fallthroughs.
        rewrite LU.
        reflexivity.
      }
      {
        destruct x1; simpl in *; subst; [|inversion EX]; [econstructor; eauto|].
        {
          eapply XSeq2; eauto.
          repeat econstructor.
        }
      }
      { rewrite EX; reflexivity. }
      { apply IHn,XP. }
    }
    {
      eapply XAbort.
      {
        unfold exp_fallthrough_sz,explicate_fallthroughs.
        rewrite LU.
        reflexivity.
      }
      {
        constructor.
        assumption.
      }
    }
  Qed.

  Theorem exp_fall_exp' (prog : program) altsz h a s n s' e :
    exec_prog h (exp_fallthrough_sz prog altsz) a s n s' e
    -> exec_prog h prog a s n s' e.
    generalize dependent e.
    generalize dependent s'.
    generalize dependent s.
    generalize dependent a.
    generalize dependent h.
    induction n; intros; [inversion H;constructor|].
    inversion H; subst.
    {
      unfold exp_fallthrough_sz,explicate_fallthroughs in LU.
      destruct prog eqn:HP; [|discriminate].
      destruct p.
      simpl in *.
      inversion LU; subst.
      inversion XS; subst.
      {
        econstructor; eauto.
      }
      {
        inversion XS0; subst.
        inversion E; subst.
        econstructor; eauto.
      }
    }
    {
      unfold exp_fallthrough_sz,explicate_fallthroughs in LU.
      destruct prog eqn:HP; [|discriminate].
      destruct p.
      inversion LU; subst.
      inversion XS; subst; [|inversion XS0].
      eapply XAbort; eauto.
    }
  Qed.

  Theorem exp_fall_exp (prog : program) altsz h a s n s' e :
    exec_prog h (exp_fallthrough_sz prog altsz) a s n s' e
    <-> exec_prog h prog a s n s' e.
    split; [apply exp_fall_exp'|apply exp_fall_exp''].
  Qed.

  (* option (N * stmt) is going to refer to absolute location here *)
  (* anything else is messy *)

  Definition jmp_const n : stmt :=
    Jmp (Word n (2^n)).

  (* Definition jmp_seq n s := Seq s ( *)
  (* Definition jmp_seq (ns : option (N * stmt)) : option stmt := *)
  (*   match ns with *)
  (*   | Some (n,s) => Some (Seq s (jmp_const n)) *)
  (*   | None => None *)
  (*   end. *)

  Fixpoint jmp_join_stmt (s : stmt) (breaks : N -> bool)
    : list N * (Index N (option (N * stmt)) -> option stmt) :=
    match s with
    | Jmp (Word n _) =>
      if breaks n
      then
        (nil, fun _ => Some s)
      else
        (cons n nil,
         fun i => match indexget i n with
                  | Some (Some (n',s)) => Some (Seq s (jmp_const (n'+n)))
                  | Some None | None => None
                  end)
    | If exp bt be =>
      let ot := jmp_join_stmt bt breaks in
      let oe := jmp_join_stmt be breaks in
      (app (fst ot) (fst oe),
       (fun i =>
          match snd ot i,snd oe i with
          | Some bt',Some et' => Some (If exp bt' et')
          | _,_ => None
          end))
    | Seq a b =>
      let oa := jmp_join_stmt a breaks in
      let ob := jmp_join_stmt b breaks in
      (app (fst oa) (fst ob),
       (fun i =>
          match snd oa i,snd ob i with
          | Some a',Some b' => Some (Seq a' b')
          | _,_ => None
          end))
    | Nop | Move _ _ | Jmp _ | Exn _ | Rep _ _ => (nil, fun _ => Some s)
    end.

  Definition jmp_join_prog_stmt (s : stmt) (loc n : N) (breaks : N -> bool)
    : list N * (Index N (option (N * stmt)) -> option (N * stmt)) :=
    let endloc := loc+n in
    match jmp_join_stmt s breaks, breaks endloc with
    | (l,f),true =>
      (l,fun i => option_map (pair n) (f i))
    | (l,f),false =>
      (cons endloc l,
       fun i =>
         match f i,indexget i endloc with
         | None,_ | _,None | _,Some None => None
         | Some s,(Some (Some (n',ends))) =>
           Some (n'+n,Seq s ends)
         end)
    end.

  Print exec_prog.
  Print program.

  Definition jmp_join_index_prog (i : Index N (option (N * stmt))) : program :=
    fun _ n =>
      match indexget i n with
      | Some (Some x) => Some x
      | Some None | None => None
      end.

  Print exec_prog.

  Definition jmp_join_contracts (p1 p2 : program) :=
    forall h loc st st' e,
      exec_prog h p1 loc st 1 st' e
      -> exists steps', exec_prog h p2 loc st steps' st' e.

  Definition static_prog2prog (p : N -> option (N * stmt)) : program :=
    fun _ => p.

  Definition jmp_join_force_add
             (prog : N -> option (N * stmt))
             (breaks : N -> bool)
             (i : Index N (option (N * stmt)))
             (loc : N) :=
    match prog loc with
    | None =>
      i
    | Some (n,s) =>
      indexsetopt i loc (Some (snd (jmp_join_prog_stmt s loc n breaks) i))
    end.

  Theorem jmp_join_stmt_contract
          (prog : N -> option (N * stmt))
          (s s' : stmt) (loc n n' : N) (breaks : N -> bool)
          (i : Index N (option (N * stmt)))
          h st st' e
    : prog loc = Some (n,s)
      -> snd (jmp_join_prog_stmt s loc n breaks) i = Some (n',s')
      -> jmp_join_contracts (jmp_join_index_prog i) (static_prog2prog prog)
      -> exec_stmt h st s' st' e
      -> exists steps,
          exec_prog h (static_prog2prog prog) loc st steps st' (exitof (n'+loc) e).
    intros HP HS HC HE.
    unfold jmp_join_prog_stmt in *.
    destruct jmp_join_stmt eqn:EJ.
    assert (o = (snd (jmp_join_stmt s breaks))) by (rewrite EJ; auto).
    clear EJ.
    Print exec_stmt.
    Print eval_exp.
    (* assert (forall h st ex, exists v, eval_exp h st ex v). *)
    (* { *)
    (*   intros. *)
    (*   generalize dependent st0. *)
    (*   induction ex; try (repeat econstructor; fail). *)
    (*     exists (VaN 0 w). *)
    (*     apply EUnknown. *)
    (*     destruct w; reflexivity. *)
    (*     econstructor. *)
    (*   } *)
    (*     auto. *)
    (*     apply EUnknown. *)
    (*     econstructor. *)
    (*     econstructor. *)
    (*     apply EUnknown. *)
    (*     econstructor. *)
    (*   induction ex; intros; do 2 econstructor; eauto. *)
    (*   3: { *)
    assert (HI : exists st1 e1, exec_stmt h st s st1 e1).
    {
      clear dependent prog.
      subst.
      simpl in *.
      destruct breaks; simpl in *; clear l.
      {
        destruct (snd _ i) eqn:HP; [|discriminate].
        simpl in *.
        inversion HS; subst.
        clear HS.
        generalize dependent s'.
        generalize dependent st'.
        generalize dependent st.
        generalize dependent e.
        induction s; intros exit st st' s' HP HE;
          inversion HP; subst; simpl in *; eauto.
        {
          destruct e; inversion HP; subst; eauto.
          repeat econstructor.
        }
        {
          destruct (snd (_ s1 _) i) eqn:EJ1; [|discriminate].
          destruct (snd (_ s2 _) i) eqn:EJ2; [|discriminate].
          inversion HP; subst.
          inversion HE; subst.
          {
            edestruct IHs1 as [? [? ?]]; [reflexivity| |]; eauto.
            destruct x1; [do 2 econstructor; eapply XSeq1; eauto|].
            edestruct IHs1 as [? [? ?]]; [reflexivity| |]; eauto.
            
            eapply XSeq2.
          apply HE.
          edestruct IHs1 as [? [? ?]]; eauto;
            [repeat destruct (jmp_join_stmt _ _); destruct o|].
          destruct (snd (_ s1 _) i) eqn:EJ1; destruct (snd (_ s2 _) i) eqn:EJ2;
            inversion HP; subst.
          inversion HE; subst.
          {
            edestruct IHs1 as [? [? ?]]; eauto.
            destruct x1; [do 2 econstructor;apply XSeq1;eauto|].
            do 2 econstructor.
            eapply XSeq1.
            eauto.
            edestruct IHs2 as [? [? ?]]; eauto.
            2: { do 2 econstructor. eapply XSeq2; eauto. }
            do 2 econstructor;eapply XSeq2;eauto.
            apply False_rect.
            clear IHs1 IHs2.
            clear dependent s0.
            generalize dependent s.
            generalize dependent st'.
            generalize dependent st.
            induction s1; intros; inversion EJ1; subst;
              try (inversion XS; fail); try (inversion H; fail).
            {
              simpl in *.
              repeat destruct (snd _ i); try discriminate.
              inversion H; subst.
              inversion EJ1; subst.
              inversion XS; subst; [eapply IHs1_1;eauto|].
              inversion EJ1; subst.
              inversion XS.
            }
            induction s1; simpl in *; inversion EJ1; subst;
              inversion XS; inversion H; subst; auto.
            false.
            clear IHs1 IHs2
            do 2 econstructor.
            apply XSeq1.
            
          specialize (IHs1 s eq_refl).
          specialize (IHs2 s0 eq_refl).
          inversio
          inversion HE; do 2 econstructor; [eapply XSeq1|eapply XSeq2].
          inversion HP; subst.
          destruct jmp_join_stmt eqn:EJ.
          econstructor; econstructor; eauto.
          destruct e0; simpl in *; inversion HP; subst; eauto.
          destruct breaks; simpl in *; [inversion HP; subst; eauto|].
          destruct indexget as [[[? ?]|]|]; [|discriminate|discriminate].
          inversion HP; subst.
          inversion HE; subst.
          {
            
          destruct indexget.
          invers
      clear dependent o.
      clear dependent e.
      induction s; try (repeat econstructor; eauto; fail).
      {
      induction s; do 3 econstructor; eauto.
      3: { eauto.
      clear dependent prog.
      destruct breaks; simpl in *; clear l; subst; destruct (snd _ i);
        try discriminate.
      2: {
        destruct indexget as [[[? ?]|]|]; [|discriminate|discriminate].
        inversion HS; subst.
        clear HS.
        
        destruct o; [|
      {
        destruct o eqn:EO.
        rewrite H in *.
        clear dependent o.
        
        simpl in *.
        inversion HS; subst.
        clear HS.
      fold o in HS.
      destruct jmp_join_stmt eqn:HG.
      destruct breaks.
      destruct jmp_join_stmt; simpl in *.
      simpl in *.
      {
        inversion HE; subst.
      clear dependent prog.
      clear l.
      generalize dependent l.
      generalize dependent e.
      generalize dependent st'.
      generalize dependent st.
      induction s; destruct breaks; intros; simpl.
      clear s.
      destruct breaks; simpl in *; clear l.
    }
    destruct breaks; simpl in *; clear l.
    destruct e as [[e|e]|]; simpl.
    {
      destruct breaks.
    destruct breaks.
    {
      
    generalize dependent o.
    generalize dependent l.
    clear HP.
    destruct e.
    2: {
      simpl.
    induction HE; simpl.
    unfold jmp_join_contracts,jmp_join_force_add,jmp_join_index_prog.
    intros HG ? loc' ? ? ? HE.
    exists 1%nat.
    destruct (prog loc) as [[n s]|]; auto.
    destruct (indexeq i loc' loc); subst.
    {
      inversion HE; subst.
      {
        eapply XStep; eauto.
      rewrite indexsetoptget in HE.
      destruct (prog loc) as [[n s]|].
      unfold jmp_join_force_add in *.
    inversion HE; subst; [|econstructor; eauto].

  Theorem jmp_join_add
          (prog : N -> option (N * stmt))
          (loc : N) (breaks : N -> bool)
          (* (s : stmt) (loc n : N) (breaks : N -> bool) *)
          (i : Index N (option (N * stmt)))
    : (* prog loc = Some (n,s) *)
      jmp_join_contracts (jmp_join_index_prog i) (static_prog2prog prog)
      -> jmp_join_contracts
           (jmp_join_index_prog (jmp_join_force_add prog breaks i loc))
              (* (indexsetopt i loc *)
              (*              (Some (snd (jmp_join_prog_stmt s loc n breaks) i))) *)
           (static_prog2prog prog).
    unfold jmp_join_contracts.
    intros H ? ? ? ? ? HE.
    assert (H' : forall h loc' st st' e,
               loc <> loc' ->
               exec_prog h (jmp_join_index_prog i) loc st 1 st' e ->
               exists steps' : nat, exec_prog h (static_prog2prog prog) loc st steps' st' e).
    unfold jmp_join_contracts,jmp_join_index_prog.
    destruct (indexeq i loc0 loc); subst.
    {
      inversion HE; subst; simpl in *.
      {
        inversion XP; subst.
        destruct x1; simpl in *; subst.
        2: { inversion EX; subst; clear EX.
        apply H.
      induction s; simpl in *.
      {
        inversion HE; subst.
        destruct breaks.
        {
          inversion HE; simpl in *; subst.
          simpl in *.
        rewrite indexsetoptget in *.
    }
    {
      apply H.
      unfold jmp_join_index_prog in *.
      inversion HE; subst; rewrite indexsetoptirrel in LU; auto;
        [|eapply XAbort;eassumption].
      inversion XP.
      subst.
      eapply XStep; eauto.
      constructor.
    }
      eapply XStep; eauto.
      {
        rewrite indexsetoptirrel in LU; auto.
        eapply XStep; eauto.
        inversion XP.
        constructor.
      }
      {
        rewrite indexsetoptirrel in LU; auto.
        eapply XAbort; eassumption.
      }
      [eapply XStep|eapply XAbort]; eauto.
      {
        econstructor.
      destruct HE; econstructor; eauto.
      destruct HE; [constructor| |].
      let iprog : program := jmp_join_index_prog i in
      fun _ n =>
        match indexget i n with
        | Some (Some x) => x
        | _ => None
        end
          (forall loc',
              exec_prog h iprog loc' st 1 st'
              -> exists steps', exec_prog h prog' loc st steps' st')
        -> exec_prog h iprog loc st 1 st'
        -> exists steps, exec_prog h prog' loc st steps st'.
  (* Definition jmp_join_step *)
  (*            (prog : N -> option (N * stmt)) (breaks : N -> bool) *)
  (*            (i : Index N (option (N * stmt))) (n : N) *)
  (*   : (list N option (Index N (option (N * stmt))) := *)
  (*   match indexget i n with *)
  (*     | None =>  *)

  Definition stmt_equiv s1 s2 :=
    forall h st st' e, exec_stmt h st s1 st' e <-> exec_stmt h st s2 st' e.

  Theorem jmp_join_eq (prog : N -> stmt) n h st st' e breaks i :
    (forall n s, indexget i n = Some (Some s) -> stmt_equiv s (prog n))
      -> stmt_equiv (prog n) (
    exec_stmt h st (prog n) st' e
  -> exec_stmt h st (breaks).

  Fixpoint inv_seq'
           (prog : N -> stmt) (breaks : N -> bool)
           (steps : N) (curr : N)
           (index : Index N (option stmt))
    : option (Index N (option stmt)) :=
    match indexget index curr with
    | Some (Some _) => Some index
    | Some None => None
    | None =>
      let index' := indexsetopt index curr None in
      
    end.
End bilopt.
