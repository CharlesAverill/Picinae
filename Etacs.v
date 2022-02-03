Tactic Notation "unsimpl" uconstr(exp) :=
  let tmp := fresh in
  epose proof (tmp := eq_refl exp); simpl in tmp;
  lazymatch type of tmp with
  | ?exp' = _ =>
      clear tmp; eassert (tmp: exp' = exp); [reflexivity|rewrite tmp in *];
          clear tmp
  end.

Ltac revert_all :=
  repeat match goal with
         | H: _ |- _ => revert H
         end.

Ltac einst0 H tac :=
  (lazymatch type of H with
   | ?t1 -> ?t2 =>
       let H0 := fresh in
       assert (H0: t1); [clear H|specialize (H H0); clear H0; einst0 H tac]
   | forall v, @?F v => epose proof (H ?[?v]) as H; einst0 H tac
   | _ => tac H
   end).

Ltac trivial2 := try solve [eassumption|discriminate|reflexivity].

Ltac einversion0 H has_intros has_trivial intros_patt :=
  let Htmp := fresh in
  pose proof H as Htmp; einst0 Htmp ltac:(fun H' =>
    lazymatch has_intros with
    | true => inversion H' as intros_patt; clear H'
    | false => inversion H'; clear H'
    end);
  lazymatch has_trivial with
  | true => trivial2
  | false => idtac
  end; subst.

Tactic Notation "einversion" uconstr(H) :=
  einversion0 H constr:(false) constr:(false) H.

Tactic Notation "einversion" "trivial" uconstr(H) :=
  einversion0 H constr:(false) constr:(true) H.

Tactic Notation "einversion" uconstr(H) "as" simple_intropattern(intros) :=
  einversion0 H constr:(true) constr:(false) intros.

Tactic Notation "einversion" "trivial" uconstr(H) "as" simple_intropattern(intros) :=
  einversion0 H constr:(true) constr:(true) intros.

Tactic Notation "einstantiate" uconstr(H) "as" simple_intropattern(Htmp) :=
  pose proof H as Htmp; einst0 Htmp ltac:(fun _ => idtac).

Tactic Notation "einstantiate" "trivial" uconstr(H) "as" simple_intropattern(Htmp):=
  einstantiate H as Htmp; trivial2.

Tactic Notation "einstantiate" uconstr(H) :=
  let Htmp := fresh in einstantiate H as Htmp.

Tactic Notation "einstantiate" "trivial" uconstr(H) :=
  let Htmp := fresh in einstantiate trivial H as Htmp.

Ltac invalid H := contradiction H; reflexivity.

Ltac contrapositive Equiv :=
  lazymatch goal with
  | [|- not _ <-> not _] =>
      let H := fresh in
      split; intro H; contradict H; eapply Equiv; try eassumption
  | [|- not _ -> not _] =>
      let H := fresh in
      intro H; contradict H; eapply Equiv; try eassumption
  | _ => fail "Expects a contrapositive of the form ~ _ <-> ~ _ or ~ _ -> ~ _"
  end.
