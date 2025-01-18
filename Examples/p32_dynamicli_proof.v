Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Import PIL32Notations.
Require Import p32_dynamicli.

Definition dynamic_li_start : N :=  0.
Definition dynamic_li_end   : N := 16.

Section Invariants.
  Variables inp1 inp2 : N.
  Variable  s0 : store.

  Definition postcondition (s:store) := s R_R5 = (777).
  Definition mem_unchanged (s:store) := s V_MEM32 = s0 V_MEM32 /\ s A_EXEC = s0 A_EXEC.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ => match a with
      | 0 => Some (mem_unchanged s)
      | 16 => Some (postcondition s)
      | _ => None end
    | _ => None end.
End Invariants.

Definition dynamicli_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 16 => true
  | _ => false
  end | _ => false end.

Definition exec_bits : addr -> N :=
  fun a => match a with
  | 0 | 4 | 8 | 12 => 1
  | _ => 0 end.

Theorem dynamicli_correctness:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models pil32typctx s)
         (MEM: dynamic_li (s V_MEM32))
         (EXEC: dynamic_li_aexec (s A_EXEC))
,
(* We define our program as p32_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-12 with all other bytes 0.
*)
  satisfies_all p32_prog (invs s) dynamicli_exit ((x',s')::t).
Proof.
Local Ltac step := time pil32_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY.
  step. repeat (split; try assumption).

  (* Inductive cases *)
  intros.
  (* somehow `startof_prefix` is bound to the wrong theorem here...
     In the strspn example the theorem is preferentially bound to
     Picinae.Picinae_armv8.Theory_arm8.startof_prefix
     rather than the alternative Picinae.Picinae_theory.startof_prefix.
     Here it is the opposite, so we must specify the arch-specific version*)
  eapply Picinae.Picinae_pilbox32.Theory_pil32.startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply welltyped_p32prog).
  clear - PRE MDL MEM EXEC. rename s into s0, t1 into t, s1 into s.

  destruct_inv 32 PRE.
  destruct PRE as [MEMSAME EXECSAME].
  rewrite <-MEMSAME, <-EXECSAME in *.
  step.
  step.
  step.
  rewrite <-MEMSAME in *.
  Ltac get_exec ::=
  repeat match goal with
  | [P: ?prop ?v |- _ ] => unfold prop in P
  | [H: xbits (_ ?m) _ _ = _ |- context[N.testbit (update ?s _ _ ?m) _]] =>
    rewrite (update_frame s _ _ m); try easy
  | [H: xbits ?v ?l ?h = ?mem |- context[N.testbit ?v ?i]] =>
    let HELP := fresh "H" in
    assert (HELP: l <= i /\ N.succ i <= h) by (split; lia); clear HELP;
    rewrite testbit_xbits, (xbits_split2 l i (N.succ i) h v mem);[reflexivity |lia..]
  end; vm_compute (N.odd _); psimpl.
Ltac effinv_none_hook ::= unfold effinv, effinv', p32_prog; get_exec.


  eapply NIStep;
   [ effinv_none_hook; reflexivity || fail_seek
   | psa_some_hook; reflexivity || fail_seek
   |  ].

   (* TODO: Continue here. ISA_step_and_simplify is hanging *)
   (let c := fresh "c" in
    let s := fresh "s" in
    let x := fresh "x" in
    let XS := fresh "XS" in
    intros c s x XS).
   Print ISA_step_and_simplify.

   Print step_stmt. Print exec_stmt.
   Print populate_varlist.
   Check fexec_stmt_init.
   generalize XS. Check update_frame.
(* Ltac mem_simpl := *)
  repeat match goal with
  | [ |- context[getmem ?w ?e ?len (setmem ?w ?e ?len ?m ?a ?v) ?a]] => rewrite getmem_setmem
  | [ |- _ ] => rewrite update_frame;[|intro;discriminate]
  end.
  Print overlap. Print N.min.
  Print "<?". Print N.zeros.
(* update_view updates the view of a memory from view1 of bits i to j-1 to
   the view with bits x to y overwritten by the bits in val *)
Definition update_view view i j val x y :=
  if x <? i then
    let view_shift = i - x in
    view << view_shift .&
Theorem update_mem:
  forall w mem i j n a len v
    (MEM: xbits mem (8*i) (8*j) = n)
    (OV: overlap w i (j-i) a len)
    (SMALL: a+len < 2 ^ w),
    xbits (setmem w LittleE len mem a v) (8*(N.min i a)) (8*(N.max j (a+len)) =
      v
  rewrite update_frame.
   mem_simpl.
   eapply fexec_stmt_init in XS.
   [ repeat
      lazymatch type of XS
      with
      | exec_stmt _ (updstr (_[_ := _]) (List.rev _) vupdate) _ _ _ _ /\ _ =>
          eapply fexec_stmt_updn in XS
      end;
      lazymatch type of XS
      with
      | exec_stmt ?c (updstr ?s (List.rev ?l) vupdate) ?q ?c' ?s' ?x /\ _ =>
          let vs := eval compute in (other_vars_read l q) in
          tacmap
           ltac:(fun v =>
                   try
                    match goal with
                    | SV:s v = ?n
                      |- _ => eapply (fexec_stmt_hypn _ _ _ c s v n _ q c' s' x SV) in XS
                    end) vs
      end; eapply fexec_stmt_fin in XS
   |  ]
$
  populate_varlist XS.
  lazymatch type of XS with
  | exec_stmt _ _ _ _ _ _ =>
      populate_varlist XS;
       [ step_precheck XS; eapply reduce_stmt in XS;
          [ let unk := fresh "unknown" in
            destruct XS as [unk XS]; compute in XS;
             repeat
              match type of XS with
              | context [ unk ?i ] =>
                  let n := fresh "n" in
                  set (n := unk i) in XS; clearbody n
              end; try clear unk
          | reflexivity ]; cbv beta match delta [noe_setop noe_typop] in XS
       | reflexivity ]
  | _ => fail "Hypothesis is not of the form (exec_stmt ...)"
  end.

   (* step_stmt hangs *)
   step_stmt XS. ; abstract_ignored_vars XS; psimpl_hyp XS; simpl_memaccs XS; destruct_memaccs XS;
   try generalize_trace

     ; ISA_step_and_simplify XS).
     repeat
      lazymatch type of XS with
      | reset_temps _ s = _ /\ x = _ =>
          try clear c; destruct XS as [XS ?]; subst x;
           try
            (let rt := fresh in
             set (rt := reset_temps _ _)  at 1; psimpl_hyp rt; subst rt;
              rewrite XS; clear XS; try clear s)
      | exec_stmt _ _ (if ?c then _ else _) _ _ _ =>
          let BC := fresh "BC" in
          destruct c eqn:BC; ISA_step_and_simplify XS
      | exec_stmt _ _ (N.iter _ _ _) _ _ _ => fail
      | _ => ISA_step_and_simplify XS
      end;
     try
      lazymatch goal with
      | |- context [ exitof (?m + ?n) ] => simpl (m + n)
      end; try (first [ rewrite exitof_none | rewrite exitof_some ])).
   Print ISA_invseek.
  eapply NIStep.
  effinv_none_hook.

  unfold invs, dynamicli_exit. effinv_none_hook.

  (p32_stmt (setmem 32 LittleE 4 (s V_MEM32) 12 12443) 12))

  (* Notice our address, 12, is exactly the location where we stored a
     value, 12443, in memory. 12433 corresponds exactly to`PIL_li r5 777,`
     the instruction for loading the immediate 777 into register 5.
  *)
  step.
  reflexivity.
Qed.
