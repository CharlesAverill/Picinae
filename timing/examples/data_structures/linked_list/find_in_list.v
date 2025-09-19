Require Import linked_list.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.
Require Import Lia ZifyN ZifyBool.
Require Import Picinae_memsolve.
Require Import Coq.Program.Equality.

Require Import Coq.Classes.RelationClasses.

Ltac _noverlap_prepare :=
  noverlap_prepare_unfold_hook; intros;
   repeat
   repeat
    match goal with
    | |- context [ ?M [Ⓓ?X + ?B + ?N := ?V ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- (setmem_mod_l _ _ _ M (X + B + N) V);
          replace (M [ⒹX + B ⊕ N := V ]) with
          (M [ⒹB ⊖ (2 ^ 32 - X) ⊕ N := V ]) in * by (unfold msub; now psimpl);
          simpl (2 ^ 32 - X)
    | |- context [ ?M [Ⓓ?X + ?Y := ?V ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- setmem_mod_l with (a := (X + Y)); replace
          (X ⊕ Y) with (Y ⊖ (2 ^ 32 - X)) in * by now rewrite N.add_comm;
          simpl (2 ^ 32 - X)
    | |- context [ ?M Ⓓ[ ?X + ?B + ?N ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- (getmem_mod_l _ _ _ M (X + B + N)); replace
          (M Ⓓ[ X + B ⊕ N ]) with (M Ⓓ[ B ⊖ (2 ^ 32 - X) ⊕ N ]) in *
          by (unfold msub; now psimpl);
          simpl (2 ^ 32 - X)
    | |- context [ ?M Ⓓ[ ?X + ?Y ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <-getmem_mod_l with (a := (X + Y)) in *; replace
          (X ⊕ Y) with (Y ⊖ (2 ^ 32 - X)) in * by now rewrite N.add_comm;
          simpl (2 ^ 32 - X)
    end;
    repeat match goal with [H:context[2^32-_]|-_] => simpl (2^32-_) in H end;
   repeat
    match goal with
    | |- context [ ?N ⊖ 4294967248 ] =>
          replace (N ⊖ 4294967248) with (48 ⊕ N)
           by (unfold msub; now psimpl);
           rewrite getmem_mod_l with (a := (48 + N)) ||
             rewrite setmem_mod_l with (a := (48 + N))
    end; (* the simpl calls aren't simplifying as intended... *) psimpl.

(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat lazymatch goal with
  | [ H: ?s ?v = _, MDL: models ?typs ?s |- _] =>
      let Hyp := fresh "SBound" in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      (** Keep limit if bitwidth is small; if it is large lia will hang. *)
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end;
      try rewrite H in *; clear H; try clear s MDL
  end.

Module TimingProof (cpu: CPUTimingBehavior).

Module Program_find_in_ll <: ProgramInformation.
    Definition entry_addr : N := 0x10250.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x102b8 => true
        | _ => false
    end | _ => false end.

    Definition binary := linked_list_bin.
End Program_find_in_ll.

Module RISCVTiming := RISCVTiming cpu Program_find_in_ll.
Module find_in_ll := RISCVTimingAutomation RISCVTiming.
Import Program_find_in_ll find_in_ll.

Module p <: LinkedListParams.
  Definition w := 32.
  Definition e := LittleE.
  Definition dw := 4.
  Definition pw := 4.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_RISCV.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *; llunfold.

Definition time_of_find_in_linked_list (mem : N)
        (head : addr) (key : N) (len : nat) (found_idx : option nat)
        (t : trace) :=
    cycle_count_of_trace t =
        (* setup time *)
        taddi + 2 * tsw + taddi + 2 * tsw + tlw +
        if head =? NULL then
            tfbne + taddi + tjal + taddi + 2 * tlw + taddi + tjalr
        else (
        (* added: *)
        match found_idx with
        | None =>
            tjalr + taddi + tlw + tlw + taddi + tlw + tfbne + tlw + tlw + tlw + tlw + tlw + taddi + ttbne + tsw
        | Some _ =>
            tjalr + taddi + tlw + tlw + taddi + tjal + tlw + tfbne + tlw + tlw + tlw
        end +
        (* added^ *)
            ttbne + tlw + ttbne +
            (N.of_nat match found_idx with None => Nat.pred len | Some idx => idx end) *
            (3 * tlw + ttbne + 3 * tlw + tsw + ttbne)
        ).

Definition find_in_linked_list_timing_invs (s : store) (base_mem : N)
    (sp : N) (head : addr) (key : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x10250 => Some (s V_MEM32 = base_mem /\ s R_SP = sp /\
    s R_A0 = head /\ s R_A1 = key /\
    node_distance base_mem head NULL len /\
    LLForall (fun m a => ~overlap 32  a 8 (sp ⊖ 24) 24) base_mem head /\
    cycle_count_of_trace t' = 0)
| 0x10278 => Some (exists ctr mem curr, s V_MEM32 = mem /\ mem Ⓓ[sp ⊖ 20] = curr /\
    s R_S0 = sp /\ mem Ⓓ[ msub 32 sp 24 ] = key/\ curr <> NULL /\
    node_distance mem head curr ctr /\
    node_distance mem head NULL len /\
    (ctr < len)%nat /\
    (head =? NULL) = false /\
    LLForall (fun m a => ~overlap 32 a 8 (sp ⊖ 24) 24) mem head /\
    LLSame base_mem mem head /\
    (forall fuel, key_in_linked_list mem head key fuel -> (ctr <= fuel)%nat) /\
    cycle_count_of_trace t' =
        (* startup time *)
        ttbne + tlw + ttbne + tlw + 2*tsw  + taddi + 2*tsw + taddi +
        (* loop iterations *)
        (N.of_nat ctr) *
        (3 * tlw + ttbne + 3 * tlw + tsw + ttbne))
| 0x102b8 => Some (
    (exists loc, key_in_linked_list base_mem head key loc /\ time_of_find_in_linked_list base_mem head key len (Some loc) t)
    \/
    (forall loc, ~key_in_linked_list base_mem head key loc /\ time_of_find_in_linked_list base_mem head key len None t))
| _ => None end | _ => None end.

Definition lifted_find_in_linked_list : program :=
    lift_riscv linked_list_bin.

(* We use simpl in a few convenient places: make sure it doesn't go haywire *)
Arguments N.add _ _ : simpl nomatch.
Arguments N.mul _ _ : simpl nomatch.

Theorem find_in_linked_list_timing:
  forall s t s' x' base_mem sp head key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (SP: s R_SP = sp)
         (A0: s R_A0 = head)
         (A1: s R_A1 = key)
         (NOV: LLForall (fun m a => ~overlap 32 a 8 (sp ⊖ 24) 24) base_mem head)
         (* list length is finite *)
         (LEN: node_distance base_mem head NULL len),
  satisfies_all
    lifted_find_in_linked_list
    (find_in_linked_list_timing_invs s base_mem sp head key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Ltac show_goal := match goal with |- ?G => idtac "goal: " G end.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. step. now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x10250 -> 0x10278 *)
    destruct PRE as (Mem & SP & A0 & A1 & Len & Bounds & Cycles).

    repeat step.
    (* 0x10278 *) {
        exists 0%nat. eexists. exists head.
        _noverlap_prepare.
        elimstore.
        repeat split; auto. now psimpl.
        now psimpl.
        now rewrite Bool.negb_true_iff, N.eqb_neq in BC0.
        constructor.
        apply llsame_distance with (mem:=base_mem); try easy; llsame_solve.
        eauto using node_distance_len_nonzero.
        now apply Bool.negb_true_iff.
        llforall_solve.
        llsame_solve.
        lia.
        hammer.
    }

    (* head = NULL, contradiction because we checked at the start *)
    inversion BC.

    (* head = null, postcondition *)
    right. intros; split. apply Bool.negb_false_iff, N.eqb_eq in BC.
    elimstore. subst. intro H; inversion H; subst; try discriminate.
    unfold time_of_find_in_linked_list, NULL.
    hammer.

    (* 0x10278 (66168)*)
    destruct PRE as (ctr & mem & curr & Mem & Curr & S0 & Key &  CurrNNull & Dist & Len &
        CtrLen & HeadNonNull & LLB & LLS & Fuel & Cycles).
    remember 0%nat as fuel; clear Heqfuel.
    step. step. step.
    step.
        { repeat step.
        (* next iteration *)
          exists (S ctr). _noverlap_prepare. rewrite Curr in *. remember (mem Ⓓ[ 4 + curr ]) as next.
          (* rewrite negb_true_iff, N.eqb_neq in *. *)
          assert (Heqnext': list_node_next mem curr = Some next).
          { subst next; unfold list_node_next. destruct curr as [|p];[contradiction|reflexivity]. }
          assert (WF:=distance_null_imp_well_formed _ _ _ Len).
          assert (LenNext:node_distance mem head next (S ctr)). { eapply node_distance_next_S_len; try eassumption. }
          repeat eexists; psimpl; auto.
              { psimpl. rewrite N.mod_small by (subst; now apply getmem_bound).
                now rewrite Bool.negb_true_iff, N.eqb_neq in BC0. }
              { psimpl. rewrite N.mod_small by (subst; now apply getmem_bound).
                apply llsame_distance with (mem:=mem); try llsame_solve. }
              { apply llsame_distance with (mem:=mem). llsame_solve. assumption. }
              {
                destruct (Nat.lt_trichotomy (S ctr) len) as [Lt | [Eq | Gt]];[assumption | subst len; exfalso; clear CtrLen | lia ].
                  assert (Help:=node_distance_uniq' _ _ _ _ _ _ LenNext Len (eq_refl (S ctr))); now rewrite Help in BC0.
              }
              llforall_solve.
              llsame_solve.
              llforall_solve.
              {
                rewrite Bool.negb_true_iff, N.eqb_neq in BC0, BC.
                rewrite Key in *.
                apply fuel_le_incr with (curr:=curr); try easy.
                apply llsame_distance with (mem:=mem); try easy; llsame_solve.
                intros fuel' KeyIn'. specialize (Fuel fuel').
                apply llsame_key_in with (mem':=mem) in KeyIn'. now specialize (Fuel KeyIn').
                apply llsame_symmetry; llsame_solve.
                unfold list_node_value. rewrite getmem_noverlap; try easy.
                destruct curr;[discriminate|intros H; injection H; intro; subst key; contradiction].
                apply noverlap_shrink with (a1:=curr) (len1:=8); try lia.
                rewrite LLForall_forall in LLB.
                apply noverlap_symmetry, noverlap_shrink with (a1:=sp ⊖ 24) (len1:=24); try lia.
                apply noverlap_symmetry, LLB; try easy.
                eapply distance_imp_in; eassumption.
              }
              { (* timing condition *)
                hammer.
              }
    destruct (key_in_linked_list_dec base_mem head key fuel) as [IN|NOT_IN].
    (* The key does exist in the linked list *) {
        (* postcondition - reached end of list without finding key ... but the IN hyp says the key is present? *)
        {
          exfalso. clear - IN BC BC0 LLB LLS Dist Len CurrNNull Curr HeadNonNull Key Fuel.
          replace (mem Ⓓ[ 4294967272 + sp ]) with (mem Ⓓ[ msub 32 sp 24 ]) in BC.
          replace (mem Ⓓ[ 4294967276 + sp ]) with (mem Ⓓ[ msub 32 sp 20 ]) in BC, BC0.
          rewrite Curr in *; elimstore; rewrite Bool.negb_true_iff, Bool.negb_false_iff, N.eqb_neq, N.eqb_eq in *.
          assert (Help:len = S ctr). {
            assert (Help2:=distance_last_node _ _ _ _ CurrNNull Dist). unfold list_node_next in Help2.
            destruct curr as [|p];[contradiction|remember (Npos p) as curr]. llunfold. rewrite BC0 in Help2; specialize (Help2 (eq_refl _)).
            eapply node_distance_uniq; eassumption.
          }
          rewrite Help in *.
          move fuel before ctr; move curr before key; move HeadNonNull before CurrNNull.
          remember (mem Ⓓ[ 4 + curr ]) as next.
          apply llsame_key_in with (mem':=mem) in IN; try assumption.
          specialize (Fuel _ IN).
          assert (Contra:=key_loc_lt_length _ _ _ _ _ Len IN).
          assert (H:ctr = fuel) by lia; subst fuel.
          assert (Help2:=key_in_linked_list_value_equal _ _ _ _ _ IN Dist).
          inj_nodeval.
          rewrite H in Key; contradiction.
          all: unfold msub; psimpl; reflexivity.
        }}
    (* The key does NOT exist in the linked list, we've reached the end. *) {
      elimstore; right; intro.
          move curr before sp;  move ctr before len; move s' before s; move fuel before len.
          move SBound before mem;
          move BC at bottom; move LLS before LLB; move Cycles before t; move MDL after Cycles; move ENTRY before t.
          move CurrNNull before CtrLen; move HeadNonNull before CurrNNull.
          move loc before ctr.
          assert (BC0':=BC0); assert (BC':=BC); move BC0 at bottom; move BC0' before MDL; move BC' before MDL.
          rewrite Bool.negb_true_iff, N.eqb_neq in BC; rewrite Bool.negb_false_iff, N.eqb_eq in BC0.
          replace (mem Ⓓ[ 4294967272 + sp ]) with (mem Ⓓ[ msub 32 sp 24 ]) in BC.
          replace (mem Ⓓ[ 4294967276 + sp ]) with (mem Ⓓ[ msub 32 sp 20 ]) in BC, BC0.
          all: try (unfold msub; psimpl; reflexivity).
          rewrite Curr, Key in BC; rewrite Curr in BC0.
          (* end of setup *)
          split.
          intro H; apply (llsame_key_in _ mem) in H; revert H.
          gdep loc; eapply key_not_in_list; try eassumption.
          destruct curr;[contradiction|]. unfold list_node_next; llunfold; now rewrite BC0.
          intro; inj_nodeval. llunfold; rewrite H0 in BC; contradiction.
          now intro.
          enough (Help: len = S ctr). subst len.
          unfold time_of_find_in_linked_list; hammer.
          assert (Help2: list_node_next mem curr = Some NULL) by (destruct curr;[contradiction| unfold list_node_next; llunfold; now rewrite BC0]).
          assert (Help:=distance_last_node _ _ _ _ CurrNNull Dist Help2).
          (* why does `destruct Help` introduce the `len=0` goal? *)
          eapply node_distance_uniq; try eassumption.
        }
    }

      (* Found key at curr node *)
      repeat step.
      elimstore.
          move curr before sp; move ctr before len; move s' before s; move fuel before len.
          move SBound before mem; move BC at bottom; move LLS before LLB; move Cycles before t; move MDL after Cycles; move ENTRY before t.
          move CurrNNull before CtrLen; move HeadNonNull before CurrNNull.
          assert (BC':=BC); move BC' before MDL; rewrite Bool.negb_false_iff, N.eqb_eq in BC.
          replace (mem Ⓓ[ 4294967272 + sp ]) with (mem Ⓓ[ msub 32 sp 24 ]) in BC.
          replace (mem Ⓓ[ 4294967276 + sp ]) with (mem Ⓓ[ msub 32 sp 20 ]) in BC.
          all: try (unfold msub; psimpl; reflexivity).
          rewrite Curr, Key in BC.
          rename ctr into loc.
          (* End of setup *)
          left; exists loc; split.
          apply llsame_key_in with (mem:=mem).
          eapply key_at_node; try eassumption. destruct curr;[contradiction|symmetry; unfold list_node_value; now rewrite BC].
          now rewrite llsame_symmetry.
          unfold time_of_find_in_linked_list; hammer.
Qed.
