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
          rewrite <- (Theory_RISCV.setmem_mod_l _ _ _ M (X + B + N) V);
          replace (M [ⒹX + B ⊕ N := V ]) with
          (M [ⒹB ⊖ (2 ^ 32 - X) ⊕ N := V ]) in * by (unfold msub; now psimpl);
          simpl (2 ^ 32 - X)
    | |- context [ ?M [Ⓓ?X + ?Y := ?V ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- Theory_RISCV.setmem_mod_l with (a := (X + Y)); replace
          (X ⊕ Y) with (Y ⊖ (2 ^ 32 - X)) in * by now rewrite N.add_comm;
          simpl (2 ^ 32 - X)
    | |- context [ ?M Ⓓ[ ?X + ?B + ?N ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- (Theory_RISCV.getmem_mod_l _ _ _ M (X + B + N)); replace
          (M Ⓓ[ X + B ⊕ N ]) with (M Ⓓ[ B ⊖ (2 ^ 32 - X) ⊕ N ]) in *
          by (unfold msub; now psimpl);
          simpl (2 ^ 32 - X)
    | |- context [ ?M Ⓓ[ ?X + ?Y ] ] =>
          assert (TEMP:2^32-X < X) by lia; clear TEMP;
          rewrite <- Theory_RISCV.getmem_mod_l with (a := (X + Y)) in *; replace
          (X ⊕ Y) with (Y ⊖ (2 ^ 32 - X)) in * by now rewrite N.add_comm;
          simpl (2 ^ 32 - X)
    end;
    repeat match goal with [H:context[2^32-_]|-_] => simpl (2^32-_) in H end;
   repeat
    match goal with
    | |- context [ ?N ⊖ 4294967248 ] =>
          replace (N ⊖ 4294967248) with (48 ⊕ N)
           by (unfold msub; now psimpl);
           rewrite Theory_RISCV.getmem_mod_l with (a := (48 + N)) ||
             rewrite Theory_RISCV.setmem_mod_l with (a := (48 + N))
    end; (* the simpl calls aren't simplifying as intended... *) psimpl.


Lemma noverlap_index_l:
  forall w a1 len1 a2 len2 index size
  (NO : ~ overlap w a1 len1 a2 len2)
  (IN : index + size <= len1),
  ~ overlap w (a1 + index) size a2 len2.
Proof.
  intros.
  remember (a1 + index) as a1'. apply noverlap_shrink with (a1:=a1) (len1:=len1).
  rewrite Heqa1'. rewrite add_msub_l.
  apply N.le_trans with (m:=index+size). rewrite <-N.add_le_mono_r. apply N.Div0.mod_le.
  assumption.
  assumption.
Qed.

Lemma noverlap_index_r:
  forall w a1 len1 a2 len2 index size
  (NO : ~ overlap w a1 len1 a2 len2)
  (IN : index + size <= len2),
  ~ overlap w a1 len1 (a2+index) size.
Proof.
  intros. eapply noverlap_symmetry, noverlap_index_l;[
    eapply noverlap_symmetry; eassumption
  | eassumption ].
Qed.

Lemma noverlap_index_index:
  forall w a1 len1 a2 len2 index1 size1 index2 size2
  (NO  : ~ overlap w a1 len1 a2 len2)
  (IN1 : index1 + size1 <= len1)
  (IN2 : index2 + size2 <= len2),
  ~ overlap w (a1 + index1) size1 (a2 + index2) size2.
Proof.
  intros. apply noverlap_index_l with (len1:=len1).
  apply noverlap_symmetry. apply noverlap_index_l with (len1:=len2).
  apply noverlap_symmetry.
  all: assumption.
Qed.


Theorem _models_var:
  forall v {c s} (MDL: models c s),
  match c v with Some (NumT w) => 
                  match s v with
                  | VaN v _ => v < 2^w
                  | _ => False
                  end
               | _ => True end.
Proof.
  intros. destruct (c v) eqn:CV; [|exact I].
  specialize (MDL _ _ CV). inversion MDL; easy.
Qed.

Theorem models_var:
  forall v {c s} (MDL: models c s) x w,
  s v = VaN x w -> match c v with 
                   | Some (NumT w) => x < 2^w 
                   | _ => True 
                   end.
Proof.
  intros. assert (H':=_models_var v MDL). rewrite H in *.
  destruct (c v) eqn:CV.
  destruct t.  assumption.
  unfold models in *. specialize (MDL v _ CV).
  inversion MDL; subst. rewrite H in *; discriminate.
  easy.
Qed.

(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat
   lazymatch goal with
   | H:?s ?v = VaN ?x ?w, MDL:models ?typs ?s
     |- _ =>
         let Hyp := fresh "SBound" in
         pose proof (models_var v MDL x w H) as Hyp;
         let tHyp := type of Hyp in
         cbv -[N.lt N.pow] in Hyp;
         let tHyp := type of Hyp in
          match type of Hyp with
          | _ < 2 ^ ?w =>
              assert (temp : (w <=? 256) = true) by reflexivity; clear temp
          | _ => clear Hyp
          end; try rewrite H in *; clear H; try clear s MDL
   end.

Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *.

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

Definition NULL : N := 0.
Definition list_node_value (mem : addr -> N) (node : addr) : N :=
    mem Ⓓ[node].
Definition list_node_next (mem : addr -> N) (node : addr) : N :=
  (* Original definition: mem Ⓓ[4 + node]. *)
  (* Allowing NULL to have itself as the next node: *)
  match node with 0 => NULL | _ => mem Ⓓ[4 + node] end.

Inductive key_in_linked_list : (addr -> N) -> addr -> N -> nat -> Prop :=
| KeyAtHead mem node key :
    node <> NULL ->
    list_node_value mem node = key ->
    key_in_linked_list mem node key 0
| KeyAtNext mem node key idx :
    node <> NULL ->
    list_node_value mem node <> key ->
    key_in_linked_list mem (list_node_next mem node) key idx ->
    key_in_linked_list mem node key (S idx).

Fixpoint key_in_linked_list_dec (mem : addr -> N) (node : addr) (key : N) (idx : nat)
        : {key_in_linked_list mem node key idx} + {~ key_in_linked_list mem node key idx}.
    destruct node as [|p];[|remember (Npos p) as node].
    {
      right. intro. dependent induction H; subst. contradiction.
      assert (Help:list_node_next mem 0 ~= 0) by reflexivity.
      now specialize (IHkey_in_linked_list Help).
    }
(* destruct (N.eq_dec (list_node_value mem node) key). *)
    destruct idx as [| idx'].
    - (* Base case: idx = 0 *)
        destruct (N.eq_dec (list_node_value mem node) key) as [Heq | Hneq].
        + left. constructor. intro; now subst. assumption.
        + right. intros H. inversion H. subst. contradiction.
    - (* Inductive case: idx = S idx' *)
        destruct (N.eq_dec (list_node_value mem node) key) as [Heq | Hneq].
        { right; intro H; inversion H; contradiction. }
        destruct (key_in_linked_list_dec mem (list_node_next mem node) key idx') as [IN | NOT_IN].
        + left. constructor. intro; now subst. assumption. exact IN.
        + right. intros H. inversion H. subst. apply NOT_IN. assumption.
Qed.

(* node_in_linked_list allows for the looked up node to be NULL. *)
Inductive node_in_linked_list : (addr -> N) -> addr -> addr -> Prop :=
  | NodeAtHead : forall mem node, node_in_linked_list mem node node
  | NodeInTail : forall mem node head
    (NEQ: node <> head)
    (NNUL: head <> NULL)
    (IN: node_in_linked_list mem (list_node_next mem head) node),
    node_in_linked_list mem head node.

(** A list is well formed if the head node points
      1) NULL, or
      2) the head of a well formed list. *)
Inductive well_formed_list : (addr -> N) -> addr -> Prop :=
| wf_nil : forall mem, well_formed_list mem NULL
| wf_cons : forall mem n
    (NNUL: n <> NULL)
    (NEXTWF: well_formed_list mem (list_node_next mem n)),
    well_formed_list mem n.

Inductive node_distance : (addr -> N) -> addr -> addr -> nat -> Prop :=
| Dst0 : forall mem node,
    node_distance mem node node 0
| DstSn : forall mem src dst len
    (NNUL: src <> NULL)
    (NEQ: src <> dst)
    (LEN: node_distance mem (list_node_next mem src) dst len),
    node_distance mem src dst (S len).

Theorem node_distance_uniq:
  forall mem src dst len1 len2,
    node_distance mem src dst len1 ->
    node_distance mem src dst len2 ->
    len1 = len2.
Proof.
  intros mem src dst len1 len2 H; revert len2.
  induction H; intros len2 L2.
  - inversion L2; subst.
      reflexivity.
      contradiction.
  - inversion L2; subst.
      contradiction.
      now rewrite (IHnode_distance len0).
Qed.

Theorem node_distance_uniq':
  forall mem src dst1 len1 dst2 len2,
    node_distance mem src dst1 len1 ->
    node_distance mem src dst2 len2 ->
    len1 = len2 -> dst1 = dst2.
Proof.
  intros mem src dst1 len1 dst2 len2 H; revert dst2 len2 .
  induction H; intros dst2 len2 L2.
  - inversion L2; subst.
      reflexivity.
      intro; discriminate.
  - inversion L2; subst.
      intro; discriminate.
      intro EQ; injection EQ; clear EQ; intro EQ; subst len0.
      eapply IHnode_distance; try eassumption. reflexivity.
Qed.


Theorem no_node_in_null:
  forall mem node (NNUL: node <> NULL), ~node_in_linked_list mem NULL node.
Proof.
  intros; intro H; inversion H; subst; try contradiction.
Qed.

Theorem wf_has_null:
  forall mem head (WF: well_formed_list mem head),
  node_in_linked_list mem head NULL.
Proof.
  intros. induction WF.
    constructor.
    eapply NodeInTail; try easy.
Qed.

Theorem has_null_wf:
  forall mem head (NUL: node_in_linked_list mem head NULL),
  well_formed_list mem head.
Proof.
  intros. dependent induction NUL.
    constructor.
    eapply wf_cons; try easy.
    apply IHNUL; reflexivity.
Qed.

Theorem well_formed_impl_next_not_same:
  forall mem src (WF: well_formed_list mem src),
  src = NULL \/ list_node_next mem src <> src.
Proof.
  intros.
  destruct (N.eq_dec src NULL).
    now left.
    (* Interesting that inversion isn't enough, needed induction. *)
    induction WF; subst; right.
       contradiction.
       intro H1; rewrite H1 in *. destruct (IHWF n).
         subst; contradiction.
         contradiction.
Qed.

Theorem only_null_in_null:
  forall mem node,  node_in_linked_list mem NULL node -> node = NULL.
Proof.
  intros mem node H. inversion H; subst; try easy.
Qed.

Theorem in_impl_next_in:
  forall mem n n' head
    (NEXT: n' = list_node_next mem n)
    (IN: node_in_linked_list mem head n),
  node_in_linked_list mem head n'.
Proof.
  intros. revert NEXT; revert n'.
  dependent induction IN.
  - intros. destruct (N.eq_dec node NULL);[subst node|].
      cbn in NEXT; subst; constructor.
      destruct (N.eq_dec n' node) as [e|e];[subst n';rewrite e in *; constructor|].
      apply NodeInTail; try easy. rewrite <-NEXT; constructor.
  - rename IHIN into IH. intros. remember (list_node_next mem head) as head'. move n' before node.
    specialize (IH _ NEXT).
    destruct (N.eq_dec n' head) as [e|e];[rewrite e; apply NodeAtHead|].
    apply NodeInTail; try easy. rewrite <-Heqhead'; assumption.
Qed.

Theorem well_formed_impl_not_in_strong:
  forall mem src (NNUL: src <> NULL) (WF: well_formed_list mem src),
  forall node (IN: node_in_linked_list mem src node),
  ~node_in_linked_list mem (list_node_next mem node) src.
Proof.
  intros mem src NNUL WF. dependent induction WF generalizing NNUL. intros node IN.
  - contradiction.
  - remember (list_node_next mem n) as n'. clear NNUL0.
    (* n -> n' ... *)
    destruct (N.eq_dec n' NULL).
    (* next node, node, is null, reached end of list without finding src *)
    (* n -> NULL = n'*)
    + intros node IN IN2. subst n'.
      (* Node must be NULL or n, we prove a contradiction in either case. *)
      assert (CASE: node = NULL \/ node = n).
      inversion IN; subst.
        right; reflexivity.
        destruct (N.eq_dec node NULL);[left; assumption|rewrite e in *]. now assert (H':=only_null_in_null _ _ IN0).
      destruct CASE.
        (* node is NULL *)
        subst node. inversion IN; subst; try easy. rewrite e in *; clear e IHWF NNUL NNUL0. 
        cbn in IN2; apply only_null_in_null in IN2. symmetry in IN2; contradiction.
        (* node is n *)
        subst node. rewrite e in *. apply only_null_in_null in IN2; contradiction.
    (* n -> n' -> ... -> node -> node' -> ... *)
    + intros node IN In2; remember (list_node_next mem node) as node'; rename IHWF into IH;
      specialize (IH n0); rename In2 into IN2.
      (* WF n'
         def: node -> node'
         IN: n -> ... -> node
         In2: node' -> ... -> n
         IH: (n' ~~> ?x) -> (~ ?x' ~~> n')
         So say ?x is node. If node is n we have a cycle, otherwise use IH.
      *)
      move IN before IN2. move IH before IN. move Heqnode' after Heqn'.
      specialize (IH node).
      inversion IN;[subst node0 node mem0|].
        rewrite <-Heqn' in *; subst node'; specialize (IH IN2); apply IH; constructor.
        subst mem0 node0 head; rewrite <-Heqn' in *; specialize (IH IN0); rewrite <-Heqnode' in *.
        move NEQ before n0; clear NNUL0.
        assert (CONTRA:=in_impl_next_in _ _ _ _ Heqn' IN2); contradiction.
Qed.

Theorem well_formed_impl_not_in:
  forall mem src (NNUL: src <> NULL) (WF: well_formed_list mem src),
  ~node_in_linked_list mem (list_node_next mem src) src.
Proof.
  intros. eapply (well_formed_impl_not_in_strong _ _ _ _ _). Unshelve.
  constructor.
  all:assumption.
Qed.

Lemma well_formed_impl_next_neq_curr : 
  forall mem src
    (NNUL: src <> NULL)
    (WF: well_formed_list mem src),
  list_node_next mem src <> src.
Proof.
    intros. induction WF; subst.
        assumption.
    intro. rewrite H in *. specialize (IHWF NNUL0). contradiction.
Qed.    

Lemma node_distance_len_nonzero : forall m head len,
    node_distance m head NULL len ->
    negb (head =? NULL) = true ->
    (0 < len)%nat.
Proof.
    intros. revert H0. induction H; intros.
        rewrite N.eqb_refl in H0; inversion H0.
    lia.
Qed.

Lemma node_distance_same : forall m h n,
    node_distance m h h n -> n = O.
Proof.
    intros. inversion H; subst. reflexivity.
    contradiction.
Qed.

Ltac gdep n := generalize dependent n.
Lemma node_distance_null_dupe : forall m head tail n1 n2,
    node_distance m head tail n1 ->
    node_distance m head tail n2 ->
    n1 = n2.
Proof.
  intros m head tail n1. gdep head; gdep tail.
  induction n1 as [n1 IHn1] using lt_wf_ind.
  intros tail head n2 N1 N2.
  inversion N1; subst.
    now inversion N2.
    inversion N2; subst.
      contradiction.
      specialize (IHn1 len (Nat.lt_succ_diag_r _) _ _ len0 LEN LEN0). now subst.
Qed.

(* Inductive type for properties holding for all nodes in a list.
   The property P is a function from memory and address to a prop. *)
Inductive LLForall (P: (addr->N)->N->Prop): (addr -> N) -> N -> Prop :=
  | LLForall_nil : forall mem, LLForall P mem NULL
  | LLForall_cons : forall mem addr 
                      (NNUL: addr <> NULL) 
                      (HEAD: P mem addr) 
                      (TAIL: LLForall P mem (list_node_next mem addr)),
                    LLForall P mem addr.

(* Specify a loose bound on the minimum address of nodes in a linked list.
   This doesn't guarantee any node actually has this address. *)
Definition LLBounds mem addr min max := LLForall (fun _ a => min <= a <= max) mem addr.
Inductive LLSame : (addr->N) -> (addr->N) -> N -> Prop :=
  | LLSame_nil : forall mem mem', LLSame mem mem' NULL
  | LLSame_cons : forall mem mem' head,
                  (list_node_value mem head) = (list_node_value mem' head) ->
                  (list_node_next mem head) = (list_node_next mem' head) ->
                  LLSame mem mem' (list_node_next mem head) ->
                  LLSame mem mem' head.

Theorem llsame_ind:
  forall mem head (f:(addr->N)->(addr->N))
    (PRES:LLForall (fun mem' a => list_node_value mem a = list_node_value mem' a /\ list_node_next mem a = list_node_next mem' a)
      (f mem) head),
  LLSame mem (f mem) head.
Proof.
  intros. dependent induction PRES;[constructor|].
  destruct HEAD as [Val Next].
  apply LLSame_cons; try easy; rename addr into a.
  specialize (IHPRES mem f (eq_refl _) (eq_refl _)).
  now rewrite Next.
Qed.

Theorem noverlap_llsame:
  forall mem e wraddr wrlen v head min max
    (LLB: LLBounds mem head min max)
    (NOV: ~overlap 32 wraddr wrlen min (max+8-min)),
  LLSame mem (setmem 32 e wrlen mem wraddr v) head.
Proof.
  intros. pose (fun mem => setmem 32 e wrlen mem wraddr v) as f.
  replace (setmem _ _ _ _ _ _) with (f mem); try reflexivity.
  apply llsame_ind.
  dependent induction LLB.
  { apply LLForall_nil. }
  {
    rename addr into a.
    assert (Rem:list_node_next mem a = list_node_next (f mem) a).
    (* noverlap_sum + lia can't handle this either *)
    { destruct a as [|p];[contradiction|].
      unfold f, list_node_next; rewrite getmem_noverlap;[reflexivity|].
      apply noverlap_symmetry; remember (N.pos p) as a.
      pose (4 + a - min) as i. replace (4+a) with (min+i) by lia.
      eapply noverlap_index_r. exact NOV. lia.
    }
    assert (Rem2:list_node_value mem a = list_node_value (f mem) a).
    (* noverlap_sum + lia can't handle this either *)
    { destruct a as [|p];[contradiction|].
      unfold f, list_node_value; rewrite getmem_noverlap;[reflexivity|].
      apply noverlap_symmetry; remember (N.pos p) as a.
      pose (a - min) as i. replace (a) with (min+i) by lia.
      eapply noverlap_index_r. exact NOV. lia.
    }
    apply LLForall_cons; try easy.
    specialize (IHLLB NOV).
    unfold f at 1. rewrite <-Rem.
    apply IHLLB.
  }
Qed.

Theorem llforall_next:
  forall mem head p
    (ALL: LLForall p mem head),
  LLForall p mem (list_node_next mem head).
Proof.
  intros. dependent induction ALL;[simpl;constructor|assumption].
Qed.

Theorem llbounds_next:
  forall mem head min max, LLBounds mem head min max -> LLBounds mem (list_node_next mem head) min max.
Proof.
  intros. now apply llforall_next.
Qed.

Theorem noverlap_llsame_trans:
  forall mem mem' e wraddr wrlen v head min max
    (LLB: LLBounds mem head min max)
    (LLS: LLSame mem mem' head)
    (NOV: ~overlap 32 wraddr wrlen min (max+8-min)),
    LLSame mem (setmem 32 e wrlen mem' wraddr v) head.
Proof.
  intros. dependent induction LLS;[constructor|].
  rename IHLLS into IH, H into VAL, H0 into NEXT; move mem' before mem.
  specialize (IH (llbounds_next _ _ _ _ LLB) NOV).
  destruct LLB; [constructor|].
  destruct HEAD as [LO HI]; clear LLB. constructor. 3: exact IH.
  unfold list_node_value. rewrite getmem_noverlap. now unfold list_node_value in VAL.
  (* Interesting, lia doesn't work for this noverlap goal, so have to do it logically... *)
  pose (addr-min) as i.
  replace addr with (min+i) by lia.
  eapply noverlap_index_l. apply noverlap_symmetry; eassumption. lia.

  clear - LO HI NEXT NNUL NOV; unfold list_node_next in *.
  destruct addr;[contradiction|remember (N.pos p) as addr].
  rewrite getmem_noverlap; try easy.
  pose (addr - min) as i. replace (4+addr) with (min+(i+4)) by lia. apply noverlap_symmetry.
  eapply noverlap_index_r; try eassumption; try lia.
Qed.

Theorem LLForall_ind':
  forall P mem head,
    P mem head ->
    (forall n, node_in_linked_list mem head n -> P mem n) ->
    LLForall P mem head.
Proof.
  intros. destruct head; constructor.
  easy. easy.
Abort.


(*
Theorem LLSame_ind' : 
       ()
       (forall mem mem' : addr -> N, LLSame mem mem' NULL) ->
       (forall (mem mem' : addr -> N) (head : addr),
        head <> NULL ->
        list_node_value mem head = list_node_value mem' head ->
        list_node_next mem head = list_node_next mem' head ->
        LLSame mem mem' (list_node_next mem head) ->
        LLSame mem mem' (list_node_next mem head) -> LLSame mem mem' head) ->
       forall (n n0 : addr -> N) (n1 : N), LLSame n n0 n1.
Proof.
  intros. destruct n1.
  constructor.
  apply H0; try easy.
 *)



Theorem llsame_same:
  forall mem head len, node_distance mem head NULL len -> LLSame mem mem head.
Proof.
  intros m head len LEN. dependent induction LEN;[constructor|].
  specialize (IHLEN (JMeq_refl 0)).
  constructor; try easy.
Qed.

Theorem llsame_same':
  forall mem head, LLSame mem mem head.
Proof.
  intros m head. constructor; try easy.
  (* Now what?? *)
Abort.

Theorem llsame_bounds:
  forall mem mem' head min max
    (SAME: LLSame mem mem' head)
    (LLB: LLBounds mem head min max),
  LLBounds mem' head min max.
Proof.
  unfold LLBounds; intros. revert SAME; revert mem'.
  dependent induction LLB.
    constructor.
    intros; inversion SAME; subst.
      contradiction.
      constructor; try easy.
      rewrite <-H0. now apply IHLLB.
Qed.

Theorem llsame_distance:
  forall mem mem' head node len
    (SAME:LLSame mem mem' head)
    (LEN: node_distance mem head node len),
  node_distance mem' head node len.
Proof.
  intros. dependent induction LEN;[constructor|].
  constructor; try easy.
  inversion SAME;subst;[contradiction|].
  rewrite <-H0. now apply IHLEN.
Qed.

Theorem llsame_symmetry:
  forall ml mr h, LLSame ml mr h <-> LLSame mr ml h.
Proof.
  intros; split; intro H; induction H; subst.
  1,3:apply LLSame_nil.
  all:apply LLSame_cons; try easy; now rewrite H0 in IHLLSame.
Qed.

(* Conveniently saves us a book-keeping clause in the loop invariant stating
   the current node is not null. *)
Theorem dist_lt_null_not_null:
  forall mem head node nodelen dst dstlen
    (NODE: node_distance mem head node nodelen)
    (DST: node_distance mem head dst dstlen)
    (LT: (nodelen < dstlen)%nat),
  node <> dst.
Proof.
  intros. gdep LT; gdep nodelen; gdep node. dependent induction DST;[lia|].
  intros.
  assert (H: N : Type) by constructor.
  Local Ltac mvvars T :=
    assert (Temp: N : Type) by constructor;
    idtac "Collecting vars of " T; clear Temp;
    repeat match goal with
    | [vtop: T |- _] =>
        idtac "vtop: " vtop;
        repeat match goal with 
        | [v: T |- _] => idtac "v: " v "vtop: " vtop; first [
              idtac "in first"; fail 0
            | assert (Temp: vtop = v) by reflexivity; clear Temp (* don't move the same var *)
            | move v before vtop ]
        end end.
  mvvars nat.


  move node before len; move nodelen before len; move NODE before DST;  rename IHDST into IH.
  inversion NODE; subst; try assumption.
  eapply IH; clear IH NNUL0; move len0 before len; move NEQ0 before NEQ; move LT after LEN; unfold lt in LT.
  eassumption.
  lia.
Qed.

Theorem distance_imp_head_next_nnul:
  forall mem head dst len'
    (DST: dst <> NULL)
    (LEN: node_distance mem head dst (S len')),
  list_node_next mem head <> NULL.
Proof.
  intros. inversion LEN; subst. inversion LEN0; subst; try easy.
Qed.

Theorem distance_imp_in:
  forall mem head dst len,
    node_distance mem head dst len -> node_in_linked_list mem head dst.
Proof.
  intros. dependent induction H;[constructor|rename IHnode_distance into IH].
  constructor; try easy.
Qed.

Theorem next_node_in_linked_list:
  forall mem head n, n <> NULL -> node_in_linked_list mem head n -> node_in_linked_list mem head (list_node_next mem n).
Proof.
  intros. induction H0.
    destruct (N.eq_dec (list_node_next mem node) node) as [EQ|NEQ];[rewrite EQ in *|]; constructor; try easy; constructor.
    rename IHnode_in_linked_list into IH. remember (list_node_next mem node) as next. specialize (IH H).
    inversion IH; subst mem0 node0; try subst head0.
      - clear - NNUL. destruct (N.eq_dec head (list_node_next mem head)) as [Eq|?];[rewrite Eq at 1; apply NodeAtHead|].
        apply NodeInTail; try easy. apply NodeAtHead.
      - destruct (N.eq_dec next head);[| apply NodeInTail; try easy].
        subst head. apply NodeAtHead.
Qed.

Theorem in_well_formed_imp_well_formed:
  forall mem head node
    (WF: well_formed_list mem head)
    (IN: node_in_linked_list mem head node),
  well_formed_list mem node.
Proof.
  intros. dependent induction IN;[assumption|].
  apply IHIN. inversion WF; subst;[contradiction|assumption].
Qed.

(* This is not generally true for lists with cycles. Observe the difference between
   the distances of X and Y, and X' and Y' below:

            X -> X' -> Y' -> _ -> _ -> _ -> Y
                        ^--------------------+ 
*)
Theorem node_distance_next_next_same:
  forall mem head (dst:addr) len
    (NNUL: dst <> NULL)
    (WF: well_formed_list mem head)
    (LEN: node_distance mem head dst len),
  node_distance mem (list_node_next mem head) (list_node_next mem dst) len.
Proof.
  intros mem head dst len. gdep dst; gdep head; gdep mem. induction len.
  {
    intros. inversion LEN; subst; constructor.
  }
  {
    intros. rename IHlen into IH.
    destruct (N.eq_dec head NULL);[inversion LEN; now subst|].
    apply DstSn; try easy. 
    - (* contradiction if head->null because there's distance between head and dst, and dst is not null. *)
      eapply distance_imp_head_next_nnul with (dst:=dst); try eassumption.
    - clear - NNUL n WF LEN. intro. inversion WF; subst; try easy. 
      clear n; move NNUL0 after NNUL.
      assert (Help:=distance_imp_in _ _ _ _ LEN).
      inversion Help; subst.
      + inversion LEN; now subst.
      + rewrite H in IN. apply (in_well_formed_imp_well_formed _ _ _ WF) in Help.
        apply (well_formed_impl_not_in _ _ NNUL Help). assumption.
    - apply IH; try easy. inversion WF; subst; try easy.
      inversion LEN; subst; try easy.
  }
Qed.

Theorem next_node_is_in:
  forall mem node
    (NNUL: node <> NULL),
  node_in_linked_list mem node (list_node_next mem node).
Proof.
  intros. destruct (N.eq_dec (list_node_next mem node) node).
  - rewrite e; constructor.
  - constructor; try easy. constructor.
Qed.

Theorem wf_imp_next_diff:
  forall mem node, node <> NULL -> well_formed_list mem node -> list_node_next mem node <> node.
Proof.
  intros mem node NNUL WF. intro. inversion WF; subst; try easy.
  assert (Help:=well_formed_impl_not_in _ _ NNUL WF).
  assert (Help2:=next_node_is_in mem _ NNUL). rewrite H in Help2. rewrite <-H in Help2 at 1. contradiction.
Qed.

(* This is not generally true of lists with cycle, Consider the situation below:

      head -> dst' -> _ -> _ -> dst 
               ^-----------------+
*)
Theorem node_distance_next_S_len:
  forall mem head dst len
    (NNUL: dst <> NULL)
    (WF: well_formed_list mem head)
    (LEN: node_distance mem head dst len),
  node_distance mem head (list_node_next mem dst) (S len).
Proof.
  intros. destruct (N.eq_dec head NULL);[inversion LEN; subst; contradiction|].
  {
    destruct len. inversion LEN; subst. constructor; try easy.
    symmetry; apply wf_imp_next_diff; try easy.
    constructor.
    constructor; try easy.
    (* Well-formedness contradiction subproof. *)
    { intro.
      assert (Help:=distance_imp_in _ _ _ _ LEN).
      assert (WFDST:=in_well_formed_imp_well_formed _ _ _ WF Help).
      move n after NNUL; move WF before WFDST; move H after LEN.
      assert (Help3:=well_formed_impl_not_in _ _ NNUL WFDST).
      now rewrite H in Help.
    }
    apply node_distance_next_next_same; try easy.
  }
Qed.

Theorem distance_null_imp_well_formed:
  forall mem head len
    (LEN: node_distance mem head NULL len),
  well_formed_list mem head.
Proof.
  intros. dependent induction LEN;[constructor|].
  rename IHLEN into IH; assert (Help:0~=NULL) by reflexivity; specialize (IH Help); clear Help NEQ.
  apply wf_cons; try easy.
Qed.
  
Theorem distance_imp_diff:
  forall mem head n len
    (LEN: node_distance mem head n (S len)),
  head <> n.
Proof.
  intros. intro. inversion LEN; subst. contradiction.
Qed.

Theorem wf_by_parts:
  forall mem head n len
    (WFTail: well_formed_list mem n)
    (LEN: node_distance mem head n len),
  well_formed_list mem head.
Proof.
  intros. dependent induction LEN;[assumption|].
  specialize (IHLEN WFTail). constructor; try easy.
Qed.

Theorem distance_last_node:
  forall mem head n len
    (NNUL: n <> NULL)
    (LEN: node_distance mem head n len)
    (NIL: list_node_next mem n = NULL),
  node_distance mem head NULL (S len).
Proof.
  intros. rewrite <-NIL.
  apply node_distance_next_S_len; try easy.
  eapply wf_by_parts; try eassumption.
  constructor; try easy.
  rewrite NIL; constructor.
Qed.

Theorem node_in_linked_list_trans:
  forall mem head m dst
    (IN1: node_in_linked_list mem head m)
    (IN2: node_in_linked_list mem m dst),
  node_in_linked_list mem head dst.
Proof.
  intros mem head m dst IN1; gdep dst; dependent induction IN1;[now intros|].
  intros. destruct (N.eq_dec dst head);[subst dst; constructor|].
  constructor; try easy.
  now apply IHIN1.
Qed.

Theorem node_distance_split:
  forall mem head m dst pre post
    (WF: well_formed_list mem head)
    (PRE: node_distance mem head m (pre))
    (POST: node_distance mem m dst post),
  node_distance mem head dst (pre+post)%nat.
Proof.
  intros mem head m dst pre post WF PRE. gdep WF; gdep dst; gdep post. dependent induction PRE;[now simpl|].
  rename len into pre'; rename src into head; rename dst into m.
  intros post dst WF POST. move post before pre'; move dst before m.
  rewrite Nat.add_succ_l. destruct (N.eq_dec head dst).
  {
    subst dst. exfalso. 
    eapply well_formed_impl_not_in; try eassumption.
    assert (IN1:=distance_imp_in _ _ _ _ PRE);
    assert (IN2:=distance_imp_in _ _ _ _ POST).
    apply node_in_linked_list_trans with (m:=m); try easy.
  }
  {
    apply DstSn; try easy.
    apply IHPRE; try easy.
    inversion WF; subst; try easy.
  }
Qed.

Theorem key_loc_split:
  forall mem head node key pre post
    (DIST: node_distance mem head node (pre))
    (KEY: key_in_linked_list mem head key (pre+post)),
  key_in_linked_list mem node key post.
Proof.
  intros mem head node key pre post DIST. dependent induction DIST;[now simpl|].
  intros. inversion KEY; subst.
  specialize (IHDIST H5). assumption.
Qed.

Theorem no_key_in_null:
  forall mem key len, ~key_in_linked_list mem NULL key len.
Proof. 
  intros. intro H. dependent induction H; subst. contradiction.
  assert (Help:list_node_next mem 0 ~= NULL) by reflexivity.
  now specialize (IHkey_in_linked_list Help).
Qed.


Theorem key_loc_lt_length:
  forall mem head len key loc
    (LEN: node_distance mem head NULL len)
    (LOC: key_in_linked_list mem head key loc),
  (loc < len)%nat.
Proof.
  intros. move loc after len. destruct (Nat.lt_ge_cases loc len) as [Lt | Ge];[assumption|exfalso].
  pose (loc-len)%nat as post.
  replace loc with (len+post)%nat in LOC by lia.
  apply (key_loc_split _ _ _ _ _ _ LEN) in LOC.
  now apply no_key_in_null in LOC.
Qed.

Theorem key_loc_le_instance:
  forall mem head key loc1 node loc2
    (LEN: node_distance mem head node loc2)
    (INST: list_node_value mem node = key)
    (LOC: key_in_linked_list mem head key loc1),
  (loc1 <= loc2)%nat.
Proof.
  intros. move loc2 before loc1; move node before head. destruct (Nat.le_gt_cases loc1 loc2) as [Le | Gt];[assumption|exfalso].
  pose (loc1-loc2)%nat as post.
  replace loc1 with (loc2+post)%nat in LOC by lia.
  apply (key_loc_split _ _ _ _ _ _ LEN) in LOC.
  inversion LOC;[lia|].
  subst mem0 node0 key0.
  contradiction.
Qed.


Theorem key_in_linked_list_value_equal:
  forall mem head key loc node
    (Key: key_in_linked_list mem head key loc)
    (Dist: node_distance mem head node loc),
  key = list_node_value mem node.
Proof.
  intros mem head key loc node Key; gdep node. dependent induction Key.
  {
    intros. inversion Dist; subst. reflexivity.
  }
  {
    intros. rename node0 into kn. apply IHKey.
    inversion Dist; now subst.
  }
Qed.

Theorem fuel_le_incr:
  forall mem head key curr ctr
    (Ctr:node_distance mem head curr ctr)
    (Fuel:forall fuel, key_in_linked_list mem head key fuel -> (ctr <= fuel)%nat)
    (BC: key <> list_node_value mem curr),
  forall fuel, key_in_linked_list mem head key fuel -> (S ctr <= fuel)%nat.
Proof.
  intros. specialize (Fuel _ H). destruct (Nat.lt_ge_cases ctr fuel);[lia|exfalso].
  assert (Help:fuel=ctr) by lia; rewrite Help in *; clear Fuel H0 Help.
  assert (Contra:=key_in_linked_list_value_equal _ _ _ _ _ H Ctr).
  contradiction.
Qed.

Theorem node_in_tail:
  forall mem head n
    (IN:node_in_linked_list mem head n)
    (NNUL:head <> NULL)
    (NEQ:head <> n),
  node_in_linked_list mem (list_node_next mem head) n.
Proof.
  intros. dependent induction IN.
  contradiction.
  assumption.
Qed.

Theorem llsame_value:
  forall mem mem' head node v
    (IN: node_in_linked_list mem head node)
    (LLS: LLSame mem mem' head)
    (V: list_node_value mem node = v)
    (NNUL: node <> NULL),
  list_node_value mem' node = v.
Proof.
  intros. gdep V; gdep IN; gdep node. dependent induction LLS; intros.
  - inversion IN; now subst.
  - destruct (N.eq_dec head NULL);[subst; now inversion IN|].
    destruct (N.eq_dec head node);[subst; now inversion IN|].
    assert (H1:=node_in_tail _ _ _ IN n n0).
    apply IHLLS; try easy.
Qed.

Theorem llsame_node_in:
  forall mem mem' head node
    (IN: node_in_linked_list mem head node)
    (LLS: LLSame mem mem' head),
  node_in_linked_list mem' head node.
Proof.
  intros. gdep IN; gdep node. dependent induction LLS; intros.
  - inversion IN; subst. apply NodeAtHead. contradiction.
  - move node before head.
    destruct (N.eq_dec head NULL). subst; assert (t:=only_null_in_null _ _ IN); subst; constructor.
    destruct (N.eq_dec head node). subst; constructor.
    apply NodeInTail; try easy. rewrite <-H0; apply IHLLS. inversion IN;[subst; contradiction|assumption].
Qed.

Theorem llsame_value_neq:
  forall mem mem' head node v
    (IN: node_in_linked_list mem head node)
    (LLS: LLSame mem mem' head)
    (V: list_node_value mem node <> v)
    (NNUL: node <> NULL),
  list_node_value mem' node <> v.
Proof.
  intros. intro. 
  apply llsame_node_in with (mem':=mem') in IN; try assumption.
  rewrite llsame_symmetry in LLS.
  assert(Help:=llsame_value _ _ _ _ _ IN LLS H NNUL).
  contradiction.
Qed.

Theorem llsame_next_node:
  forall mem mem' head node
    (IN: node_in_linked_list mem head node)
    (LLS: LLSame mem mem' head)
    (NNUL: node <> NULL),
  list_node_next mem node = list_node_next mem' node.
Proof.
  intros. gdep IN; dependent induction LLS; intro.
  - eassert (H:=only_null_in_null _ _ IN). contradiction.
  - destruct (N.eq_dec head NULL). subst; assert (t:=only_null_in_null _ _ IN); subst; constructor.
    destruct (N.eq_dec head node). subst. assumption.
    apply IHLLS; try easy.
    now apply node_in_tail.
Qed.

Theorem llsame_key_in:
  forall mem mem' head key loc
    (Key: key_in_linked_list mem head key loc)
    (LLS: LLSame mem mem' head),
  key_in_linked_list mem' head key loc.
Proof.
  intros mem mem' head key loc Key; gdep mem'; dependent induction Key.
  { intros. constructor; try easy. inversion LLS; now subst. }
  rename IHKey into IH.
  intros. move mem' before mem.
  apply KeyAtNext. assumption.
  replace (list_node_next mem' node) with (list_node_next mem node) by (inversion LLS; now subst).
  eapply llsame_value_neq; try eassumption. constructor.
  erewrite llsame_next_node with (mem':=mem); try eassumption.
  apply IH.
  inversion LLS; subst.
    simpl; constructor.
    assumption.
  eapply llsame_node_in; try eassumption. constructor.
  apply llsame_symmetry. assumption.
Qed.

Theorem noverlap_llbounds_shrink:
  forall mem head min max node w a2 len2
    (NNUL: node <> NULL)
    (LLB: LLBounds mem head min max)
    (IN: node_in_linked_list mem head node)
    (NOV: ~overlap w min (8+max) a2 len2),
  ~overlap w node 8 a2 len2.
Proof.
  intros. dependent induction IN; rename node into addr.
  inversion LLB; subst;[contradiction|].
  pose (addr-min) as i.
  replace addr with (min+i) by lia.
  eapply noverlap_index_l. eassumption. lia.

  inversion LLB; subst;[contradiction|]. apply IHIN; try easy.
Qed.

Theorem key_not_in_list:
  forall mem head key n nloc
    (NNUL: n <> NULL)
    (LAST: list_node_next mem n = NULL)
    (NLOC: node_distance mem head n nloc)
    (KLOC: forall kloc, key_in_linked_list mem head key kloc -> (nloc <= kloc)%nat)
    (NEQ: list_node_value mem n <> key),
  forall kloc, ~key_in_linked_list mem head key kloc.
Proof.
  intros. intro H. specialize (KLOC _ H).
  assert (H2:node_distance mem head NULL (S nloc)).
  {
    inversion H; subst.
    - rewrite <-Nat.add_1_r. apply node_distance_split with (m:=n); try easy.
      apply has_null_wf, node_in_linked_list_trans with (m:=n).
      eapply distance_imp_in; eassumption.
      1-2: constructor; try easy; rewrite LAST; constructor.
    - rewrite <-Nat.add_1_r. apply node_distance_split with (m:=n); try easy.
      apply has_null_wf, node_in_linked_list_trans with (m:=n).
      eapply distance_imp_in; eassumption.
      1-2: constructor; try easy; rewrite LAST; constructor.
  }
  assert (H3:=key_loc_lt_length _ _ _ _ _ H2 H).
  assert (H4:nloc = kloc) by lia; subst kloc; clear KLOC H3.
  assert (H5:=key_in_linked_list_value_equal _ _ _ _ _ H NLOC); symmetry in H5.
  contradiction.
Qed.

(* This is only true because the location of key is not unique,
  will have to change our reasoning for the key-found in linked list
  postcondition after changing the key_in_linked_list def. *)
Theorem key_at_node:
  forall mem head key node loc
    (Dist: node_distance mem head node loc)
    (NNul: node <> NULL)
    (Key: list_node_value mem node = key)
    (Min: forall i, key_in_linked_list mem head key i -> (loc <= i)%nat),
  key_in_linked_list mem head key loc.
Proof.
  intros mem head key node loc Dist; dependent induction Dist; intros.
  { constructor; try easy. }
  assert (NEQk: list_node_value mem src <> key). {
    intro.
    destruct (key_in_linked_list_dec mem src key 0). specialize (Min _ k); lia.
    apply n; constructor; try easy.
  }
  apply KeyAtNext; try easy.
  apply IHDist; try easy.
  intros.
  enough (H1:key_in_linked_list mem src key (S i)).
  specialize (Min (S i) H1); lia.
  apply KeyAtNext; try easy.
Qed.
  
Definition time_of_find_in_linked_list (mem : addr -> N) 
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


Definition find_in_linked_list_timing_invs (s : store) (base_mem : addr -> N)
    (sp : N) (head : addr) (key : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x10250 => Some (s V_MEM32 = Ⓜbase_mem /\ s R_SP = Ⓓsp /\
    s R_A0 = Ⓓhead /\ s R_A1 = Ⓓkey /\ 32 <= sp /\
    node_distance base_mem head NULL len /\
    LLBounds base_mem head 0 (sp ⊖ 32) /\
    cycle_count_of_trace t' = 0)
| 0x10278 => Some (exists ctr mem curr, s V_MEM32 = Ⓜmem /\ mem Ⓓ[sp ⊖ 20] = curr /\
    s R_S0 = Ⓓsp /\ mem Ⓓ[ msub 32 sp 24 ] = key/\ 32 <= sp /\ curr <> NULL /\
    node_distance mem head curr ctr /\
    node_distance mem head NULL len /\
    (ctr < len)%nat /\
    (head =? NULL) = false /\
    LLBounds base_mem head 0 (sp ⊖ 32) /\
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

Lemma Npos_P_of_succ_nat :
    forall n : nat, N.pos (Pos.of_succ_nat n) = N.succ (N.of_nat n).
Proof. lia. Qed.

Theorem find_in_linked_list_timing:
  forall s t s' x' base_mem sp head key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = Ⓜbase_mem)
         (SP: s R_SP = Ⓓsp)
         (A0: s R_A0 = Ⓓhead)
         (A1: s R_A1 = Ⓓkey)
         (* Bound list length to prevent difficult wrap around cases *)
         (SPLo: 32 <= sp)
         (LLB: LLBounds base_mem head 0 (sp ⊖ 32))
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
    Local Ltac step := time rv_step.
    Local Ltac llsame_solve :=
        repeat (psimpl 
                || assumption 
                || lia
                || apply noverlap_sum
                || solve [eapply llsame_same; eassumption]
                || apply noverlap_llsame 
                || solve [eapply llsame_bounds; eassumption]
                || lazymatch goal with
                   | [H: LLBounds _ _ ?lo ?hi |- _] => apply noverlap_llsame_trans with (min:=lo) (max:=hi)
                   end
                   || match goal with [H:LLSame ?ml ?mr ?a |- LLSame ?mr ?ml ?a] => rewrite llsame_symmetry; apply H end).

    simpl. rewrite ENTRY. unfold entry_addr. step. now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    (* 0x10250 -> 0x10278 *)
    destruct PRE as (Mem & SP & A0 & A1 & SPLo & Len & Bounds & Cycles).
    repeat step.
    (* 0x10278 *) {
        exists 0%nat. eexists. exists head.
        _noverlap_prepare.
        elimstore.
        repeat split; auto. now psimpl.
        now psimpl.
        now rewrite Bool.negb_true_iff, N.eqb_neq in BC0.
        constructor. apply llsame_distance with (mem:=base_mem); try easy; try llsame_solve.
        eauto using node_distance_len_nonzero. 
        now apply Bool.negb_true_iff.
        llsame_solve.
        lia.
        hammer.
    }

    (* head = NULL, contradiction because we checked at the start *)
    inversion BC.

    (* head = null, postcondition *)
    right. intros; split.
    apply Bool.negb_false_iff, N.eqb_eq in BC. subst. intro H; inversion H; subst; try contradiction.
    unfold time_of_find_in_linked_list, NULL.
    hammer.

    (* 0x10278 (66168)*)
    destruct PRE as (ctr & mem & curr & Mem & Curr & S0 & Key & SPLo & CurrNNull & Dist & Len &
        CtrLen & HeadNonNull & LLB & LLS & Fuel & Cycles).
    remember 0%nat as fuel; clear Heqfuel.
    step. step. step.
    step.
        { repeat step.
        (* next iteration *)
          exists (S ctr). _noverlap_prepare. rewrite Curr in *. remember (mem Ⓓ[ 4 + curr ]) as next.
          (* rewrite negb_true_iff, N.eqb_neq in *. *)
          assert (Heqnext':next = list_node_next mem curr). 
          { subst next; unfold list_node_next. destruct curr as [|p];[contradiction|reflexivity]. }
          assert (WF:=distance_null_imp_well_formed _ _ _ Len).
          assert (LenNext:node_distance mem head next (S ctr)). { rewrite Heqnext'; apply node_distance_next_S_len; try easy. }
          repeat eexists; psimpl; auto.
              { psimpl. rewrite N.mod_small by (subst; now apply getmem_bound).
                now rewrite Bool.negb_true_iff, N.eqb_neq in BC0. }
              { psimpl. rewrite N.mod_small by (subst; now apply getmem_bound).
                apply llsame_distance with (mem:=mem); try llsame_solve. }
              { apply llsame_distance with (mem:=mem). llsame_solve. assumption. }
              {
                destruct (Nat.lt_trichotomy (S ctr) len) as [Lt | [Eq | Gt]];[assumption | subst len; exfalso; clear CtrLen | lia ].
                  enough (Contra:node_distance mem head next (S ctr)).
                  assert (Help:=node_distance_uniq' _ _ _ _ _ _ Contra Len (eq_refl (S ctr))); now rewrite Help in BC0.
                  apply DstSn; try easy. eapply distance_imp_diff; eassumption.
                  now inversion LenNext.
                  now inversion LenNext.
              }
              llsame_solve.
              {
                rewrite Bool.negb_true_iff, N.eqb_neq in BC0, BC.
                rewrite Key in *.
                apply fuel_le_incr with (curr:=curr); try easy.
                apply llsame_distance with (mem:=mem); try easy; llsame_solve.
                intros fuel' KeyIn'. specialize (Fuel fuel').
                apply llsame_key_in with (mem':=mem) in KeyIn'. now specialize (Fuel KeyIn').
                apply llsame_symmetry; llsame_solve.
                unfold list_node_value. rewrite getmem_noverlap; try easy.
                (* continue here *)
                apply noverlap_shrink with (a1:=curr) (len1:=8); try lia.
                eapply noverlap_llbounds_shrink; try eassumption.
                eapply distance_imp_in.
                eapply llsame_distance; try eassumption. now apply llsame_symmetry.
                apply noverlap_sum; lia.
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
            destruct curr as [|p];[contradiction|remember (Npos p) as curr]. rewrite BC0 in Help2; specialize (Help2 (eq_refl 0)).
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
          rewrite Help2 in Key; unfold list_node_value in Key.
          contradiction.
          all: unfold msub; psimpl; reflexivity.
        }}
    (* The key does NOT exist in the linked list, we've reached the end. *) {
      elimstore; right; intro.
          move curr before sp; move n before sp; move ctr before len; move s' before s; move fuel before len.
          move SBound before Mem; move SBound0 before Mem.
          move BC at bottom; move LLB before SPLo; move LLS before LLB; move Cycles before t; move MDL after Cycles; move ENTRY before t.
          move CtrLen before SPLo; move CurrNNull before CtrLen; move HeadNonNull before CurrNNull.
          move loc before ctr.
          assert (BC0':=BC0); assert (BC':=BC); move BC0 at bottom; move BC0' before MDL; move BC' before MDL.
          rewrite Bool.negb_true_iff, N.eqb_neq in BC; rewrite Bool.negb_false_iff, N.eqb_eq in BC0.
          replace (mem Ⓓ[ 4294967272 + sp ]) with (mem Ⓓ[ msub 32 sp 24 ]) in BC.
          replace (mem Ⓓ[ 4294967276 + sp ]) with (mem Ⓓ[ msub 32 sp 20 ]) in BC, BC0.
          all: try (unfold msub; psimpl; reflexivity).
          rewrite Curr, Key in BC; rewrite Curr in BC0.
          split.
          intro H; apply (llsame_key_in _ mem) in H; revert H.
          gdep loc; eapply key_not_in_list; try eassumption.
          destruct curr;[contradiction|]; now unfold list_node_next.
          now unfold list_node_value.
          now intro.
          enough (Help: len = S ctr). subst len.
          unfold time_of_find_in_linked_list; hammer.
          assert (Help2: list_node_next mem curr = NULL) by (destruct curr;[contradiction| now unfold list_node_next]).
          assert (Help:=distance_last_node _ _ _ _ CurrNNull Dist Help2).
          (* why does `destruct Help` introduce the `len=0` goal? *)
          eapply node_distance_uniq; try eassumption.
        }
    }

      (* Found key at curr node *)
      repeat step.
      elimstore.
          move curr before sp; move n before sp; move ctr before len; move s' before s; move fuel before len.
          move SBound before Mem; move SBound0 before Mem.
          move BC at bottom; move LLB before SPLo; move LLS before LLB; move Cycles before t; move MDL after Cycles; move ENTRY before t.
          move CtrLen before SPLo; move CurrNNull before CtrLen; move HeadNonNull before CurrNNull.
          assert (BC':=BC); move BC' before MDL; rewrite Bool.negb_false_iff, N.eqb_eq in BC.
          replace (mem Ⓓ[ 4294967272 + sp ]) with (mem Ⓓ[ msub 32 sp 24 ]) in BC.
          replace (mem Ⓓ[ 4294967276 + sp ]) with (mem Ⓓ[ msub 32 sp 20 ]) in BC.
          all: try (unfold msub; psimpl; reflexivity).
          rewrite Curr, Key in BC.
          rename ctr into loc.
          left; exists loc; split.
          apply llsame_key_in with (mem:=mem).
          eapply key_at_node; try eassumption. destruct curr;[contradiction|symmetry; now unfold list_node_value].
          now rewrite llsame_symmetry.
          unfold time_of_find_in_linked_list; hammer.
Qed.
