Require Import NArith ZArith Bool Coq.Lists.List.
Require Import Lia ZifyBool ZifyN.
Require Import -(notations) arm7_cfi2.
Require Import Picinae_armv7.
Require Import Lia ZifyN ZifyNat.
Import ARM7Notations.
Import ListNotations.
Require Import Nat.

Open Scope N.

Lemma GOTO_correct:
  forall c s l src dest c' s' x i,
    src < 2^30 ->
    dest < 2^30 ->
    GOTO l 14 (Z.of_N src) (Z.of_N dest) = Some i ->
    exec_stmt c s (arm2il (src * 4) i) c' s' x ->
    x = Some (Addr (dest * 4)).
Proof.
  intros c s l src dest c' s' x i S D G. intros.
  cbv [GOTO] in G. destruct orb eqn:e in G; try discriminate.
  remember (_ - _ - _)%Z as offset. unfold Z2 in *.
  assert (src * 4 ⊕ 8 ⊕ scast 26 32 (Z.to_N (offset mod 16777216) << 2) .& 4294967292 = dest * 4).
  {
    change 2 with (Z.to_N 2) at 2. rewrite <- Z2N_inj_shiftl, Z.shiftl_mul_pow2, <- Zmult_mod_distr_r by lia.
    change (Z.to_N _) with (ofZ 26 (offset * 4)).
    unfold scast. rewrite toZ_ofZ by (unfold signed_range; cbn; lia). unfold ofZ.
    rewrite <- (N2Z.id ((_ + 8) mod _)), <- Z2N.inj_add, N2Z.inj_mod, <- (N2Z.id (_ ^ _)), <- Z2N.inj_mod, <- Zplus_mod by lia.
    replace (_ + _ * 4)%Z with (Z.of_N (dest * 4)) by lia.
    rewrite Z2N.inj_mod, 2 N2Z.id, N_land_mod_pow2_move by lia.
    change (_ mod _) with (N.lnot (2 * (2 * 0 + 1) + 1) 32).
    rewrite <- N.ldiff_land_low, 2 N.ldiff_odd_r, N.ldiff_0_r. lia.
    destruct (dest * 4) eqn:E; now try solve [apply N.log2_lt_pow2; lia].
  }
  destruct l; inversion G; subst; cbv [arm2il arm_bl_il arm_b_il] in H;
    remember (scast _ _ _) as dsta; remember (src * 4) as srca;
    step_stmt H; destruct H as [[_ A] _]; inversion A; now rewrite H0.
Qed.

Lemma GOTOz_correct:
  forall c s l src dest c' s' x z,
    src < 2^30 ->
    dest < 2^30 ->
    GOTOz l 14 (Z.of_N src) (Z.of_N dest) = Some z ->
    exec_stmt c s (arm2il (src * 4) (arm_decode z)) c' s' x ->
    x = Some (Addr (dest * 4)).
Proof.
  intros. unfold GOTOz in H1. destruct GOTO eqn:e in H1; try discriminate. apply arm_assemble_eq in H1. rewrite H1 in H2.
  now apply (GOTO_correct c s l src dest c' s' x a).
Qed.

Open Scope nat.

Definition to_a := Z.mul 4.
Definition i2a' i2i' (i: Z) := to_a (i2i' i).
Definition compute_table_size sr := Z.to_nat (2 ^ (32 - sr)).
Definition compute_table_start_index tbi ti := Z.to_nat (ti - tbi).
Definition SafeEntry i2i' (pol: Z -> list Z) ai si a :=
  to_a ai = a \/ exists di (D: i2a' i2i' di = a), In di (pol si).
Definition InBlock i2i' i ilen da' :=
  (i2a' i2i' i <= Z.of_N da' /\ Z.of_N da' < i2a' i2i' i + 4 * Z.of_nat ilen /\ N.divide 4 da')%Z.
Definition SafeDest i2i' pol ai si ilen a :=
  SafeEntry i2i' pol ai si (Z.of_N a) \/ InBlock i2i' si ilen a.
Definition InBlockXs i2i' i ilen (xs: exit * ARM7Arch.store) :=
  match xs with
  | (Addr a, _) => InBlock i2i' i ilen a
  | _ => False
  end.
Definition ContainsBlock i2i' i (p: program) s block :=
  forall a, InBlock i2i' i (length block) a ->
    match nth_error block (N.to_nat (N.shiftr a 2) - Z.to_nat (i2i' i)) with
    | Some z => p s a = Some (4%N, arm2il a (arm_decode z))
    | _ => False
    end.
Definition SafeTable i2i' pol ai si table :=
  Forall (SafeEntry i2i' pol ai si) table.
Definition extract_table sr tbi ti (flattened_tables: list Z) :=
  let si := compute_table_start_index tbi ti in
  let ts := compute_table_size sr in
  let table := firstn ts (skipn si flattened_tables) in
  if (si + ts <=? length flattened_tables) && (tbi <=? ti)%Z then Some table else None.
Definition SafeTableCache i2i' pol ai tbi (flattened_tables: list Z) (tc: TableCache) :=
  forall si ti sl sr
    (TC: tc (pol si) = Some (ti, sl, sr)),
    exists table, extract_table sr tbi ti flattened_tables = Some table /\ SafeTable i2i' pol ai si table.

Ltac destruct_match_in H :=
  repeat match type of H with context[match ?x with _ => _ end] =>
    let e := fresh "e" in
    destruct x eqn:e in H
  end.

Lemma table_size_correctness:
  forall sr tbi ti flattened_tables t
    (T: extract_table sr tbi ti flattened_tables = Some t),
    length t = compute_table_size sr.
Proof.
  intros. unfold extract_table in T. destruct_match_in T; try discriminate.
  inversion T. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma extracttable_app_r:
  forall sr tbi ti flattened_tables table t
    (T: extract_table sr tbi ti flattened_tables = Some table),
    extract_table sr tbi ti (flattened_tables++t) = Some table.
Proof.
  intros. unfold extract_table in T. destruct andb eqn:e in T; try discriminate. apply andb_prop in e.
    inversion T; clear T; subst.
    unfold extract_table. destruct andb eqn:e1.
      rewrite 2 firstn_skipn_comm, firstn_app.
        remember (_ + _ - _) as n; assert (n = 0) by lia.
        now rewrite H, firstn_O, app_nil_r.
      rewrite length_app in e1. lia.
Qed.

Lemma extracttable_after:
  forall sr tbi flattened_tables t
    (T: length t = compute_table_size sr),
    extract_table sr tbi (tbi + Z.of_nat (length flattened_tables)) (flattened_tables++t) = Some t.
Proof.
  intros. unfold extract_table, compute_table_start_index.
  rewrite length_app, T, Z.add_simpl_l, Nat2Z.id, Nat.leb_refl.
  remember (Z.leb _ _) as b; assert (b = true) by lia; rewrite H.
  now rewrite skipn_app, skipn_all, Nat.sub_diag, skipn_O, <- T, firstn_all.
Qed.

Lemma safetablecache_app_r:
  forall t tc i2i' pol ai tbi flattened_tables,
    SafeTableCache i2i' pol ai tbi flattened_tables tc ->
    SafeTableCache i2i' pol ai tbi (flattened_tables++t) tc.
Proof.
  unfold SafeTableCache. intros. specialize (H si ti sl sr TC). inversion H. exists x. now erewrite extracttable_app_r.
Qed.

Lemma Forall_map2list:
  forall P m n (H: forall a, P (m a)),
    Forall P (_map2list m n).
Proof.
  intros. induction n. constructor. simpl. now constructor.
Qed.

Lemma make_jump_table_size:
  forall dis dis' ai sl sr n,
    length (make_jump_table dis dis' ai sl sr (Z.of_nat n)) = n.
Proof.
  intros. unfold make_jump_table. rewrite length_rev, map2list_fix, Nat2Z.id. induction n.
    reflexivity.
    cbn [_map2list]. now rewrite length_cons, IHn.
Qed.

Lemma make_jump_table_map_safety:
  forall ai dis i2i' sl sr x,
    In (make_jump_table_map dis (map i2i' dis) sl sr (fun _ => to_a ai) x) (to_a ai::map (i2a' i2i') dis).
Proof.
  intros. induction dis.
    now left.
    cbn [make_jump_table_map map]. destruct orb.
      right. now left.
      inversion IHdis.
        now left.
        right. now right.
Qed.

Lemma safeentry_in:
  forall ai pol i2i' i x,
    In x (to_a ai::map (i2a' i2i') (pol i)) ->
    SafeEntry i2i' pol ai i x.
Proof.
  intros. inversion H.
    now left.
    right. apply in_map_iff in H0. inversion H0. now exists x0.
Qed.

Lemma list_eqb_eq:
  forall a b, list_eqb a b = true <-> a = b.
Proof.
  induction a.
    split; now destruct b.
    split; simpl; intro; destruct b; try easy.
      destruct Z.eqb eqn:e in H; try easy. rewrite IHa in H. apply Z.eqb_eq in e. now subst.
      destruct Z.eqb eqn:e. rewrite IHa. now inversion H. inversion H. apply Z.eqb_neq in e. easy.
Qed.

Lemma rewrite_w_table_safety:
  forall irm tc pol i2i' cond z i ti ai z' table tc'
    (RWT: rewrite_w_table irm tc (pol i) i2i' cond z i ti ai = Some (z', table, tc')),
    SafeTable i2i' pol ai i table.
Proof.
  intros. unfold rewrite_w_table in RWT. destruct_match_in RWT; try discriminate.
    inversion RWT; subst. apply Forall_nil.
    remember (Z.shiftl _ _). inversion RWT. apply Forall_rev. rewrite map2list_fix. apply Forall_map2list.
      intro. apply safeentry_in, make_jump_table_map_safety.
Qed.

Lemma rewrite_w_table_cache_safety:
  forall tbi flattened_tables irm tc pol i2i' cond z i ti ai z' table tc'
    (STC: SafeTableCache i2i' pol ai tbi flattened_tables tc)
    (TI: (ti = tbi + Z.of_nat (length flattened_tables))%Z)
    (RWT: rewrite_w_table irm tc (pol i) i2i' cond z i ti ai = Some (z', table, tc')),
    SafeTableCache i2i' pol ai tbi (flattened_tables ++ table) tc'.
Proof.
  intros. eapply rewrite_w_table_safety in RWT as ST. unfold rewrite_w_table in RWT.
  destruct_match_in RWT; try discriminate.
    inversion RWT; subst; now rewrite app_nil_r.
    remember (Z.shiftl _ _). inversion RWT; subst; clear RWT. unfold SafeTableCache. intros. destruct list_eqb eqn:E.
      remember (make_jump_table _ _ _ _ _ _) as t. exists t. inversion TC; subst. split.
        apply extracttable_after.
          rewrite <- (Z2Nat.id (Z.shiftl _ _)), make_jump_table_size, Z.shiftl_1_l; now try apply Z.shiftl_nonneg.
        apply list_eqb_eq in E. unfold SafeTable, SafeEntry. now rewrite E.
      eapply STC in TC. inversion TC. exists x. split; now try apply extracttable_app_r.
Qed.

Lemma rewrite_inst_safety:
  forall tc i2i' z pol i ti ai bi txt z' table tc'
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (z', table, tc')),
    SafeTable i2i' pol ai i table.
Proof.
  assert (forall i' ai tc a b c, goto_abort i' ai tc = Some (a, b, c) -> b = nil).
    unfold goto_abort. intros. destruct GOTOz eqn:e in H; now inversion H.
  assert (forall x tc a b c, wo_table x tc = Some (a, b, c) -> b = nil).
    unfold wo_table. intros. destruct x in H0; now inversion H0.
  assert (forall l cond imm24 i dis i2i' ai tc a b c, rewrite_b_bl l cond imm24 i dis i2i' ai tc = Some (a, b, c) -> b = nil).
    unfold rewrite_b_bl. intros. destruct_match_in H1; now inversion H1.

  intros. unfold rewrite_inst in RI. destruct_match_in RI;
    try solve [first [apply H in RI|apply H0 in RI|apply H1 in RI|inversion RI]; subst; constructor];
    now apply rewrite_w_table_safety in RI.
Qed.

Lemma rewrite_inst_cache_safety:
  forall tc i2i' z pol i ti ai bi txt z' table tc' tbi flattened_tables
    (STC: SafeTableCache i2i' pol ai tbi flattened_tables tc)
    (TI: (tbi + Z.of_nat (length flattened_tables) = ti)%Z)
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (z', table, tc')),
    SafeTableCache i2i' pol ai tbi (flattened_tables ++ table) tc'.
Proof.
  assert (forall i' ai tc a b c, goto_abort i' ai tc = Some (a, b, c) -> c = tc).
    unfold goto_abort. intros. destruct GOTOz eqn:e in H; now inversion H.
  assert (forall x tc a b c, wo_table x tc = Some (a, b, c) -> c = tc).
    unfold wo_table. intros. destruct x in H0; now inversion H0.
  assert (forall l cond imm24 i dis i2i' ai tc a b c, rewrite_b_bl l cond imm24 i dis i2i' ai tc = Some (a, b, c) -> c = tc).
    unfold rewrite_b_bl. intros. destruct_match_in H1; now inversion H1.

  intros. unfold rewrite_inst in RI. destruct_match_in RI;
    try solve [first [apply H in RI|apply H0 in RI|apply H1 in RI|inversion RI]; subst; now apply safetablecache_app_r];
    eapply rewrite_w_table_cache_safety in RI; now try apply RI.
Qed.

Lemma _rewrite_cache_safety:
  forall zs tc pol i2i' i ti ai bi txt z's ts tc' t
    (RR: _rewrite zs tc pol i2i' i (ti + Z.of_nat (length t)) ai bi txt = Some (z's, ts, tc')),
    SafeTableCache i2i' pol ai ti t tc ->
    SafeTableCache i2i' pol ai ti (t++concat ts) tc'.
Proof.
  induction zs.
    intros. simpl in RR; inversion RR; subst. now rewrite concat_nil, app_nil_r.
    intros. simpl in RR; destruct_match_in RR; try discriminate; inversion RR; subst.
      simpl. rewrite app_assoc. eapply IHzs.
        now rewrite length_app, Nat2Z.inj_add, Z.add_assoc, e2.
        eapply rewrite_inst_cache_safety in e; now try apply e.
Qed.

Lemma _rewrite_cache_safety2:
  forall zs pol i2i' i ti ai bi txt z's ts tc'
    (RR: _rewrite zs (fun _ => None) pol i2i' i ti ai bi txt = Some (z's, ts, tc')),
    SafeTableCache i2i' pol ai ti (concat ts) tc'.
Proof.
  intros. rewrite <- (app_nil_l (concat _)). eapply _rewrite_cache_safety.
    rewrite Z.add_0_r. apply RR.
    discriminate.
Qed.

Lemma firstinst:
  forall i2i' i p s z t
    (CB: ContainsBlock i2i' i p s (z::t))
    (Z: (0 <= i2i' i)%Z),
    p s (Z.to_N (i2a' i2i' i)) = Some (4%N, arm2il (Z.to_N (i2a' i2i' i)) (arm_decode z)).
Proof.
  intros. remember (Z.to_N _) as a. specialize (CB a). cbn in CB. remember (_ - _). unfold i2a', to_a in *. assert (n = 0) by lia. rewrite H in CB. cbn in CB.
  apply CB. unfold InBlock. unfold i2a', to_a. rewrite Heqa, Z2N.id. repeat split. lia. lia. exists (Z.to_N (i2i' i)). lia. lia.
Qed.

Fixpoint mylast {A:Type} (l:list A) d :=
  match l with
  | [] => d
  | [a] => a
  | a:: (_::_) as l0 => mylast l0 a
  end.

Theorem last_rm_h {A:Type}:
  forall (l:list A) h h' d, last (h::h'::l) d = last (h'::l) d.
Proof.
  induction l; try reflexivity; intros.
Qed.

Theorem last_d_d' {A:Type}:
  forall (l:list A) h d d', last (h::l) d = last (h::l) d'.
Proof.
  induction l. reflexivity.
  intros.
  rewrite! last_rm_h. apply IHl.
Qed.

Theorem mylast_last {A:Type} :
  forall (l:list A) d, mylast l d = last l d.
Proof.
  induction l. reflexivity.
  intros. destruct l. reflexivity.
  simpl.  match goal with |- ?f = _ => assert (f = mylast (a0::l) a) by reflexivity end.
  rewrite H. rewrite IHl. rewrite last_d_d' with (d':= d).
  reflexivity.
Qed.

Theorem mylast_unfold {A:Type}:
  forall (t:list A) a d, mylast (a::t) d = mylast t a.
Proof.
  destruct t; reflexivity.
Qed.

Theorem last_unfold {A:Type}:
  forall (t:list A) a d, last (a::t) d = last t a.
Proof.
  intros. rewrite <-!mylast_last. apply mylast_unfold.
Qed.

Theorem last_in_list {A}:
  forall (t:list A) h, In (last t h) (h::t).
Proof.
  induction t. simpl; now constructor.
  intros. unfold In in *. right.
  rewrite last_unfold. apply IHt.
Qed.

Lemma single_element:
  forall A (a: A) b c,
    [a] = b ++ [c] ->
    a = c.
Proof.
  intros. destruct b. simpl in H. now inversion H. simpl in H. inversion H. simpl in H2. now apply app_cons_not_nil in H2.
Qed.

Lemma SafeDest_rewrite_inst:
  forall tc i2i' z pol i ti ai bi txt irm' table tc' p a' s' s1 t1 t0
    (TC: True) (* table cache is consistent with memory *)
    (AI: (0 <= ai < 2^30)%Z)
    (TI: (0 <= ti < 2^30)%Z)
    (I:  (0 <=  i < 2^30)%Z)
    (BI: (0 <= bi < 2^30)%Z)
    (I2I': forall i, (0 <= i2i' i < 2^30)%Z)
    (AIB: ~InBlock i2i' i (length irm') (Z.to_N ai * 4))
    (CB: ContainsBlock i2i' i p s1 irm')
    (IB: Forall (InBlockXs i2i' i (length irm')) t1)
    (XP: exec_prog p ((Addr a', s')::t1++(Addr (Z.to_N (i2a' i2i' i)), s1)::t0))
    (RI: rewrite_inst tc i2i' z (pol i) i ti ai bi txt = Some (irm', table, tc')),
  SafeDest i2i' pol ai i (length irm') a'.
Proof.
  intros.
  assert (goto_abort (i2i' i) ai tc = Some (irm', table, tc') -> SafeDest i2i' pol ai i (length irm') a') as GA.
  {
    unfold goto_abort. intro GA; destruct_match_in GA; try discriminate.
    inversion GA; subst; clear GA.

    rewrite app_comm_cons in XP. remember (_ :: t1) as l. destruct (rev_destruct l). subst; discriminate.
    inversion e0 as [t2 H]; clear e0; subst. inversion H as [(x, s) H0]; clear H; simpl in H0.
    unfold exec_prog in XP.
    rewrite H0, <- app_assoc, stepsof_app, 2 Forall_app in XP. destruct XP as [_ [_ XP]].
    inversion XP; clear XP H1 H3; subst. inversion H2; clear H2.

    apply firstinst in CB; try apply I2I'. rewrite CB in LU. inversion LU; clear LU. subst.
    unfold i2a', to_a in XS. rewrite Z.mul_comm, Z2N.inj_mul in XS by (apply I2I' || lia).
    remember (Z.to_N (i2i' i)) as src.
    rewrite <-(Z2N.id (i2i' i)) in e by (apply I2I'; lia). rewrite <-Heqsrc in e.
    rewrite <-(Z2N.id ai) in e by lia.
    epose proof (GOTOz_correct _ _ _ _ _ _ _ _ _ _ _ e XS).
    Unshelve.
    all: try lia.
    2: { rewrite Heqsrc. specialize (I2I' i). lia. }
    subst.

    simpl in H0. destruct t1.
      apply single_element in H0. inversion H0. left. left. unfold to_a; lia.
      destruct (exists_last (ltac:(discriminate):p0::t1<>[])) as [? [? ?]].
        rewrite e0, app_comm_cons, app_inj_tail_iff in H0. destruct H0. subst.
        rewrite e0, Forall_app in IB. destruct IB. now inversion H0.
  }
 unfold rewrite_inst in RI. destruct_match_in RI; try discriminate;
  match type of RI with context[goto_abort] => now apply GA
  | _ => clear GA
  end.

(** Definitions for reasoning about the locations in memory and sizes of
    jumptable entries. *)
Section JTAbstractions.
Local Definition jtT := list (list Z).
Fixpoint _block_of (i:nat) (lengths:list nat) : option nat :=
  match lengths with
  | l::t => if (i <? l)%nat then Some O else
      match _block_of (Nat.sub i l) t with
      | Some i' => Some (S i')
      | _ => None
      end
  | _ => None
  end.

Definition block_of (a:addr) (p:list (list Z)) ti : option nat :=
  let lengths := map (@length Z) p in
  let i := (msub 32 a (4*ti)) >> 2 in
  _block_of (N.to_nat i) lengths.

Definition jt_section jt a ti : option (N * nat) :=
  match block_of a jt ti with
  | Some i =>
      let entry_start := List.fold_left Nat.add
        (List.firstn i (List.map (@length Z) jt)) O in
      Some (4*(ti + (N.of_nat entry_start)), length (List.nth i jt []))
  | None => None
  end.

Fixpoint block_start {A:Set} (i:nat) (ls:list (list A)) :=
  match ls with
  | [] => false
  | l::t =>
      match i, length l with
      | O, S _ => true
      | _, O => block_start i t
      | S _, S _ => 
          if (i <? length l)%nat
          then false
          else block_start (Nat.sub i (length l)) t
      end
  end.
Section JTAbstractions.

(** Definitions for reasoning about the jumptable in memory. *)
Section DataDefinitions.
  (* Concatenate bits, but for Z *)
  Definition czbits (z1:Z) i (z2:Z) := Z.lor (Z.shiftl z1 (Z.of_N i)) z2.

  (* Concatenates a `list Z` of 32-bit numbers into a single number.  Returns
    the value, bitwidth pair. *)
  Definition czlist zs : Z * bitwidth := List.fold_left
    (fun '(zacc,bits_written) z => (czbits z bits_written zacc, 32+bits_written))
    zs (Z0,0).

  (* Concatenates the `list (list Z)` rewritten program into its value in memory. *)
  Definition czslist zss : Z * bitwidth :=
    List.fold_left 
    (fun '(zacc,bits_written) zs => 
      match czlist zs with
      | (z,bits) => (czbits z bits_written zacc, bits+bits_written)
      end)
    zss (Z0,0).

  Definition flatten {A:Type} (ls:list (list A)) :=
    List.fold_left (fun acc l => l++acc) ls [].
End DataDefinitions.

(* Questions:

  1. Can we abstract away from quantifying over the specific program
      and the output of the rewriter? 

  2. How will we instantiate or define the "f" address translation function? *)

(* Simplifying assumptions:

    1. Each instruction that needs a jump table has an entry in the jump table
        at the index of the instruction.  This is not true because of a rewriter
        optimization that elides duplicate table entries.  I hope we can use a
        trick to reason about this simplified version. 
    2. We assume the jump table is read from an index less than its size.  We
        leave it up to the master theorem to prove the contents of the register
        jump-target corresponds to this offset. *)


Theorem jt_safe_jmp:
  forall jt a1 base offset size mem pol zs i i' ti ai f zs'
    (* Add bounds to the Z values for clarity; they get converted to N below. *)
    (TI: (ti >= 0)%Z)
    (A1: (a1 >= 0)%Z)

    (* Tie the output of the rewriter to the rewritten instructions and jumptable. *)
    (RR: rewrite pol zs i i' ti ai = Some(zs', jt) )

    (* Two ideas for formulating the "jumptable stored in memory" hypothesis
       1. use xbits to talk about the values of bits of memory. This won't work
          if the jumptable wraps around the end of memory.
       2. axiomatize the value of aligned reads from the jumptable. *)
    (DATA: match czslist zs' with
           | (jtbits, bits) => xnbits mem (Z.to_N ti) bits = (Z.to_N jtbits)
           end)
    (DATA2: forall i, (i < length (flatten jt))%nat ->
            mem Ⓓ[4*((Z.to_N ti) + (N.of_nat i))] =  Z.to_N (nth i (flatten jt) Z0))

    (* We do not have this "f" function for translating old addresses to new,
       so we axiomatize its important properties:
          1. it maps addresses from the initial code section to addresses in the
             new code, preserving the block index and
          2. the new address is the start of its block *)
    (F: forall z z' (ZLT:z < N.of_nat (length zs)),
        block_of (f (4*(Z.to_N i+z))) zs' (Z.to_N i') = Some z'
        /\ block_start z' zs' = true)

    (* The section of the jump table corresponding to the address a1 has some base
       and size *)
    (SECN: jt_section jt (Z.to_N a1) (Z.to_N ti) = Some (base, size))
    (OFFLT: (offset < size)%nat),
    exists a2, mem Ⓓ[base + 4*(N.of_nat offset)] = f a2
              /\ In (Z.of_N a2) (pol a1).
Proof.
  intros; move mem after offset; move a1 after zs; move zs' before jt.
  (* Simplify RR *)
  unfold rewrite in RR;
  destruct (_rewrite _ _ _ _ _ _ _ _ _) eqn:_rr ;[|discriminate].
  (* Simplify SECN *)
  unfold jt_section in SECN;
  destruct (block_of (Z.to_N a1) jt (Z.to_N ti)) eqn:block_of_jt;[|discriminate];
  symmetry in SECN; inversion SECN as [[BASE LEN]]; rewrite <-BASE;
  assert (BASE':base=4*((Z.to_N ti)+(N.of_nat (fold_left Nat.add (firstn n (map (length (A:=Z)) jt)) 0%nat)))) by (subst;reflexivity);
  clear SECN BASE; rename BASE' into BASE.

  eexists; split.
