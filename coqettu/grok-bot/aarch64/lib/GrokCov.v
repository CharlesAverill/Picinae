(* GrokCov: copy-coverage predicate for loop-based copies (memcpy n > 128).
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lib Require Import GrokStr GrokFrame GrokFill GrokMem GrokCopy.
Import ARM8Notations.
Open Scope N.

(* M agrees with a copy of n bytes src -> d on the offsets in C, and with mem outside [d, d+n) *)
Definition cov (mem M : memory) (s d n : N) (C : N -> Prop) :=
  (∀ i, i < n -> C i -> M Ⓑ[d + i] = mem Ⓑ[s + i]) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = mem Ⓑ[a]).

Lemma cov_init: ∀ mem s d n, cov mem mem s d n (fun _ => False).
Proof. intros. split; intros; [contradiction | reflexivity]. Qed.

Lemma cov_mono: ∀ mem M s d n (C C' : N -> Prop), cov mem M s d n C ->
  (∀ i, i < n -> C' i -> C i) -> cov mem M s d n C'.
Proof. intros mem M s d n C C' [H1 H2] H. split; [intros i I Ci; apply H1; auto | exact H2]. Qed.

Lemma cov_store8: ∀ mem M s d n C j, cov mem M s d n C -> j + 8 <= n -> d + n < 2^64 ->
  cov mem (setmem 64 LittleE 8 M (d + j) (mem Ⓠ[s + j])) s d n (fun i => C i \/ (j <= i /\ i < j + 8)).
Proof.
  intros mem M s d n C j [H1 H2] J D. split.
  - intros i I Ci.
    assert (W: (d + j <= d + i /\ d + i < d + j + 8) \/ (d + i < d + j \/ d + j + 8 <= d + i)) by lia.
    destruct W as [[W1 W2]|W].
    + rewrite read_in by (change (2^64) with 18446744073709551616 in *; lia).
      rewrite byte_getmem by lia. apply (f_equal (getmem 64 LittleE 1 mem)). lia.
    + rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia).
      apply H1; [exact I|]. destruct Ci as [Ci|Ci]; [exact Ci | exfalso; lia].
  - intros a A O. rewrite read_out by (change (2^64) with 18446744073709551616 in *; lia). apply H2; assumption.
Qed.

Lemma cov_copied: ∀ mem M s d n C, cov mem M s d n C -> (∀ i, i < n -> C i) ->
  (∀ i, i < n -> M Ⓑ[d + i] = mem Ⓑ[s + i]) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = mem Ⓑ[a]).
Proof. intros mem M s d n C [H1 H2] H. split; [intros i I; apply H1; auto | exact H2]. Qed.

(* source reads are unaffected when the buffers are disjoint *)
Lemma cov_src: ∀ mem M s d n C j len, cov mem M s d n C -> d + n < 2^64 -> s + n < 2^64 ->
  (s + n <= d \/ d + n <= s) -> j + len <= n ->
  getmem 64 LittleE len M (s + j) = getmem 64 LittleE len mem (s + j).
Proof.
  intros mem M s d n C j len [_ H2] D S X J. apply getmem_ext. intros k K.
  apply H2; lia.
Qed.

Lemma land15: ∀ d, N.land d 15 = d mod 16.
Proof. intro d. change 15 with (N.ones 4). rewrite N.land_ones. reflexivity. Qed.

Lemma cov_store8': ∀ mem M s d n C j b v, cov mem M s d n C -> b = d + j -> v = mem Ⓠ[s + j] ->
  j + 8 <= n -> d + n < 2^64 ->
  cov mem (setmem 64 LittleE 8 M b v) s d n (fun i => C i \/ (j <= i /\ i < j + 8)).
Proof. intros. subst b v. apply cov_store8; assumption. Qed.

Lemma cov_src': ∀ mem M s d n C a len, cov mem M s d n C -> d + n < 2^64 -> s + n < 2^64 ->
  (s + n <= d \/ d + n <= s) -> s <= a -> a + len <= s + n ->
  getmem 64 LittleE len M a = getmem 64 LittleE len mem a.
Proof.
  intros. replace a with (s + (a - s)) by lia. eapply cov_src; try eassumption. lia.
Qed.

Lemma msub64_small': ∀ x k, k <= x -> x < 2^64 -> msub 64 x k = x - k.
Proof.
  intros x k H1 H2. unfold msub. rewrite (N.mod_small k) by lia.
  replace (x + (2^64 - k)) with ((x - k) + 1 * 2^64) by lia.
  rewrite N.mod_add by discriminate. apply N.mod_small. lia.
Qed.

Lemma land_m16': ∀ d, d < 2^64 -> N.land d 18446744073709551600 = d - d mod 16.
Proof.
  intros d D.
  replace (d - d mod 16) with (N.shiftl (N.shiftr d 4) 4).
  - rewrite <- N.ldiff_ones_r. apply N.bits_inj. intro k.
    rewrite N.land_spec, N.ldiff_spec.
    replace 18446744073709551600 with (N.ldiff (N.ones 64) (N.ones 4)) by reflexivity.
    rewrite N.ldiff_spec.
    destruct (N.lt_ge_cases k 64) as [K|K].
    + rewrite (N.ones_spec_low 64 k K). destruct (N.testbit d k), (N.testbit (N.ones 4) k); reflexivity.
    + rewrite (N.ones_spec_high 64 k) by lia.
      replace (N.testbit d k) with false; [reflexivity|].
      symmetry. apply (N.bits_above_log2 d k). destruct (N.eq_dec d 0) as [->|NZ]; [simpl; lia|].
      apply N.log2_lt_pow2; [lia | apply N.lt_le_trans with (2^64); [exact D | apply N.pow_le_mono_r; lia]].
  - rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. pose proof (N.div_mod d 16 ltac:(discriminate)).
    change (2^4) with 16. lia.
Qed.

Ltac upd_simpl := repeat first [ rewrite update_updated | rewrite update_frame by discriminate ].

Ltac num_norm :=
  change (2^64) with 18446744073709551616 in *;
  repeat match goal with
  | |- context [(?x + ?y) mod 18446744073709551616] => rewrite (N.mod_small (x + y)) by lia
  | |- context [msub 64 ?x ?k] => rewrite (msub64_small' x k) by (change (2^64) with 18446744073709551616; lia)
  end;
  repeat match goal with
  | H: context [(?x + ?y) mod 18446744073709551616] |- _ => rewrite (N.mod_small (x + y)) in H by lia
  | H: context [msub 64 ?x ?k] |- _ => rewrite (msub64_small' x k) in H by (change (2^64) with 18446744073709551616; lia)
  end.

(* reads of source bytes through dest stores *)
Ltac src_read COV :=
  repeat first [ rewrite getmem_setmem_above by (change (2^64) with 18446744073709551616 in *; lia)
               | rewrite getmem_setmem_below by (change (2^64) with 18446744073709551616 in *; lia) ];
  repeat (erewrite (cov_src' _ _ _ _ _ _ _ _ COV) by (change (2^64) with 18446744073709551616 in *; lia)).

Ltac src_read0 :=
  repeat first [ rewrite getmem_setmem_above by (change (2^64) with 18446744073709551616 in *; lia)
               | rewrite getmem_setmem_below by (change (2^64) with 18446744073709551616 in *; lia) ].

Ltac cov_peel :=
  repeat match goal with |- cov ?mem (setmem 64 LittleE 8 ?M ?b ?v) ?s ?d ?n _ =>
    eapply (cov_store8' mem M s d n _ (b - d) b v);
    [ | lia | apply (f_equal (getmem 64 LittleE 8 mem)); lia | lia | lia ] end.

Ltac pow_lits_g := repeat match goal with |- context [2 ^ ?k] =>
  let v := eval compute in (2 ^ k) in change (2 ^ k) with v end.

Ltac lor_absurd := exfalso; match goal with H: N.lor _ _ = _ |- _ => vm_compute in H; discriminate H end.

(* prefix form: avoids disjunction blow-up in lia *)
Lemma cov_init0: ∀ mem s d n, cov mem mem s d n (fun i => i < 0).
Proof. intros. split; intros; [lia | reflexivity]. Qed.

Lemma cov_store8m: ∀ mem M s d n P j b v, cov mem M s d n (fun i => i < P) -> b = d + j -> v = mem Ⓠ[s + j] ->
  j <= P -> j + 8 <= n -> d + n < 2^64 ->
  cov mem (setmem 64 LittleE 8 M b v) s d n (fun i => i < N.max P (j + 8)).
Proof.
  intros. eapply cov_mono. eapply cov_store8'; eassumption.
  intros i I Ci. cbv beta in *. lia.
Qed.

Ltac cov_peel2 :=
  match goal with
  | |- cov ?mem (setmem 64 LittleE 8 ?M ?b ?v) ?s ?d ?n _ =>
      eapply (cov_store8m mem M s d n _ (b - d) b v);
      [ cov_peel2 | lia | apply (f_equal (getmem 64 LittleE 8 mem)); lia | lia | lia | lia ]
  | |- cov _ _ _ _ _ _ => first [ eassumption | apply cov_init0 ]
  end.
