Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Lemma mod_once : forall b x, 0<b -> b<=x -> x<2*b -> x mod b=x-b.
Proof.
  intros. symmetry. apply N.mod_unique with (q:=1); nia.
Qed.

(* The Ghidra ADC lift computes two overflow tests and ORs them. *)
Definition adc_flag b x y c :=
  (if (x+y) mod b <? x then 1 else 0) .|
  (if (x+y+c) mod b <? (x+y) mod b then 1 else 0).
Lemma adc_flag_equation : forall b x y c,
  1<b -> x<b -> y<b -> c<=1 ->
  (x+y+c) mod b + b*adc_flag b x y c = x+y+c /\ adc_flag b x y c <= 1.
Proof.
  intros b x y c B X Y C.
  unfold adc_flag.
  destruct (N.lt_ge_cases (x+y) b) as [LO|HI].
  - rewrite (N.mod_small _ _ LO).
    assert (E : (x+y <? x)=false) by (apply N.ltb_ge; lia).
    rewrite E. destruct (N.lt_ge_cases (x+y+c) b) as [LO'|HI'].
    + rewrite (N.mod_small _ _ LO').
      assert (E' : (x+y+c <? x+y)=false) by (apply N.ltb_ge; lia).
      rewrite E'. cbn. split; lia.
    + rewrite mod_once by lia.
      assert (E' : (x+y+c-b <? x+y)=true) by (apply N.ltb_lt; lia).
      rewrite E'. cbn. split; lia.
  - rewrite (mod_once b (x+y)), (mod_once b (x+y+c)) by lia.
    assert (E : (x+y-b <? x)=true) by (apply N.ltb_lt; lia).
    assert (E' : (x+y+c-b <? x+y-b)=false) by (apply N.ltb_ge; lia).
    rewrite E, E'. cbn. split; lia.
Qed.

Definition sbb_flag b x y c :=
  (if x <? y then 1 else 0) .|
  (if (x+b-y) mod b <? c then 1 else 0).

(* This is also the one-limb equation used by the high-level LimbArrays
   theory: a borrow is a positive radix contribution, not N.sub truncation. *)
Lemma sbb_flag_equation : forall b x y c,
  1<b -> x<b -> y<b -> c<=1 ->
  ((x+b-y) mod b+b-c) mod b + y+c = x+b*sbb_flag b x y c /\
  sbb_flag b x y c <= 1.
Proof.
  intros b x y c B X Y C. unfold sbb_flag.
  destruct (N.lt_ge_cases x y) as [LO|HI].
  - assert (L : x+b-y < b) by lia.
    rewrite (N.mod_small _ _ L).
    assert (E : (x <? y)=true) by (apply N.ltb_lt; lia).
    assert (E' : (x+b-y <? c)=false) by (apply N.ltb_ge; lia).
    rewrite E, E'.
    rewrite mod_once by lia. cbn. split; lia.
  - replace (x+b-y) with (b+(x-y)) by lia.
    rewrite N.add_mod, N.Div0.mod_same, N.add_0_l, N.Div0.mod_mod by lia.
    rewrite (N.mod_small (x-y) b) by lia.
    assert (E : (x <? y)=false) by (apply N.ltb_ge; lia). rewrite E.
    destruct (N.lt_ge_cases (x-y) c) as [LO'|HI'].
    + assert (E' : (x-y <? c)=true) by (apply N.ltb_lt; lia). rewrite E'.
      rewrite N.mod_small by lia. cbn. split; lia.
    + assert (E' : (x-y <? c)=false) by (apply N.ltb_ge; lia). rewrite E'.
      rewrite mod_once by lia. cbn. split; lia.
Qed.

Lemma radix_add : forall k j, radix (k+j)=radix k*radix j.
Proof. intros. unfold radix. rewrite <-N.pow_add_r. f_equal. nia. Qed.
Lemma value_add : forall m p k j,
  value m p (k+j) = value m p k + radix k*value m (p+8*k) j.
Proof.
  intros. rewrite value_split, cbits_add by apply value_bound.
  unfold radix, GMPArrayParams.bytes. nia.
Qed.
Lemma nc_append : forall sub k j r a b cin c out x y cout,
  nc_equation sub r a b cin c k ->
  nc_equation sub out x y c cout j ->
  nc_equation sub (r+radix k*out) (a+radix k*x) (b+radix k*y) cin cout (k+j).
Proof.
  intros sub k j r a b cin c out x y cout E1 E2.
  unfold nc_equation in *. rewrite radix_add.
  destruct sub; nia.
Qed.

Lemma unread_limb : forall m0 m u v n k i,
  unread m0 m u v n k -> k+i+1<=n ->
  value m (u+8*(k+i)) 1=value m0 (u+8*(k+i)) 1 /\
  value m (v+8*(k+i)) 1=value m0 (v+8*(k+i)) 1.
Proof.
  intros m0 m u v n k i [U V] B.
  unfold value, GMPArrayParams.w, GMPArrayParams.bytes in *.
  replace (u+8*(k+i)) with (u+8*k+8*i) by nia.
  replace (v+8*(k+i)) with (v+8*k+8*i) by nia.
  split; eapply getmem_inner; [exact U | |exact V | ]; nia.
Qed.

Lemma noverlap_adjacent64 : forall p a b,
  a+b<=2^64 -> ~overlap 64 p a (p+a) b.
Proof.
  intros p a b B [i [j [I [J E]]]].
  apply (f_equal (fun x => msub 64 x p)) in E.
  rewrite !msub_mod_l, add_msub_l in E by reflexivity.
  replace (p+a+j) with (p+(a+j)) in E by lia.
  rewrite add_msub_l in E.
  rewrite !N.mod_small in E by lia. lia.
Qed.

Lemma value_commit : forall m d k j out,
  8*(k+j)<=2^64 -> out<radix j ->
  value (setmem 64 LittleE (8*j) m (d+8*k) out) d (k+j)
    = value m d k+radix k*out.
Proof.
  intros m d k j out B O. rewrite value_add.
  unfold value, GMPArrayParams.w, GMPArrayParams.bytes.
  rewrite getmem_noverlap by (apply noverlap_adjacent64; nia).
  rewrite getmem_setmem by nia.
  replace (8*j*8) with (8*8*j) by nia.
  rewrite N.mod_small by exact O. reflexivity.
Qed.

Lemma unread_commit : forall m0 m d u v n k j out,
  forward_safe d u n -> forward_safe d v n -> k+j<=n ->
  unread m0 m u v n (k+j) ->
  unread m0 (setmem 64 LittleE (8*j) m (d+8*k) out) u v n (k+j).
Proof.
  intros m0 m d u v n k j out U V B [UM VM].
  unfold unread, value, GMPArrayParams.w, GMPArrayParams.bytes in *.
  rewrite !getmem_noverlap; try solve [split; assumption].
  - eapply noverlap_index_r with (index:=8*k) (len2:=8*(k+j)).
    apply V. lia. nia.
  - eapply noverlap_index_r with (index:=8*k) (len2:=8*(k+j)).
    apply U. lia. nia.
Qed.

Definition limb_result (sub : bool) x y c :=
  if sub then msub 64 (msub 64 x y) c else (x+y+c) mod 2^64.
Definition limb_carry (sub : bool) x y c :=
  if sub then sbb_flag (2^64) x y c else adc_flag (2^64) x y c.
Lemma limb_equation : forall sub x y c,
  x<2^64 -> y<2^64 -> c<=1 ->
  nc_equation sub (limb_result sub x y c) x y c (limb_carry sub x y c) 1 /\
  limb_carry sub x y c<=1.
Proof.
  intros sub x y c X Y C. destruct sub.
  - pose proof (sbb_flag_equation (2^64) x y c ltac:(reflexivity) X Y C) as [E B].
    unfold limb_result, limb_carry, nc_equation. change (radix 1) with (2^64).
    unfold msub. rewrite (N.mod_small _ _ Y).
    assert (C64 : c<2^64) by lia. rewrite (N.mod_small _ _ C64).
    replace (x+(2^64-y)) with (x+2^64-y) by lia.
    replace (((x+2^64-y) mod 2^64)+(2^64-c))
      with (((x+2^64-y) mod 2^64)+2^64-c) by lia.
    split; assumption.
  - exact (adc_flag_equation (2^64) x y c ltac:(reflexivity) X Y C).
Qed.

Lemma cbits_bound_add : forall hi lo wh wl,
  hi<2^wh -> lo<2^wl -> cbits hi wl lo<2^(wh+wl).
Proof. intros. rewrite cbits_add, N.pow_add_r by assumption. nia. Qed.

Lemma buffered_bound : forall s q,
  models x64typctx s -> q<=4 -> buffered s q<radix q.
Proof.
  intros s q M Q.
  assert (B8 := models_var R_R8 M). change (s R_R8<2^64) in B8.
  assert (B9 := models_var R_R9 M). change (s R_R9<2^64) in B9.
  assert (B10 := models_var R_R10 M). change (s R_R10<2^64) in B10.
  assert (B11 := models_var R_R11 M). change (s R_R11<2^64) in B11.
  assert (CASES : q=0 \/ q=1 \/ q=2 \/ q=3 \/ q=4) by lia.
  destruct CASES as [E|[E|[E|[E|E]]]]; subst q; cbn [buffered].
  - reflexivity.
  - exact B8.
  - change (radix 2) with (2^(64+64)). apply cbits_bound_add; assumption.
  - change (radix 3) with (2^(64+128)). apply cbits_bound_add; [exact B10|].
    change 128 with (64+64). apply cbits_bound_add; assumption.
  - change (radix 4) with (2^(64+192)). apply cbits_bound_add; [exact B11|].
    change 192 with (64+128). apply cbits_bound_add; [exact B10|].
    change 128 with (64+64). apply cbits_bound_add; assumption.
Qed.

Definition pending_reg q := match q with 0=>R_R8 | 1=>R_R9 | 2=>R_R10 | _=>R_R11 end.
Lemma buffered_extend : forall s q lo cout,
  models x64typctx s -> q<4 ->
  buffered (s[R_CF:=cout][pending_reg q:=lo]) (q+1)
    = buffered s q + radix q*lo.
Proof.
  intros s q lo cout M Q.
  assert (B : buffered s q<radix q) by (apply buffered_bound; [assumption|lia]).
  assert (CASES : q=0 \/ q=1 \/ q=2 \/ q=3) by lia.
  destruct CASES as [E|[E|[E|E]]]; subst q;
    cbn [N.add Pos.add Pos.add_carry Pos.succ pending_reg buffered] in *;
    repeat (rewrite update_updated || rewrite update_frame by discriminate).
  - change (radix 0) with 1. lia.
  - rewrite cbits_add by exact B. change (radix 1) with (2^64). nia.
  - rewrite cbits_add by exact B. change (radix 2) with (2^128). nia.
  - rewrite cbits_add by exact B. change (radix 3) with (2^192). nia.
Qed.

Lemma nc_prefix_extend : forall sub m0 d u v cin k q s,
  models x64typctx s -> q<4 ->
  nc_prefix sub m0 d u v cin k q s ->
  s (pending_reg q)=value m0 (u+8*(k+q)) 1 ->
  let x := s (pending_reg q) in
  let y := value m0 (v+8*(k+q)) 1 in
  nc_prefix sub m0 d u v cin k (q+1)
    (s[R_CF:=limb_carry sub x y (s R_CF)]
      [pending_reg q:=limb_result sub x y (s R_CF)]).
Proof.
  intros sub m0 d u v cin k q s M Q [CF [QB EQ]] X.
  cbn zeta.
  assert (XB := models_var (pending_reg q) M).
  assert (CASE : q=0 \/ q=1 \/ q=2 \/ q=3) by lia.
  assert (X64 : s (pending_reg q)<2^64).
  { destruct CASE as [E|[E|[E|E]]]; subst q; exact XB. }
  assert (Y64 : value m0 (v+8*(k+q)) 1<2^64) by apply value_bound.
  pose proof (limb_equation sub _ _ _ X64 Y64 CF) as [LEQ LBIT].
  pose proof (nc_append sub (k+q) 1 _ _ _ _ _ _ _ _ _ EQ LEQ) as NEXT.
  rewrite X in NEXT. rewrite <-!value_add, <-N.add_assoc in NEXT.
  assert (NO_CF : pending_reg q<>R_CF).
  { destruct CASE as [E|[E|[E|E]]]; subst q; discriminate. }
  assert (NO_MEM : pending_reg q<>V_MEM64).
  { destruct CASE as [E|[E|[E|E]]]; subst q; discriminate. }
  unfold nc_prefix.
  rewrite update_frame by congruence. rewrite update_updated.
  split. exact LBIT. split. lia.
  rewrite buffered_extend by assumption.
  rewrite update_frame by congruence. rewrite update_frame by discriminate.
  rewrite radix_add in NEXT.
  rewrite X. replace (k+(q+1)) with (k+q+1) by lia.
  clear -NEXT. unfold nc_equation in *. destruct sub; nia.
Qed.

Lemma unread_shrink : forall m0 m u v n k j,
  unread m0 m u v n k -> k+j<=n -> unread m0 m u v n (k+j).
Proof.
  intros m0 m u v n k j [U V] B.
  unfold unread, value, GMPArrayParams.w, GMPArrayParams.bytes in *.
  replace (u+8*(k+j)) with (u+8*k+8*j) by nia.
  replace (v+8*(k+j)) with (v+8*k+8*j) by nia.
  split; eapply getmem_inner; [exact U | |exact V | ]; nia.
Qed.

Lemma nc_prefix_commit : forall sub m0 d u v n cin k q s,
  models x64typctx s -> 8*n<=2^64 -> k+q<=n ->
  nc_prefix sub m0 d u v cin k q s ->
  nc_prefix sub m0 d u v cin (k+q) 0
    (s[V_MEM64:=setmem 64 LittleE (8*q) (s V_MEM64) (d+8*k) (buffered s q)]).
Proof.
  intros sub m0 d u v n cin k q s M N K [CF [Q EQ]].
  unfold nc_prefix. rewrite update_frame by discriminate.
  cbn [buffered]. rewrite N.mul_0_r, !N.add_0_r, update_updated.
  split. exact CF. split. lia.
  rewrite value_commit; [exact EQ | nia | apply buffered_bound; assumption].
Qed.

Lemma msub_repr64 : forall x y,
  y<2^64 -> x ⊖ y=(x+2^64-y) mod 2^64.
Proof.
  intros x y Y. unfold msub. rewrite (N.mod_small y (2^64) Y). f_equal. lia.
Qed.
