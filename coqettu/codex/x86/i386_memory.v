(* Pointwise fill and outside-region memory frames for writing primitives. *)
Require Import Picinae_i386.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition memory_region_frame (m0 m : memory) (p len : N) : Prop :=
  forall a count, ~overlap 32 p len a count ->
    getmem 32 LittleE count m a=getmem 32 LittleE count m0 a.
Definition wide_filled (m : memory) (p c k : N) : Prop :=
  forall i, i<k -> getmem 32 LittleE 4 m (p+4*i)=c.

Lemma protected_stack_region_bound : forall sp p n,
  ~overlap 32 sp 16 p (4*n) -> 4*n<2^32.
Proof.
  intros sp p n NO. destruct (noverlap_sep 32 sp 16 p (4*n) NO) as [LE|ZERO];
    [|discriminate]. pose proof (msub_lt 32 sp p) as BOUND. lia.
Qed.

Lemma distinct_wide_cells : forall p n i j,
  4*n<2^32 -> i<n -> j<n -> i<>j ->
  ~overlap 32 (p+4*i) 4 (p+4*j) 4.
Proof.
  intros p n i j BOUND I J NE (u & v & U & V & EQ).
  replace (p+4*i+u) with (p+(4*i+u)) in EQ by lia.
  replace (p+4*j+v) with (p+(4*j+v)) in EQ by lia.
  pose proof (f_equal (fun a=>msub 32 a p) EQ) as DELTA.
  cbn beta in DELTA. rewrite !msub_mod_l, !add_msub_l in DELTA by reflexivity.
  rewrite !N.mod_small in DELTA by lia. lia.
Qed.

Lemma wide_filled_step : forall m p c n k,
  4*n<2^32 -> c<2^32 -> k<n -> wide_filled m p c k ->
  wide_filled (setmem 32 LittleE 4 m (p+4*k) c) p c (k+1).
Proof.
  intros m p c n k BOUND C K FILLED i I.
  destruct (N.eq_dec i k) as [EQ|NE].
  - subst i. rewrite getmem_setmem by lia. apply N.mod_small. exact C.
  - rewrite getmem_noverlap.
    + apply FILLED. clear - I NE. lia.
    + apply distinct_wide_cells with (n:=n); try assumption; clear - I K; lia.
Qed.

Lemma memory_region_frame_step : forall m0 m p c n k,
  k<n -> memory_region_frame m0 m p (4*n) ->
  memory_region_frame m0 (setmem 32 LittleE 4 m (p+4*k) c) p (4*n).
Proof.
  intros m0 m p c n k K FRAME a count NO.
  rewrite getmem_noverlap.
  - exact (FRAME a count NO).
  - apply noverlap_symmetry. eapply noverlap_shrink; [|exact NO].
    rewrite add_msub_l. eapply N.le_trans.
    + apply N.add_le_mono_r, N.Div0.mod_le.
    + clear - K. lia.
Qed.

Lemma protected_stack_load : forall m0 m sp p n off,
  ~overlap 32 sp 16 p (4*n) -> memory_region_frame m0 m p (4*n) -> off<=12 ->
  getmem 32 LittleE 4 m (off+sp)=getmem 32 LittleE 4 m0 (off+sp).
Proof.
  intros m0 m sp p n off NO FRAME OFF. apply FRAME.
  apply noverlap_symmetry. eapply (noverlap_shrink 32 sp 16 p (4*n) (off+sp) 4).
  - rewrite add_msub_r. eapply N.le_trans.
    + apply N.add_le_mono_r, N.Div0.mod_le.
    + clear - OFF. lia.
  - exact NO.
Qed.
