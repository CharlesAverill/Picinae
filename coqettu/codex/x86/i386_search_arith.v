(* Bounded indices behind wrapping byte-search pointers and word endpoints. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_byte_search i386_bits.
From Stdlib Require Import NArith Lia.
Open Scope N.

Lemma search_pointer_injective32:forall p i j,
  i<2^32 ->j<2^32 ->(p+i) mod 2^32=(p+j) mod 2^32 ->i=j.
Proof.
  intros p i j I J EQ. apply (f_equal (fun x=>msub 32 x p)) in EQ.
  psimpl in EQ. exact EQ.
Qed.
Lemma search_endpoint_remaining32:forall p n k,
  n<2^32 ->k<=n ->msub 32 ((p+n) mod 2^32) ((p+k) mod 2^32)=n-k.
Proof.
  intros p n k N K. psimpl. rewrite msub_sub by exact K.
  apply N.mod_small. lia.
Qed.
Lemma search_word_room:forall k e,
  k<=e ->k<>e ->(e-k) mod 4=0 ->k+4<=e.
Proof.
  intros k e LE NE MOD. destruct (N.lt_ge_cases (e-k) 4) as [LT|GE];[|lia].
  rewrite N.mod_small in MOD by exact LT. lia.
Qed.
Lemma search_word_multiple_next:forall k e,
  k+4<=e ->(e-k) mod 4=0 ->(e-(k+4)) mod 4=0.
Proof.
  intros k e LE MOD. pose proof (N.div_mod (e-k) 4 ltac:(discriminate)) as DIV.
  rewrite MOD in DIV.
  replace (e-(k+4)) with (((e-k)/4-1)*4) by lia. apply N.Div0.mod_mul.
Qed.
Lemma search_word_endpoint:forall n k,n<2^32 ->k<=n ->
  let e:=k+N.land (n-k) 4294967292 in
  k<=e /\ e<=n /\ (e-k) mod 4=0.
Proof.
  intros n k N K e. unfold e.
  assert (BOUND:n-k<2^32) by lia.
  pose proof (align_down4_32_bounds (n-k) BOUND) as [LE HI].
  rewrite N.add_comm,N.add_sub. split;[lia|]. split;[lia|].
  apply align_down4_32_multiple;exact BOUND.
Qed.

Lemma search_endpoint_write:forall p n k,k<=n ->n-k+p+k=p+n.
Proof. intros;lia. Qed.
Lemma search_word_address:forall p n k,
  (N.land (n-k) 4294967292+p+k) mod 2^32=
  (p+(k+N.land (n-k) 4294967292)) mod 2^32.
Proof. intros. f_equal. lia. Qed.

Lemma search_repeated_signed_product:forall c,c<256 ->
  (scast 32 64 c*scast 32 64 16843009) mod 2^32=repeated_byte32 c.
Proof.
  intros c C. change ((scast 32 64 c*16843009) mod 2^32=repeated_byte32 c).
  unfold scast. rewrite toZ32_small by lia. rewrite ofZ_N2Z. rewrite (N.mod_small c (2^64)) by lia.
  unfold repeated_byte32. apply N.mod_small. lia.
Qed.
