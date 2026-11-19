(* Wide-string scan periods and i386 signed pointer-difference arithmetic. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_strings.
From Stdlib Require Import NArith Lia.
Open Scope N.

Definition wide_first_nul (m:memory) (p k:N) :=
  k<2^30 /\ wide_prefix m p 0 k /\ getmem 32 LittleE 4 m (p+4*k)=0.
Definition wide_length32 (k:N) := ashiftr 32 ((4*k) mod 2^32) 2.

Lemma wide_offset_reduce : forall k,(4*k) mod 2^32=4*(k mod 2^30).
Proof. intros k. change ((4*k) mod (4*2^30)=4*(k mod 2^30)). apply N.Div0.mul_mod_distr_l. Qed.
Lemma wide_read_reduce : forall m p k,
  getmem 32 LittleE 4 m (p+4*(k mod 2^30))=getmem 32 LittleE 4 m (p+4*k).
Proof.
  intros. rewrite <- getmem_mod_l at 1.
  rewrite <- wide_offset_reduce,mp2_add_r,getmem_mod_l. reflexivity.
Qed.
Lemma wide_prefix_stop : forall m p k,
  wide_prefix m p 0 k -> getmem 32 LittleE 4 m ((p+4*k) mod 2^32)=0 ->
  wide_first_nul m p (k mod 2^30).
Proof.
  intros m p k PRE ZERO. split;[apply mp2_mod_lt|]. split.
  - intros i I. apply PRE. pose proof (mp2_mod_le k 30). clear - I H;lia.
  - rewrite wide_read_reduce. rewrite getmem_mod_l in ZERO. exact ZERO.
Qed.
Lemma wide_first_nul_unique : forall m p i j,
  wide_first_nul m p i -> wide_first_nul m p j -> i=j.
Proof.
  intros m p i j (IB & IP & IZ) (JB & JP & JZ).
  destruct (N.lt_trichotomy i j) as [LT|[EQ|GT]];[|exact EQ|].
  - exfalso. exact (JP i LT IZ).
  - exfalso. exact (IP j GT JZ).
Qed.
Lemma wide_length32_reduce : forall k,wide_length32 (k mod 2^30)=wide_length32 k.
Proof. intros k. unfold wide_length32. rewrite <- wide_offset_reduce,mp2_mod_mod. reflexivity. Qed.
Lemma wide_length32_small : forall k,k<2^29 -> wide_length32 k=k.
Proof.
  intros k K. unfold wide_length32. rewrite N.mod_small by lia.
  rewrite ashiftr_nonneg by (rewrite N.mod_small by lia;change (4*k<2147483648);lia).
  rewrite N.mod_small by lia. rewrite N.shiftr_div_pow2.
  change (4*k/4=k). rewrite N.mul_comm. apply N.div_mul;discriminate.
Qed.
