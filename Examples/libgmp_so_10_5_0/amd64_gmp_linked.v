(* A linked IL program with explicit assumed PLT symbol bindings.
   The synthetic jumps encode the linking abstraction used by call proofs. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_add_nc_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_sub_nc_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_add_n_sub_n_amd64.
From Stdlib Require Import NArith.
Open Scope N.

Definition gmp_plt (a : addr) : option (N*stmt) :=
  match a with
  | 0x10c030 => Some (6,Jmp (Word 0x1284e0 64))
  | 0x10b8f0 => Some (6,Jmp (Word 0x128740 64))
  | 0x10bbe0 => Some (6,Jmp (Word 0x15b186 64))
  | _ => None
  end.
Definition gmp_linked : program := fun s a =>
  match libgmp_so_10_5_0___gmpn_copyi_amd64 s a with
  | Some code => Some code | None =>
  match libgmp_so_10_5_0___gmpn_add_nc_amd64 s a with
  | Some code => Some code | None =>
  match libgmp_so_10_5_0___gmpn_sub_nc_amd64 s a with
  | Some code => Some code | None =>
  match libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 s a with
  | Some code => Some code | None => gmp_plt a
  end end end end.

Lemma gmp_plt_welltyped : welltyped_prog x64typctx (fun _ => gmp_plt).
Proof. Picinae_typecheck. Qed.
Theorem gmp_linked_welltyped : welltyped_prog x64typctx gmp_linked.
Proof.
  intros s a. unfold gmp_linked.
  destruct (libgmp_so_10_5_0___gmpn_copyi_amd64 s a) as [[sz q]|] eqn:C.
  - pose proof (Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.welltyped s a) as H.
    rewrite C in H. exact H.
  - destruct (libgmp_so_10_5_0___gmpn_add_nc_amd64 s a) as [[sz q]|] eqn:A.
    + pose proof (Picinae.Examples.libgmp_so_10_5_0.gmpn_add_nc_amd64.welltyped s a) as H.
      rewrite A in H. exact H.
    + destruct (libgmp_so_10_5_0___gmpn_sub_nc_amd64 s a) as [[sz q]|] eqn:S.
      * pose proof (Picinae.Examples.libgmp_so_10_5_0.gmpn_sub_nc_amd64.welltyped s a) as H.
        rewrite S in H. exact H.
      * destruct (libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 s a) as [[sz q]|] eqn:W.
        -- pose proof (Picinae.Examples.libgmp_so_10_5_0.gmpn_add_n_sub_n_amd64.welltyped s a) as H.
           rewrite W in H. exact H.
        -- exact (gmp_plt_welltyped s a).
Qed.
Theorem gmp_linked_nwc : forall s s', gmp_linked s=gmp_linked s'.
Proof. reflexivity. Qed.

Ltac gmp_check_lookup :=
  intros s a CODE; destruct a as [|a];
  repeat first [reflexivity | solve [exfalso; apply CODE; reflexivity] | destruct a as [a|a|] ].

Lemma gmp_linked_copyi : forall s a,
  libgmp_so_10_5_0___gmpn_copyi_amd64 s a<>None ->
  gmp_linked s a=libgmp_so_10_5_0___gmpn_copyi_amd64 s a.
Proof.
  intros s a H. unfold gmp_linked.
  destruct (libgmp_so_10_5_0___gmpn_copyi_amd64 s a); [reflexivity | contradiction].
Qed.
Lemma gmp_linked_add_nc : forall s a,
  libgmp_so_10_5_0___gmpn_add_nc_amd64 s a<>None ->
  gmp_linked s a=libgmp_so_10_5_0___gmpn_add_nc_amd64 s a.
Proof. gmp_check_lookup. Qed.
Lemma gmp_linked_sub_nc : forall s a,
  libgmp_so_10_5_0___gmpn_sub_nc_amd64 s a<>None ->
  gmp_linked s a=libgmp_so_10_5_0___gmpn_sub_nc_amd64 s a.
Proof. gmp_check_lookup. Qed.
Lemma gmp_linked_wrapper : forall s a,
  libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 s a<>None ->
  gmp_linked s a=libgmp_so_10_5_0___gmpn_add_n_sub_n_amd64 s a.
Proof. gmp_check_lookup. Qed.

Lemma gmp_link_add : forall s, gmp_linked s 0x10c030=Some (6,Jmp (Word 0x1284e0 64)).
Proof. reflexivity. Qed.
Lemma gmp_link_sub : forall s, gmp_linked s 0x10b8f0=Some (6,Jmp (Word 0x128740 64)).
Proof. reflexivity. Qed.
Lemma gmp_link_copy : forall s, gmp_linked s 0x10bbe0=Some (6,Jmp (Word 0x15b186 64)).
Proof. reflexivity. Qed.
