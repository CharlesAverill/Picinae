(* A fixed address/ID classifier for all four GMP routines.
   Contexts and wrapper properties occur only in predicate arguments. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_copyi_preservation.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
From Stdlib Require Import NArith.
Import X64Notations.
Open Scope N.

Record gmp_context := {
  call_initial : store;
  call_dst : N;
  call_src1 : N;
  call_src2 : N;
  call_count : N;
  call_carry : N
}.
Definition call_memory c := call_initial c V_MEM64.
Definition context_nc_inv sub c :=
  nc_call_invset sub (call_memory c) (call_dst c) (call_src1 c) (call_src2 c)
    (call_count c) (call_carry c) (call_initial c).
Definition context_copy_inv c :=
  copyi_call_invset (call_memory c) (call_dst c) (call_src1 c) (call_count c) (call_initial c).

Definition gmp_family copy_ctx add_ctx sub_ctx (wrapper_property : store -> addr -> Prop)
  T (Inv Post : inv_type T) (NoInv : T) (s : store) (a : addr) : T :=
  match a with
  (* __gmpn_copyi precondition *)
  | 0x15b186 => Inv 0 (true_inv (context_copy_inv copy_ctx ((Addr a,s)::nil)))
  | 0x15b190 | 0x15b1bc | 0x15b1cf => Inv 0 (true_inv (context_copy_inv copy_ctx ((Addr a,s)::nil)))
  (* __gmpn_copyi postcondition *)
  | 0x15b1e2 => Post 0 (true_inv (context_copy_inv copy_ctx ((Addr a,s)::nil)))
  (* __gmpn_add_nc precondition *)
  | 0x1284e0 => Inv 1 (true_inv (context_nc_inv false add_ctx ((Addr a,s)::nil)))
  (* __gmpn_add_n precondition *)
  | 0x128500 => Inv 1 (true_inv (context_nc_inv false add_ctx ((Addr a,s)::nil)))
  | 0x128517 | 0x12851e | 0x128521 | 0x128524 | 0x128527
  | 0x12852f | 0x128532 | 0x128536 | 0x12853d | 0x128540
  | 0x128544 | 0x128547 | 0x12854b | 0x12854f | 0x12855a
  | 0x128560 | 0x128563 | 0x128567 | 0x12856b | 0x12856f
  | 0x128594 | 0x12859e | 0x1285a2 | 0x1285a5 | 0x1285a9
  | 0x1285ad | 0x1285b1 | 0x1285ca | 0x1285d2 => Inv 1 (true_inv (context_nc_inv false add_ctx ((Addr a,s)::nil)))
  (* __gmpn_add_nc postcondition *)
  (* __gmpn_add_n postcondition *)
  | 0x128526 | 0x12853f | 0x12855d | 0x1285d4 => Post 1 (true_inv (context_nc_inv false add_ctx ((Addr a,s)::nil)))
  (* __gmpn_sub_nc precondition *)
  | 0x128740 => Inv 2 (true_inv (context_nc_inv true sub_ctx ((Addr a,s)::nil)))
  (* __gmpn_sub_n precondition *)
  | 0x128760 => Inv 2 (true_inv (context_nc_inv true sub_ctx ((Addr a,s)::nil)))
  | 0x128777 | 0x12877e | 0x128781 | 0x128784 | 0x128787
  | 0x12878f | 0x128792 | 0x128796 | 0x12879d | 0x1287a0
  | 0x1287a4 | 0x1287a7 | 0x1287ab | 0x1287af | 0x1287ba
  | 0x1287c0 | 0x1287c3 | 0x1287c7 | 0x1287cb | 0x1287cf
  | 0x1287f4 | 0x1287fe | 0x128802 | 0x128805 | 0x128809
  | 0x12880d | 0x128811 | 0x12882a | 0x128832 => Inv 2 (true_inv (context_nc_inv true sub_ctx ((Addr a,s)::nil)))
  (* __gmpn_sub_nc postcondition *)
  (* __gmpn_sub_n postcondition *)
  | 0x128786 | 0x12879f | 0x1287bd | 0x128834 => Post 2 (true_inv (context_nc_inv true sub_ctx ((Addr a,s)::nil)))
  (* __gmpn_add_n_sub_n precondition *)
  | 0x15c360 => Inv 3 (wrapper_property s a)
  | 0x15c448 | 0x15c508 | 0x15c3b8 | 0x15c480 | 0x15c538
  | 0x15c3ef | 0x15c420 | 0x15c4b7 | 0x15c4e8 | 0x15c568
  | 0x15c597 | 0x15c5b1 | 0x15c432 => Inv 3 (wrapper_property s a)
  (* __gmpn_add_n_sub_n postcondition *)
  | 0x15c443 => Post 3 (wrapper_property s a)
  | _ => NoInv
  end.

Definition gmp_invs id copy_ctx add_ctx sub_ctx wrapper_property :=
  make_invs id gmp_linked (gmp_family copy_ctx add_ctx sub_ctx wrapper_property).
Definition gmp_exits id copy_ctx add_ctx sub_ctx wrapper_property :=
  make_exits id gmp_linked (gmp_family copy_ctx add_ctx sub_ctx wrapper_property).

Theorem gmp_same_invset_family : forall c a s w c' a' s' w',
  same_invset_family (gmp_family c a s w) (gmp_family c' a' s' w').
Proof. reflexivity. Qed.
