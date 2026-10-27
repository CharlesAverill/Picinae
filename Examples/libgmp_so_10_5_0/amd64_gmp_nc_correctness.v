(* Whole-function partial correctness of the standalone AMD64 NC lifts.
   Exit invariants hold immediately before RET. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_proof.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_control.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Ltac nc_discharge_cut MDL POS C B SAFE_U SAFE_V PRE :=
  match goal with
  |- nextinv _ (nc_invset ?sub ?m0 ?d ?u ?v ?n ?cin) _ _ ((Addr ?pc,_)::_) =>
    let a := eval vm_compute in (if sub then pc-0x260 else pc) in
    first [
      solve [eapply (nc_vc_arithmetic sub a); [exact MDL | vm_compute; tauto | exact PRE]] |
      solve [eapply (nc_vc_tail_store sub a); [exact MDL | exact B | vm_compute; tauto | exact PRE]] |
      solve [eapply nc_vc_tail_load1; exact PRE] |
      solve [eapply nc_vc_tail_load2; exact PRE] |
      solve [eapply nc_vc_tail_load3; exact PRE] |
      solve [eapply nc_vc_block_dispatch; exact PRE] |
      solve [eapply nc_vc_final_advance; exact PRE] |
      solve [eapply nc_vc_remainder_dispatch; exact PRE] |
      solve [eapply nc_vc_cycle; [exact MDL | exact B | exact SAFE_U | exact SAFE_V | exact PRE]] |
      solve [eapply nc_vc_final_store; [exact MDL | exact B | exact SAFE_U | exact SAFE_V | exact PRE]] |
      solve [eapply nc_vc_entry; [exact MDL | exact POS | exact C | exact PRE]] |
      solve [destruct PRE as (MEM & DI & SI & DX & CX & CZ); subst cin;
        eapply nc_vc_plain_entry; [exact MDL | exact POS | repeat split; assumption]] |
      solve [destruct PRE as [CF AX]; eapply (nc_vc_return_adc sub a);
        [vm_compute; tauto | exact CF | exact AX]] |
      solve [destruct PRE as [CF AX]; eapply nc_vc_return_setc; [exact CF | exact AX]]
    ]
  end.

Theorem nc_functional_correctness_from :
  forall sub a s m0 d u v n cin t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub a),s))
    (START : a=0x1284e0 \/ a=0x128500)
    (MDL : models x64typctx s)
    (INITIAL : true_inv (nc_invset sub m0 d u v n cin ((Addr (nc_address sub a),s)::nil)))
    (POS : 0<n) (C : cin<=1) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) ((x',s')::t).
Proof.
  intros sub a s m0 d u v n cin t s' x' ENTRY START MDL INITIAL POS C B SAFE_U SAFE_V.
  apply prove_invs.
  - simpl. rewrite ENTRY. destruct START as [A|A]; subst a; destruct sub;
      cbn [nc_program nc_address]; x64_step; exact INITIAL.
  - intros t1 a1 s1 t2 UT SPL PRE.
    eapply models_at_invariant.
    + exact MDL.
    + apply nc_welltyped.
    + rewrite <-(startof_prefix _ _ _ _ _ SPL). exact ENTRY.
    + intro CURRENT.
      clear -CURRENT PRE POS C B SAFE_U SAFE_V.
      destruct sub; destruct_inv 64 PRE;
        nc_discharge_cut CURRENT POS C B SAFE_U SAFE_V PRE.
Qed.

Theorem nc_functional_correctness :
  forall sub s m0 d u v n cin t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub 0x1284e0),s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m0) (DST : s R_RDI=d) (SRC_U : s R_RSI=u)
    (SRC_V : s R_RDX=v) (LEN : s R_RCX=n) (CIN : s R_R8=cin)
    (POS : 0<n) (C : cin<=1) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) ((x',s')::t).
Proof.
  intros. eapply nc_functional_correctness_from; try eassumption.
  - left. reflexivity.
  - destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv];
      repeat split; assumption.
Qed.

Theorem nc_plain_functional_correctness :
  forall sub s m0 d u v n t s' x'
    (ENTRY : startof t (x',s')=(Addr (nc_address sub 0x128500),s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m0) (DST : s R_RDI=d) (SRC_U : s R_RSI=u)
    (SRC_V : s R_RDX=v) (LEN : s R_RCX=n)
    (POS : 0<n) (B : 8*n<=2^64)
    (SAFE_U : forward_safe d u n) (SAFE_V : forward_safe d v n),
  satisfies_all (nc_program sub) (nc_invset sub m0 d u v n 0) (nc_exit sub) ((x',s')::t).
Proof.
  intros. eapply nc_functional_correctness_from; try eassumption.
  - right. reflexivity.
  - destruct sub; cbn [nc_address nc_invset nc_aux_invset nc_invset_core true_inv];
      repeat split; try assumption; reflexivity.
  - vm_compute; easy.
Qed.

(* Named specializations expose the four supported entry contracts. *)
Definition add_nc_functional_correctness := nc_functional_correctness false.
Definition sub_nc_functional_correctness := nc_functional_correctness true.
Definition add_n_functional_correctness := nc_plain_functional_correctness false.
Definition sub_n_functional_correctness := nc_plain_functional_correctness true.
