(* Checked control-flow obligations in the shared GMP program. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_nc_vcs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_linked.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_family.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_specs.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.
Lemma wrapper_vc_epilogue : forall r cc ac sc s t,
  wrapper_pre r -> wrapper_epilogue r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c432,s)::t).
Proof.
 intros r cc ac sc s t PRE [SP [SAVED [FRAME POST]]].
 pose proof PRE as WPRE. destruct PRE as [MDL PRE].
 assert (STACK : 0x5a8<=r R_RSP) by (clear -PRE; intuition lia).
 pose proof (models_var R_RSP MDL) as B. change (r R_RSP<2^64) in B.
 unfold wrapper_saved in SAVED.
 do 7 x64_step.
 split; [exact WPRE | ].
 unfold wrapper_post,leaf_abi,add_n_sub_n_post.
 nc_updates. psimpl.
 destruct SAVED as (BX & BP & R12 & R13 & R14 & R15).
 rewrite (N.add_comm (wrapper_frame r)) in BX,BP,R12,R13,R14,R15.
 rewrite BX,BP,R12,R13,R14,R15.
 split; [exact POST | ].
 split; [ | exact FRAME ].
 repeat split; try reflexivity.
 unfold wrapper_frame. rewrite N.mod_small by lia. lia.
Qed.

Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_wrapper_lemmas.
Lemma wrapper_dispatch_prologue : forall r s,
  wrapper_pre r ->
  s V_MEM64=wrapper_prologue_memory r -> s R_RSP=wrapper_frame r ->
  s R_R12=wrapper_n r -> s R_RBX=wrapper_u r -> s R_RBP=wrapper_v r ->
  s R_R13=wrapper_sum r -> s R_R14=wrapper_diff r -> wrapper_dispatch r s.
Proof.
  intros r s PRE MEM SP LEN U V SUM DIFF.
  unfold wrapper_dispatch. rewrite MEM.
  split.
  - unfold wrapper_common. rewrite MEM. split; [exact SP | ].
    split; [exact LEN | ]. split.
    + apply wrapper_prologue_saved,PRE.
    + apply wrapper_prologue_memory_frame,PRE.
  - split; [apply wrapper_prologue_unread,PRE | repeat split; assumption].
Qed.

Lemma wrapper_epilogue_zero : forall r s,
  wrapper_pre r -> wrapper_n r=0 ->
  s V_MEM64=wrapper_prologue_memory r -> s R_RSP=wrapper_frame r ->
  s R_RAX=0 -> wrapper_epilogue r s.
Proof.
  intros r s PRE ZERO MEM SP AX. unfold wrapper_epilogue. rewrite MEM.
  split; [exact SP | ]. split; [apply wrapper_prologue_saved,PRE | ].
  split; [apply wrapper_prologue_memory_frame,PRE | ].
  unfold add_n_sub_n_post. rewrite ZERO,AX.
  exists 0,0. unfold nc_equation. rewrite !value_zero. repeat split; lia.
Qed.

Ltac wrapper_prologue_projection PRE STACK B :=
  eapply wrapper_dispatch_prologue; [exact PRE | | | | | | | ];
    unfold wrapper_prologue_memory,wrapper_frame,wrapper_n,wrapper_sum,wrapper_diff,wrapper_u,wrapper_v;
    nc_updates; repeat rewrite msub_sub by (clear -STACK; lia);
    repeat rewrite N.mod_small by (clear -B STACK; lia); reflexivity.

Lemma wrapper_vc_entry_zero : forall r cc ac sc t,
  wrapper_pre r -> wrapper_n r=0 ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c360,r)::t).
Proof.
  intros r cc ac sc t PRE ZERO.
  pose proof (proj1 PRE) as MDL.
  assert (STACK : 0x5b0<=r R_RSP) by (unfold wrapper_pre in PRE; tauto).
  pose proof (models_var R_RSP MDL) as B. change (r R_RSP<2^64) in B.
  do 14 x64_step.
  - abstract (split; [exact PRE | ]; split;
      [wrapper_prologue_projection PRE STACK B | left; apply N.eqb_eq in BC; exact BC]).
  - do 2 x64_step.
    + abstract (split; [exact PRE | ]; split;
        [wrapper_prologue_projection PRE STACK B | right; apply N.eqb_eq in BC0; exact BC0]).
    + change (r R_R8=0) in ZERO. rewrite ZERO.
      do 4 x64_step.
      abstract (split; [exact PRE | ];
        eapply wrapper_epilogue_zero; [exact PRE | exact ZERO | | | ];
        unfold wrapper_prologue_memory,wrapper_frame;
        nc_updates; repeat rewrite msub_sub by (clear -STACK; lia);
        repeat rewrite N.mod_small by (clear -B STACK; lia);
        first [reflexivity | rewrite N.lxor_nilpotent; reflexivity]).
Qed.

Lemma wrapper_zero_common : forall r s,
  wrapper_common r s -> wrapper_n r=0 -> s R_RAX=0 -> wrapper_epilogue r s.
Proof.
  intros r s (SP & LEN & SAVED & FRAME) ZERO AX.
  unfold wrapper_epilogue. split; [exact SP | ]. split; [exact SAVED | ].
  split; [exact FRAME | ]. unfold add_n_sub_n_post. rewrite ZERO,AX.
  exists 0,0. unfold nc_equation. rewrite !value_zero. repeat split; lia.
Qed.

Lemma wrapper_vc_scratch_zero : forall r cc ac sc s t,
  wrapper_pre r -> wrapper_n r=0 -> wrapper_dispatch r s ->
  nextinv gmp_linked (gmp_invs 3 cc ac sc (wrapper_property r))
    (gmp_exits 3 cc ac sc (wrapper_property r)) false ((Addr 0x15c508,s)::t).
Proof.
  intros r cc ac sc s t PRE ZERO [COMMON REST].
  pose proof (proj1 (proj2 COMMON)) as LEN.
  x64_step. rewrite ?LEN,ZERO. x64_step.
  do 2 x64_step. split; [exact PRE | ].
  apply wrapper_zero_common; [ | exact ZERO | ].
  - unfold wrapper_common. nc_updates.
    destruct COMMON as (SP & N & SAVED & FRAME).
    split; [exact SP | ]. split; [symmetry; exact ZERO | ]. split; assumption.
  - nc_updates. rewrite N.lxor_nilpotent. reflexivity.
Qed.
