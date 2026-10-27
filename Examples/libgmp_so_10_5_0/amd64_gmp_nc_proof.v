(* Shared verification conditions for the add/subtract-with-carry lifts. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_add_nc_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_sub_nc_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_lemmas.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Definition nc_program (sub : bool) : program :=
  if sub then libgmp_so_10_5_0___gmpn_sub_nc_amd64 else libgmp_so_10_5_0___gmpn_add_nc_amd64.
Definition nc_address (sub : bool) a := if sub then a+0x260 else a.
Definition nc_exit (sub : bool) (t : trace) :=
  match t with (Addr pc,_)::_ =>
    match (if sub then pc-0x260 else pc) with
    | 0x128526 | 0x12853f | 0x12855d | 0x1285d4 => true | _ => false end
  | _ => false end.

Theorem nc_welltyped : forall sub, welltyped_prog x64typctx (nc_program sub).
Proof.
  intros [].
  - exact Picinae.Examples.libgmp_so_10_5_0.gmpn_sub_nc_amd64.welltyped.
  - exact Picinae.Examples.libgmp_so_10_5_0.gmpn_add_nc_amd64.welltyped.
Qed.

Ltac nc_bigstep := first [libgmp_so_10_5_0___gmpn_add_nc_amd64_bigstep |
                          libgmp_so_10_5_0___gmpn_sub_nc_amd64_bigstep].

(* ADC EAX,EAX converts an outgoing CF into the ABI return value when EAX=0.
   INC/DEC preserve CF, so the same lemma closes all three such return paths. *)
Lemma nc_vc_return_adc : forall sub a m0 d u v n cin s t,
  (a=0x128524 \/ a=0x12853d \/ a=0x1285d2) ->
  nc_cf_post sub m0 d u v n cin s -> s R_RAX=0 ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub a),s)::t).
Proof.
  intros sub a m0 d u v n cin s t A [CF EQ] AX.
  assert (CASES : s R_CF=0 \/ s R_CF=1) by lia.
  destruct sub; destruct A as [A|[A|A]]; subst a;
    destruct CASES as [C|C]; cbn [nc_program nc_address];
    nc_bigstep;
    unfold nc_post; psimpl;
    rewrite ?AX, ?C; psimpl;
    (split; [vm_compute; easy | rewrite C in EQ; exact EQ]).
Qed.

(* SETC AL replaces the low byte of EAX=1 on the three-limb return path. *)
Lemma nc_vc_return_setc : forall sub m0 d u v n cin s t,
  nc_cf_post sub m0 d u v n cin s -> s R_RAX=1 ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x12855a),s)::t).
Proof.
  intros sub m0 d u v n cin s t [CF EQ] AX.
  assert (CASES : s R_CF=0 \/ s R_CF=1) by lia.
  destruct sub; destruct CASES as [C|C]; cbn [nc_program nc_address];
    nc_bigstep;
    unfold nc_post; psimpl;
    rewrite ?AX, ?C; psimpl;
    (split; [vm_compute; easy | rewrite C in EQ; exact EQ]).
Qed.

Lemma nc_vc_first_limb : forall sub m0 d u v n cin s t,
  models x64typctx s ->
  (exists k, n=k+1 /\ nc_stage sub m0 d u v n cin k 0 k s /\
    s R_RAX=0 /\ preloaded m0 u k 1 s) ->
  nextinv (nc_program sub) (nc_invset sub m0 d u v n cin) (nc_exit sub) false
    ((Addr (nc_address sub 0x12851e),s)::t).
Proof.
  intros sub m0 d u v n cin s t MDL [k [NK [[KN [PTR [UN PRE]]] [AX LOAD]]]].
  destruct PTR as [DI [SI DX]].
  assert (X : s R_R8=value m0 (u+8*k) 1) by (apply (proj1 LOAD); lia).
  assert (X' : s (pending_reg 0)=value m0 (u+8*(k+0)) 1).
  { rewrite N.add_0_r. exact X. }
  pose proof (nc_prefix_extend sub m0 d u v cin k 0 s MDL ltac:(lia) PRE X') as NP.
  rewrite N.add_0_r in NP.
  pose proof (unread_limb m0 (s V_MEM64) u v n k 0 UN ltac:(lia)) as [U V].
  rewrite N.add_0_r in U,V.
  change ((s V_MEM64) Ⓠ[v+8*k]=value m0 (v+8*k) 1) in V.
  destruct UN as [UNU UNV].
  destruct sub; cbn [nc_program nc_address]; nc_bigstep;
    (exists k; split; [exact NK | ]);
    unfold nc_stage, nc_ptrs; psimpl;
    rewrite ?DI, ?SI, ?DX, ?AX; psimpl;
    repeat split; try assumption; try reflexivity.
  all: try discriminate; try assumption; try solve [lia].
  all: cbn [buffered]; psimpl.
  all: rewrite ?V.
  all: unfold nc_prefix, buffered, limb_result, limb_carry, adc_flag, sbb_flag in NP.
  all: psimpl in NP.
  all: destruct NP as [NCF [_ NEQ]].
  all: try exact NCF; try exact NEQ.
  all: assert (YB : value m0 (v+8*k) 1<2^64) by apply value_bound.
  all: cbn [N.add Pos.add Pos.add_carry Pos.succ pending_reg] in NCF, NEQ.
  all: psimpl in NCF; psimpl in NEQ.
  all: try rewrite (N.add_comm (2^64) (s R_R8)) in NCF, NEQ.
  all: rewrite <-msub_repr64 in NCF, NEQ by exact YB.
  all: repeat (rewrite update_updated || rewrite update_frame by discriminate).
  all: try exact NCF; try exact NEQ.
Qed.
