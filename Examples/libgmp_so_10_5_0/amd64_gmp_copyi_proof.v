(* Partial functional correctness of the original AMD64 lift, including
   forward overlap and n=0.  See libgmp_invariants.md for address meanings. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.gmpn_copyi_amd64.
From Stdlib Require Import NArith Lia FunctionalExtensionality.
Import X64Notations.
Open Scope N.

Module GMP64Params <: LimbArrayParams.
  Definition w := 64.
  Definition bytes := 8.
  Global Transparent w bytes.
End GMP64Params.
Module GMP64 := LimbArrays GMP64Params.
Import GMP64.

Theorem copyi_nwc : forall s1 s2,
  libgmp_so_10_5_0___gmpn_copyi_amd64 s1 = libgmp_so_10_5_0___gmpn_copyi_amd64 s2.
Proof. reflexivity. Qed.
Theorem copyi_welltyped : welltyped_prog x64typctx libgmp_so_10_5_0___gmpn_copyi_amd64.
Proof. Picinae_typecheck. Qed.

Definition copyi_exit (t : trace) :=
  match t with (Addr 0x15b1e2, _)::_ => true | _ => false end.
Definition copyi_regs m d p k (s : store) :=
  s V_MEM64 = copied m d p k /\
  s R_RSI = (p+8*k) mod 2^64 /\ s R_RDI = (d+8*k) ⊖ 8.
Definition copyi_invset m d p n (t : trace) :=
  match t with (Addr a,s)::_ => match a with
  (* __gmpn_copyi precondition *)
  | 0x15b186 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = p /\ s R_RDX = n)
  | 0x15b190 => Some (exists k, copyi_regs m d p k s /\ k+4 <= n /\ s R_RDX = n-k-4)
  | 0x15b1bc => Some (exists k, copyi_regs m d p k s /\ k <= n /\ n-k < 4 /\ s R_RDX = (n-k) ⊖ 4)
  | 0x15b1cf => Some (exists k, copyi_regs m d p k s /\ k <= n /\ (n-k=0 \/ n-k=2) /\ s R_RDX = 2147483646+(n-k)/2)
  (* __gmpn_copyi postcondition *)
  | 0x15b1e2 => Some (s V_MEM64 = copied m d p n)
  | _ => None end | _ => None end.

Lemma copyi_more1 : forall m d p n k,
  forward_safe d p n -> k+1 <= n ->
  (copied m d p k)[Ⓠd+8*k := (copied m d p k) Ⓠ[p+8*k]] = copied m d p (k+1).
Proof.
  intros. change (setmem 64 LittleE (8*1) (copied m d p k) (d+8*k)
    (value (copied m d p k) (p+8*k) 1) = copied m d p (k+1)).
  erewrite copied_read with (n:=n) by eassumption. apply copied_more.
Qed.

Lemma copyi_more2 : forall m d p n k,
  forward_safe d p n -> k+2 <= n ->
  (copied m d p k)[Ⓠd+8*k := (copied m d p k) Ⓠ[p+8*k]]
    [Ⓠd+8*k+8 := (copied m d p k) Ⓠ[p+8*k+8]] = copied m d p (k+2).
Proof.
  intros. rewrite setmem_merge, N.mod_small by apply getmem_bound.
  change (setmem 64 LittleE (8*2) (copied m d p k) (d+8*k)
    (cbits (getmem 64 LittleE 8 (copied m d p k) (p+8*k+8)) 64
           (getmem 64 LittleE 8 (copied m d p k) (p+8*k))) = copied m d p (k+2)).
  rewrite <- (getmem_split 64 LittleE 8 8).
  change (setmem 64 LittleE (8*2) (copied m d p k) (d+8*k)
    (value (copied m d p k) (p+8*k) 2) = copied m d p (k+2)).
  erewrite copied_read with (n:=n) by eassumption. apply copied_more.
Qed.

Lemma copyi_more4 : forall m d p n k,
  forward_safe d p n -> k+4 <= n ->
  (copied m d p k)[Ⓠd+8*k := (copied m d p k) Ⓠ[p+8*k]]
    [Ⓠd+8*k+8 := (copied m d p k) Ⓠ[p+8*k+8]]
    [Ⓠd+8*k+16 := (copied m d p k) Ⓠ[p+8*k+16]]
    [Ⓠd+8*k+24 := (copied m d p k) Ⓠ[p+8*k+24]] = copied m d p (k+4).
Proof.
  intros. rewrite setmem_merge, N.mod_small by apply getmem_bound.
  rewrite <- (getmem_split 64 LittleE 8 8).
  replace (d+8*k+16) with ((d+8*k)+(8+8)) by lia.
  rewrite setmem_merge, N.mod_small by apply getmem_bound.
  rewrite <- (getmem_split 64 LittleE 16 8).
  replace (d+8*k+24) with ((d+8*k)+(8+8+8)) by lia.
  rewrite setmem_merge.
  rewrite N.mod_small by apply getmem_bound.
  rewrite <- (getmem_split 64 LittleE 24 8).
  change (setmem 64 LittleE (8*4) (copied m d p k) (d+8*k)
    (value (copied m d p k) (p+8*k) 4) = copied m d p (k+4)).
  erewrite copied_read with (n:=n) by eassumption. apply copied_more.
Qed.

Lemma copyi_vc_entry : forall m d p n s t,
  d < 2^64 -> p < 2^64 -> n < 2^64 ->
  s V_MEM64 = m -> s R_RDI = d -> s R_RSI = p -> s R_RDX = n ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_invset m d p n) copyi_exit false ((Addr 0x15b186,s)::t).
Proof.
  intros m d p n s t D64 P64 N64 M D P C.
  libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep.
  all: rewrite ?M, ?D, ?P, ?C in *.
  all: psimpl.
  all: repeat match goal with H : (_ <? _) = true |- _ => apply N.ltb_lt in H | H : (_ <? _) = false |- _ => apply N.ltb_ge in H end.
  - exists 0. unfold copyi_regs. psimpl. rewrite copied_zero.
    repeat split; try assumption; try reflexivity.
    lia.
  - exists 0. unfold copyi_regs. psimpl. rewrite copied_zero.
    repeat split; try assumption; try reflexivity.
    lia.
Qed.

Lemma copyi_vc_loop : forall m d p n s t,
  n < 2^64 -> forward_safe d p n ->
  (exists k, copyi_regs m d p k s /\ k+4 <= n /\ s R_RDX=n-k-4) ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_invset m d p n) copyi_exit false ((Addr 0x15b190,s)::t).
Proof.
  intros m d p n s t N64 SAFE [k [[M [P D]] [KN C]]].
  libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep.
  all: rewrite ?M, ?D, ?P, ?C in *.
  all: unfold copyi_regs; psimpl.
  all: repeat match goal with H : (_ <? _) = true |- _ => apply N.ltb_lt in H | H : (_ <? _) = false |- _ => apply N.ltb_ge in H end.
  all: exists (k+4); repeat split.
  all: try solve [lia].
  all: try solve [replace (n-(k+4)) with (n-k-4) by lia; reflexivity].
  all: try solve [replace (d+8*(k+4)) with (32+(d+8*k)) by nia; psimpl; reflexivity].
  all: try solve [replace (p+8*(k+4)) with (32+p+8*k) by nia; reflexivity].
  all: try solve [rewrite msub_sub, N.mod_small by lia; lia].
  all: try solve [
    replace (8+d+8*k) with (d+8*k+8) by lia;
    replace (16+d+8*k) with (d+8*k+16) by lia;
    replace (24+d+8*k) with (d+8*k+24) by lia;
    replace (8+p+8*k) with (p+8*k+8) by lia;
    replace (16+p+8*k) with (p+8*k+16) by lia;
    replace (24+p+8*k) with (p+8*k+24) by lia;
    eapply copyi_more4; eassumption].
Qed.

Lemma copyi_vc_tail1 : forall m d p n s t,
  forward_safe d p n ->
  (exists k, copyi_regs m d p k s /\ k<=n /\ n-k<4 /\ s R_RDX=(n-k) ⊖ 4) ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_invset m d p n) copyi_exit false ((Addr 0x15b1bc,s)::t).
Proof.
  intros m d p n s t SAFE [k [[M [P D]] [KN [REM C]]]].
  assert (CASES : n-k=0 \/ n-k=1 \/ n-k=2 \/ n-k=3) by lia.
  destruct CASES as [E|[E|[E|E]]]; rewrite E in C.
  all: libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep.
  all: rewrite ?M, ?D, ?P, ?C in *.
  all: try discriminate.
  all: psimpl.
  all: unfold copyi_regs; psimpl.
  all: try change (scast 32 64 ((0 ⊖ 4 >> 0) mod 2^32 >> 1) mod 2^32) with 2147483646.
  all: try change (scast 32 64 ((1 ⊖ 4 >> 0) mod 2^32 >> 1) mod 2^32) with 2147483646.
  all: try change (scast 32 64 ((2 ⊖ 4 >> 0) mod 2^32 >> 1) mod 2^32) with 2147483647.
  all: try change (scast 32 64 ((3 ⊖ 4 >> 0) mod 2^32 >> 1) mod 2^32) with 2147483647.
  1: exists k.
  2: exists (k+1).
  3: exists k.
  4: exists (k+1).
  all: repeat split; try reflexivity; try assumption.
  all: try solve [eapply copyi_more1; [exact SAFE | clear -KN E; lia]].
  all: try solve [rewrite E; reflexivity].
  all: try solve [replace (n-(k+1)) with (n-k-1) by (clear -KN E; lia); rewrite E; reflexivity].
  all: try solve [replace (p+8*(k+1)) with (8+p+8*k) by (clear; nia); reflexivity].
  all: try solve [replace (d+8*(k+1)) with (8+(d+8*k)) by (clear; nia); psimpl; reflexivity].
  all: try solve [clear -KN E; lia | left; clear -KN E; lia | right; clear -KN E; lia].
Qed.

Lemma copyi_vc_tail2 : forall m d p n s t,
  forward_safe d p n ->
  (exists k, copyi_regs m d p k s /\ k<=n /\ (n-k=0 \/ n-k=2) /\ s R_RDX=2147483646+(n-k)/2) ->
  nextinv libgmp_so_10_5_0___gmpn_copyi_amd64 (copyi_invset m d p n) copyi_exit false ((Addr 0x15b1cf,s)::t).
Proof.
  intros m d p n s t SAFE [k [[M [P D]] [KN [CASES C]]]].
  destruct CASES as [E|E]; rewrite E in C.
  all: libgmp_so_10_5_0___gmpn_copyi_amd64_bigstep.
  all: rewrite ?M, ?D, ?P, ?C in *.
  all: try discriminate.
  all: psimpl.
  - replace n with k by lia. reflexivity.
  - replace n with (k+2) by lia.
    replace (8+d+8*k) with (d+8*k+8) by lia.
    replace (8+p+8*k) with (p+8*k+8) by lia.
    eapply copyi_more2; [exact SAFE | lia].
Qed.


Theorem copyi_functional_correctness :
  forall s d p n m t s' x'
    (ENTRY : startof t (x',s') = (Addr 0x15b186,s))
    (MDL : models x64typctx s)
    (MEM : s V_MEM64=m) (DST : s R_RDI=d) (SRC : s R_RSI=p) (LEN : s R_RDX=n)
    (SAFE : forward_safe d p n),
  satisfies_all libgmp_so_10_5_0___gmpn_copyi_amd64
    (copyi_invset m d p n) copyi_exit ((x',s')::t).
Proof.
  intros.
  assert (D64 := models_var R_RDI MDL). rewrite DST in D64. change (d<2^64) in D64.
  assert (P64 := models_var R_RSI MDL). rewrite SRC in P64. change (p<2^64) in P64.
  assert (N64 := models_var R_RDX MDL). rewrite LEN in N64. change (n<2^64) in N64.
  apply prove_invs.
  - simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  - intros. clear -PRE D64 P64 N64 SAFE.
    destruct_inv 64 PRE.
    + destruct PRE as [M [D [P C]]]. eapply copyi_vc_entry; eassumption.
    + eapply copyi_vc_loop; eassumption.
    + eapply copyi_vc_tail1; eassumption.
    + eapply copyi_vc_tail2; eassumption.
Qed.
