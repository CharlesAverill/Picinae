(* __memcpy_generic, AArch64, actual size partition 0 <= n <= 32.

   PROVENANCE (inherited, not a binary/lifter-refinement theorem):
   Ubuntu ARM64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Ghidra 11.4.2 explicit strict scalar replacement, e08 accepted artifacts.
   Model addresses = ELF addresses + 0x100000. Generic entry 0x19ab40
   (ELF 0x9ab40). The unchanged generated map contains 99 generic instructions
   plus nine mempcpy-wrapper instructions; this proof never enters the wrapper.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, 2026-11-03.
   Proof repair: OpenAI gpt-6.1-sol, xhigh/priority, 2026-11-03.
   Full-target validation and final proof status: notes/a-memcpy-small-fix/.

   ENGLISH SPECIFICATION / AAPCS64:
   X0=d, X1=s, X2=n; 64-bit pointers/count, n<=32. The buffers do not wrap:
   d+n<=2^64, s+n<=2^64, and have disjoint modular byte addresses. Every source
   byte is initially readable and every destination byte writable. All initial
   architectural values satisfy arm8typctx. There is no n>0, alignment, or
   non-null premise. n=0 permits d=s=0 with no memory-access premise.
   At the reached small-path RET, X0=d; every byte d+i (i<n) equals ORIGINAL
   source byte s+i, and EVERY byte outside the destination retains its initial
   value. SP, X19..X29, X30, and the distinct modeled R_LR are unchanged.
   Entire modeled Z8..Z15 values are unchanged (stronger than their AAPCS64
   low-64-bit frame). No additional CPU feature or tunable premise is used.
   The theorem stops AT RET, before transfer to X30; it does not prove
   termination, fault freedom, cache/IRQ behavior, or binary/lifter soundness.
   Medium 33..128, large 129+, mempcpy and checked wrappers are out of scope.

   Small instructions, all read from the generated map:
   19ab40 nop; 44/48 compute source/dest ends; 4c/50 cmp128/b.hi;
   54/58 cmp32/b.hi; 5c/60 cmp16/b.cc.
   16..32: 64/68 load two head/tail pairs, 6c/70 store pairs, 74 ret.
   8..15: 78 tbz bit3; 7c/80 load head/tail, 84/88 store, 8c ret.
   4..7: 90 tbz bit2; 94/98 load W head/tail, 9c/a0 store, a4 ret.
   0..3: a8 cbz to c8; ac computes n>>1; b0/b4/b8 load bytes at
   0,n-1,n>>1; bc/c0/c4 store at 0,n>>1,n-1; c8 ret.
   All nonzero small paths finish all source loads before their first store.
   Actual flag registers have width 8, with explicit low-1 branch casts.
*)

Require Import Picinae_armv8.
Require Import e08___memcpy_generic_arm8.
Require Import arm8_memcpy_common.
Import ARM8Notations.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition memcpy_small_saved : list arm8var :=
  [R_SP; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
   R_X26; R_X27; R_X28; R_X29; R_X30; R_LR;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15].
Definition memcpy_small_frame (st0 st:store) :=
  forall v, In v memcpy_small_saved -> st v = st0 v.

Definition memcpy_small_domain (st:store) (d s n:N) :=
  n <= 32 /\ d + n <= 2^64 /\ s + n <= 2^64 /\ nov d s n /\
  (forall i, i < n -> mem_readable st (s ⊕ i)) /\
  (forall i, i < n -> mem_writable st (d ⊕ i)).

Definition memcpy_small_input (st0:store) (m d s n:N) (st:store) :=
  st V_MEM64 = m /\ st R_X0 = d /\ st R_X1 = s /\ st R_X2 = n /\
  memcpy_small_frame st0 st.

Definition memcpy_small_post (st0:store) (m d s n:N) (st:store) :=
  st R_X0 = d /\ copied m (st V_MEM64) d s n /\ memcpy_small_frame st0 st.

Definition memcpy_small_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x19ab74 | 0x19ab8c | 0x19aba4 | 0x19abc8 => true
  | _ => false end | _ => false end.

Definition memcpy_small_invs (st0:store) (m d s n:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0x19ab40 => Some (memcpy_small_input st0 m d s n st)
  | 0x19ab74 | 0x19ab8c | 0x19aba4 | 0x19abc8 =>
      Some (memcpy_small_post st0 m d s n st)
  | 0x19abd0 | 0x19ac40 => Some False
  | _ => None end | _ => None end.

Theorem memcpy_small_nwc:
  forall s2 s1, e08___memcpy_generic_arm8 s1 = e08___memcpy_generic_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions memcpy_small_nwc.

Theorem memcpy_small_welltyped:
  welltyped_prog arm8typctx e08___memcpy_generic_arm8.
Proof. exact e08___memcpy_generic_arm8.welltyped. Qed.
Print Assumptions memcpy_small_welltyped.

(* This witness is symbolic: the enormous permission mask must never be
   evaluated into a concrete integer. It is a finite N value in the model. *)
Definition memcpy_small_witness (m d s n:N) : store :=
  update (update (update (update (update (update (fun _ => 0)
    A_READ (N.ones (2^64))) A_WRITE (N.ones (2^64)))
    V_MEM64 m) R_X0 d) R_X1 s) R_X2 n.

Theorem memcpy_small_witness_typed:
  forall m d s n, m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> n < 2^64 ->
  models arm8typctx (memcpy_small_witness m d s n).
Proof.
  intros m d s n M D S NN. unfold memcpy_small_witness.
  apply models_update; [exact NN|].
  apply models_update; [exact S|].
  apply models_update; [exact D|].
  apply models_update; [exact M|].
  apply models_update; [apply ones_bound|].
  apply models_update; [apply ones_bound|].
  intros v w T. apply mp2_gt_0.
Qed.
Print Assumptions memcpy_small_witness_typed.

Theorem memcpy_small_entry_inhabited:
  forall m d s n,
  m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> n <= 32 ->
  d+n <= 2^64 -> s+n <= 2^64 -> nov d s n ->
  exists st, models arm8typctx st /\ memcpy_small_domain st d s n /\
             memcpy_small_input st m d s n st.
Proof.
  intros m d s n M D S NN DN SN NOV.
  exists (memcpy_small_witness m d s n). split.
  - apply memcpy_small_witness_typed; try assumption.
    clear - NN. change (2^64) with 18446744073709551616. lia.
  - split.
    + unfold memcpy_small_domain. repeat split; try assumption.
      * intros i I. unfold mem_readable, memcpy_small_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
      * intros i I. unfold mem_writable, memcpy_small_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
    + unfold memcpy_small_input. repeat split.
      all: try (unfold memcpy_small_witness;
                rewrite ?update_frame by discriminate;
                rewrite update_updated; reflexivity).
Qed.
Print Assumptions memcpy_small_entry_inhabited.

Theorem memcpy_small_zero_entry:
  exists st, models arm8typctx st /\ memcpy_small_domain st 0 0 0 /\
             memcpy_small_input st 0 0 0 0 st.
Proof.
  apply memcpy_small_entry_inhabited; try apply mp2_gt_0;
    try (change (2^64) with 18446744073709551616; lia).
  unfold nov. intros i j I J. lia.
Qed.
Print Assumptions memcpy_small_zero_entry.

(* Bound the search by the actual small size partition. Arithmetic obligations
   are cleared of all memory terms before invoking lia. Offset selection uses
   only congruence of the actual store address, never a desired postcondition. *)
Ltac small_store_chain :=
  lazymatch goal with
  | |- cpy ?m (setmem 64 LittleE ?L ?M ?a (getmem 64 LittleE ?L ?m ?sa)) ?d ?s _ =>
    let rec seek k :=
      first
      [ let E := fresh "OFFSET" in
        assert (E: a mod 2^64 = (d+k) mod 2^64)
          by (clear - d; unfold msub;
              change (2^64) with 18446744073709551616 in *; lia);
        eapply (cpy_store m M d s _ k L a sa);
        [ small_store_chain
        | intros i I; clear - I;
          change (2^64) with 18446744073709551616; lia
        | clear; lia
        | clear; change (2^64) with 18446744073709551616; lia
        | exact E
        | clear - s; unfold msub;
          change (2^64) with 18446744073709551616 in *; lia ]
      | lazymatch eval compute in (k <? 31) with
        | true => let k' := eval compute in (k+1) in seek k'
        | false => fail "Store address is not a small destination offset"
        end ]
    in seek 0
  | |- cpy ?m ?m ?d ?s _ => apply cpy_empty
  end.

Ltac small_copied :=
  eapply cpy_copied; cycle 1;
  [ small_store_chain | intro i; split; let HI := fresh "HI" in intro HI; clear - HI; cbn in *; lia ].

Ltac small_frame_finish FRAME :=
  unfold memcpy_small_frame in *; intros v V;
  unfold memcpy_small_saved in V;
  repeat destruct V as [<-|V];
  try contradiction;
  rewrite ?update_frame by discriminate;
  apply FRAME; unfold memcpy_small_saved; simpl; tauto.

(* Defer expensive symbolic memory and width arithmetic during conversion.
   This affects unfolding order only; all proofs still receive full Qed checks. *)
Strategy 1000 [N.pow getmem setmem N.modulo N.land N.lor N.lxor
  N.shiftl N.shiftr].

(* These scratch flags are overwritten inside each lifted instruction before
   any use. NG and OV are never consulted on the small path. Abstraction only
   forgets their final values, and retains CY/ZR and every framed register. *)
Ltac ignore_vars v ::= constr:(match v with
  | R_TMPCY | R_TMPOV | R_TMPNG | R_TMPZR | R_NG | R_OV => true
  | _ => false end).

(* Memory operations are rewritten through proved contracts, never evaluated. *)
Local Opaque getmem setmem.

(* Concrete small size 0; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_0:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 0 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 0)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_0.

(* Concrete small size 1; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_1:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 1 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 1)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_1.

(* Concrete small size 2; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_2:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 2 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 2)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_2.

(* Concrete small size 3; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_3:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 3 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 3)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_3.

(* Concrete small size 4; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_4:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 4 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 4)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_4.

(* Concrete small size 5; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_5:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 5 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 5)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_5.

(* Concrete small size 6; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_6:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 6 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 6)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_6.

(* Concrete small size 7; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_7:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 7 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 7)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_7.

(* Concrete small size 8; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_8:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 8 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 8)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_8.

(* Concrete small size 9; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_9:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 9 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 9)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_9.

(* Concrete small size 10; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_10:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 10 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 10)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_10.

(* Concrete small size 11; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_11:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 11 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 11)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_11.

(* Concrete small size 12; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_12:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 12 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 12)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_12.

(* Concrete small size 13; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_13:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 13 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 13)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_13.

(* Concrete small size 14; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_14:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 14 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 14)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_14.

(* Concrete small size 15; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_15:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 15 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 15)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_15.

(* Concrete small size 16; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_16:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 16 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 16)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_16.

(* Concrete small size 17; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_17:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 17 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 17)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_17.

(* Concrete small size 18; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_18:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 18 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 18)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_18.

(* Concrete small size 19; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_19:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 19 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 19)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_19.

(* Concrete small size 20; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_20:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 20 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 20)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_20.

(* Concrete small size 21; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_21:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 21 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 21)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_21.

(* Concrete small size 22; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_22:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 22 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 22)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_22.

(* Concrete small size 23; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_23:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 23 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 23)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_23.

(* Concrete small size 24; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_24:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 24 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 24)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_24.

(* Concrete small size 25; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_25:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 25 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 25)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_25.

(* Concrete small size 26; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_26:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 26 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 26)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_26.

(* Concrete small size 27; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_27:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 27 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 27)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_27.

(* Concrete small size 28; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_28:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 28 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 28)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_28.

(* Concrete small size 29; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_29:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 29 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 29)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_29.

(* Concrete small size 30; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_30:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 30 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 30)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_30.

(* Concrete small size 31; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_31:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 31 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 31)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_31.

(* Concrete small size 32; opaque closure keeps symbolic states local. *)
Lemma memcpy_small_case_32:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_small_input st m d s 32 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_small_invs st m d s 32)
    memcpy_small_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_small_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; small_copied
    | small_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_small_case_32.

Theorem memcpy_small_correct:
  forall st t st' x' m d s n
    (ENTRY: startof t (x',st') = (Addr 0x19ab40,st))
    (MDL: models arm8typctx st)
    (MEM: st V_MEM64 = m) (DEST: st R_X0 = d)
    (SRC: st R_X1 = s) (COUNT: st R_X2 = n)
    (DOMAIN: memcpy_small_domain st d s n),
  satisfies_all e08___memcpy_generic_arm8
    (memcpy_small_invs st m d s n) memcpy_small_exit ((x',st')::t).
Proof.
  intros. destruct DOMAIN as [SMALL [DN [SN [NOV [READ WRITE]]]]].
  apply prove_invs.
  - simpl. rewrite ENTRY. arm8_step.
    unfold memcpy_small_input. repeat split; try assumption.
  - intros.
    erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply memcpy_small_welltyped. intro MDL1.
    clear - PRE MDL1 SMALL. rename t1 into t.
    destruct_inv 64 PRE.
    unfold memcpy_small_input in PRE.
    destruct PRE as [MEM [DEST [SRC [COUNT FRAME]]]].
    assert (CASES: n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31 \/ n = 32)
      by (clear - SMALL; lia).
    repeat destruct CASES as [->|CASES]; try (rewrite CASES in *; clear CASES).
    + apply memcpy_small_case_0; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_1; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_2; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_3; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_4; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_5; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_6; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_7; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_8; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_9; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_10; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_11; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_12; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_13; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_14; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_15; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_16; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_17; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_18; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_19; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_20; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_21; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_22; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_23; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_24; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_25; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_26; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_27; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_28; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_29; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_30; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_31; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).
    + apply memcpy_small_case_32; [exact MDL1|].
      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).

Qed.
Print Assumptions memcpy_small_correct.

(* A trace-scoped exported frame, derived only from the actual generic entry
   theorem. A global noassign assertion would be false for this union map. *)
Theorem memcpy_small_preserves_callee_saved:
  forall st t st' a m d s n,
    startof t (Addr a,st') = (Addr 0x19ab40,st) ->
    models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
    st R_X1 = s -> st R_X2 = n -> memcpy_small_domain st d s n ->
    exec_prog e08___memcpy_generic_arm8 ((Addr a,st')::t) ->
    unterminated memcpy_small_exit t ->
    In a [0x19ab74; 0x19ab8c; 0x19aba4; 0x19abc8] ->
    memcpy_small_frame st st'.
Proof.
  intros st t st' a m d s n ENTRY MDL MEM D S NN DOMAIN XP UT RET.
  pose proof (memcpy_small_correct st t st' (Addr a) m d s n
    ENTRY MDL MEM D S NN DOMAIN) as SA.
  pose proof (satall_trueif_inv _ _ _ _ SA XP UT) as POST.
  repeat destruct RET as [<-|RET]; try contradiction;
    cbn [memcpy_small_invs trueif_inv] in POST;
    exact (proj2 (proj2 POST)).
Qed.
Print Assumptions memcpy_small_preserves_callee_saved.
