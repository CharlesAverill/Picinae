(* PARTIAL Astra one-shot handoff: full build failed with out-of-memory.
   Only the prefix through case_46 reached Qed; no full target .vo exists.
   Unfinished statements remain below with Abort. No second author build. *)
(* __memcpy_generic, AArch64: ONLY actual medium size paths 33 <= n <= 128.

   PROVENANCE (inherited; not a binary/lifter-refinement certificate):
   Ubuntu ARM64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Ghidra 11.4.2 strict scalar replacement, accepted e08 union map, unchanged:
   99 generic instructions plus nine mempcpy wrapper instructions. Model
   addresses = ELF addresses + 0x100000; generic entry is 0x19ab40.
   Initial author: OpenAI gpt-6-astra, xhigh/default, 2026-11-03.
   Initial proof adapted from accepted Astra/Sol arm8_memcpy_small_proof.v;
   shared pure helpers from arm8_memcpy_common.v are imported unchanged.
   Final proof producer/status: see notes/a-memcpy-medium/README.md.

   ENGLISH SPECIFICATION / AAPCS64:
   X0=d, X1=s, X2=n are 64-bit. Initially typed ARM8 state; 33<=n<=128;
   d+n<=2^64 and s+n<=2^64; modular source/destination byte sets disjoint;
   every source byte readable and destination byte writable. There are no
   extra alignment, non-null, CPU-feature, or tunable hypotheses.
   At either reached medium RET cut, X0=d; each destination byte equals its
   ORIGINAL source byte; EVERY byte outside the destination is unchanged.
   SP, X19..X29, X30, distinct modeled R_LR, and whole modeled Z8..Z15
   are unchanged. The theorem stops AT RET, before executing the transfer
   through X30. It proves IL partial correctness, not termination, accessible
   execution/fault freedom, hardware behavior, or binary-to-IL soundness.

   Actual size branches:
   33..64: loads head32/tail32, stores them, RET 0x19abf8.
   65..96: also loads/stores head[32,64), RET 0x19ac38.
   97..128: also loads/stores tail[n-64,n-32), RET 0x19ac38.
   All source loads precede the first store on all three paths. The proof
   executes the original map, including entry size dispatch, with separate
   opaque lemmas for each size to bound symbolic-state growth. Small/large
   copy, mempcpy and checked wrappers are NOT covered by this theorem.
*)

Require Import Picinae_armv8.
Require Import e08___memcpy_generic_arm8.
Require Import arm8_memcpy_common.
Import ARM8Notations.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition memcpy_medium_saved : list arm8var :=
  [R_SP; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
   R_X26; R_X27; R_X28; R_X29; R_X30; R_LR;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15].
Definition memcpy_medium_frame (st0 st:store) :=
  forall v, In v memcpy_medium_saved -> st v = st0 v.

Definition memcpy_medium_domain (st:store) (d s n:N) :=
  33 <= n <= 128 /\ d + n <= 2^64 /\ s + n <= 2^64 /\ nov d s n /\
  (forall i, i < n -> mem_readable st (s ⊕ i)) /\
  (forall i, i < n -> mem_writable st (d ⊕ i)).

Definition memcpy_medium_input (st0:store) (m d s n:N) (st:store) :=
  st V_MEM64 = m /\ st R_X0 = d /\ st R_X1 = s /\ st R_X2 = n /\
  memcpy_medium_frame st0 st.

Definition memcpy_medium_post (st0:store) (m d s n:N) (st:store) :=
  st R_X0 = d /\ copied m (st V_MEM64) d s n /\ memcpy_medium_frame st0 st.

Definition memcpy_medium_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x19abf8 | 0x19ac38 => true
  | _ => false end | _ => false end.

Definition memcpy_medium_invs (st0:store) (m d s n:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0x19ab40 => Some (memcpy_medium_input st0 m d s n st)
  | 0x19abf8 | 0x19ac38 =>
      Some (memcpy_medium_post st0 m d s n st)
  | 0x19ab5c | 0x19ac40 => Some False
  | _ => None end | _ => None end.

Theorem memcpy_medium_nwc:
  forall s2 s1, e08___memcpy_generic_arm8 s1 = e08___memcpy_generic_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions memcpy_medium_nwc.

Theorem memcpy_medium_welltyped:
  welltyped_prog arm8typctx e08___memcpy_generic_arm8.
Proof. exact e08___memcpy_generic_arm8.welltyped. Qed.
Print Assumptions memcpy_medium_welltyped.

(* This witness is symbolic: the enormous permission mask must never be
   evaluated into a concrete integer. It is a finite N value in the model. *)
Definition memcpy_medium_witness (m d s n:N) : store :=
  update (update (update (update (update (update (fun _ => 0)
    A_READ (N.ones (2^64))) A_WRITE (N.ones (2^64)))
    V_MEM64 m) R_X0 d) R_X1 s) R_X2 n.

Theorem memcpy_medium_witness_typed:
  forall m d s n, m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> n < 2^64 ->
  models arm8typctx (memcpy_medium_witness m d s n).
Proof.
  intros m d s n M D S NN. unfold memcpy_medium_witness.
  apply models_update; [exact NN|].
  apply models_update; [exact S|].
  apply models_update; [exact D|].
  apply models_update; [exact M|].
  apply models_update; [apply ones_bound|].
  apply models_update; [apply ones_bound|].
  intros v w T. apply mp2_gt_0.
Qed.
Print Assumptions memcpy_medium_witness_typed.

Theorem memcpy_medium_entry_inhabited:
  forall m d s n,
  m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> 33 <= n <= 128 ->
  d+n <= 2^64 -> s+n <= 2^64 -> nov d s n ->
  exists st, models arm8typctx st /\ memcpy_medium_domain st d s n /\
             memcpy_medium_input st m d s n st.
Proof.
  intros m d s n M D S NN DN SN NOV.
  exists (memcpy_medium_witness m d s n). split.
  - apply memcpy_medium_witness_typed; try assumption.
    clear - NN. change (2^64) with 18446744073709551616. lia.
  - split.
    + unfold memcpy_medium_domain. repeat split; try assumption;
        try (exact (proj1 NN)); try (exact (proj2 NN)).
      * intros i I. unfold mem_readable, memcpy_medium_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
      * intros i I. unfold mem_writable, memcpy_medium_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
    + unfold memcpy_medium_input. repeat split.
      all: try (unfold memcpy_medium_witness;
                rewrite ?update_frame by discriminate;
                rewrite update_updated; reflexivity).
Qed.
Print Assumptions memcpy_medium_entry_inhabited.

Theorem memcpy_medium_alignment_witness:
  forall m da sa n,
    m < 2^(8*2^64) -> da < 16 -> sa < 16 -> 33 <= n <= 128 ->
    exists st, models arm8typctx st /\
      memcpy_medium_domain st da (256+sa) n /\
      memcpy_medium_input st m da (256+sa) n st.
Proof.
  intros m da sa n M DA SA NN. apply memcpy_medium_entry_inhabited.
  - exact M.
  - clear - DA. change (2^64) with 18446744073709551616. lia.
  - clear - SA. change (2^64) with 18446744073709551616. lia.
  - exact NN.
  - clear - DA NN. change (2^64) with 18446744073709551616. lia.
  - clear - SA NN. change (2^64) with 18446744073709551616. lia.
  - unfold nov. intros i j I J. clear - DA SA NN I J.
    change (2^64) with 18446744073709551616.
    rewrite !N.mod_small by lia. lia.
Qed.
Print Assumptions memcpy_medium_alignment_witness.

(* Bound the search by the actual medium size partition. Arithmetic obligations
   are cleared of all memory terms before invoking lia. Offset selection uses
   only congruence of the actual store address, never a desired postcondition. *)
Ltac medium_store_chain :=
  lazymatch goal with
  | |- cpy ?m (setmem 64 LittleE ?L ?M ?a (getmem 64 LittleE ?L ?m ?sa)) ?d ?s _ =>
    let rec seek k :=
      first
      [ let E := fresh "OFFSET" in
        assert (E: a mod 2^64 = (d+k) mod 2^64)
          by (clear - d; unfold msub;
              change (2^64) with 18446744073709551616 in *; lia);
        eapply (cpy_store m M d s _ k L a sa);
        [ medium_store_chain
        | intros i I; clear - I;
          change (2^64) with 18446744073709551616; lia
        | clear; lia
        | clear; change (2^64) with 18446744073709551616; lia
        | exact E
        | clear - s; unfold msub;
          change (2^64) with 18446744073709551616 in *; lia ]
      | lazymatch eval compute in (k <? 127) with
        | true => let k' := eval compute in (k+1) in seek k'
        | false => fail "Store address is not a medium destination offset"
        end ]
    in seek 0
  | |- cpy ?m ?m ?d ?s _ => apply cpy_empty
  end.

Ltac medium_copied :=
  eapply cpy_copied; cycle 1;
  [ medium_store_chain | intro i; split; let HI := fresh "HI" in intro HI; clear - HI; cbn in *; lia ].

Ltac medium_frame_finish FRAME :=
  unfold memcpy_medium_frame in *; intros v V;
  unfold memcpy_medium_saved in V;
  repeat destruct V as [<-|V];
  try contradiction;
  rewrite ?update_frame by discriminate;
  apply FRAME; unfold memcpy_medium_saved; simpl; tauto.

(* Defer expensive symbolic memory and width arithmetic during conversion.
   This affects unfolding order only; all proofs still receive full Qed checks. *)
Strategy 1000 [N.pow getmem setmem N.modulo N.land N.lor N.lxor
  N.shiftl N.shiftr].

(* These scratch flags are overwritten inside each lifted instruction before
   any use. NG and OV are never consulted on the medium paths. Abstraction only
   forgets their final values, and retains CY/ZR and every framed register. *)
Ltac ignore_vars v ::= constr:(match v with
  | R_TMPCY | R_TMPOV | R_TMPNG | R_TMPZR | R_NG | R_OV => true
  | _ => false end).

(* Memory operations are rewritten through proved contracts, never evaluated. *)
Local Opaque getmem setmem.

(* Concrete medium size 33; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_33:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 33 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 33)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_33.

(* Concrete medium size 34; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_34:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 34 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 34)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_34.

(* Concrete medium size 35; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_35:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 35 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 35)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_35.

(* Concrete medium size 36; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_36:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 36 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 36)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_36.

(* Concrete medium size 37; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_37:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 37 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 37)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_37.

(* Concrete medium size 38; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_38:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 38 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 38)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_38.

(* Concrete medium size 39; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_39:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 39 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 39)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_39.

(* Concrete medium size 40; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_40:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 40 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 40)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_40.

(* Concrete medium size 41; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_41:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 41 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 41)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_41.

(* Concrete medium size 42; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_42:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 42 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 42)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_42.

(* Concrete medium size 43; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_43:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 43 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 43)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_43.

(* Concrete medium size 44; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_44:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 44 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 44)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_44.

(* Concrete medium size 45; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_45:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 45 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 45)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_45.

(* Concrete medium size 46; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_46:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 46 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 46)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s t s1 MDL1 [MEM [DEST [SRC [COUNT FRAME]]]].
  repeat arm8_step;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end);
    unfold memcpy_medium_post;
    split; [reflexivity|]; split;
    [ rewrite ?MEM, ?getmem_mod_r, ?setmem_mod_r,
        ?getmem_mod_l, ?setmem_mod_l; medium_copied
    | medium_frame_finish FRAME ].
Qed.
Print Assumptions memcpy_medium_case_46.

(* Concrete medium size 47; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_47:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 47 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 47)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 48; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_48:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 48 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 48)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 49; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_49:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 49 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 49)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 50; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_50:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 50 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 50)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 51; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_51:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 51 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 51)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 52; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_52:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 52 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 52)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 53; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_53:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 53 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 53)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 54; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_54:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 54 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 54)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 55; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_55:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 55 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 55)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 56; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_56:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 56 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 56)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 57; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_57:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 57 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 57)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 58; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_58:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 58 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 58)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 59; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_59:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 59 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 59)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 60; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_60:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 60 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 60)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 61; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_61:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 61 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 61)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 62; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_62:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 62 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 62)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 63; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_63:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 63 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 63)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 64; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_64:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 64 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 64)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 65; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_65:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 65 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 65)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 66; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_66:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 66 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 66)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 67; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_67:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 67 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 67)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 68; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_68:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 68 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 68)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 69; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_69:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 69 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 69)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 70; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_70:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 70 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 70)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 71; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_71:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 71 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 71)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 72; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_72:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 72 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 72)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 73; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_73:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 73 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 73)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 74; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_74:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 74 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 74)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 75; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_75:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 75 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 75)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 76; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_76:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 76 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 76)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 77; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_77:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 77 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 77)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 78; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_78:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 78 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 78)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 79; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_79:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 79 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 79)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 80; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_80:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 80 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 80)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 81; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_81:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 81 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 81)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 82; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_82:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 82 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 82)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 83; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_83:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 83 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 83)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 84; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_84:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 84 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 84)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 85; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_85:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 85 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 85)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 86; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_86:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 86 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 86)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 87; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_87:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 87 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 87)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 88; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_88:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 88 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 88)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 89; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_89:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 89 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 89)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 90; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_90:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 90 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 90)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 91; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_91:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 91 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 91)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 92; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_92:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 92 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 92)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 93; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_93:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 93 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 93)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 94; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_94:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 94 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 94)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 95; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_95:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 95 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 95)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 96; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_96:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 96 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 96)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 97; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_97:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 97 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 97)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 98; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_98:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 98 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 98)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 99; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_99:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 99 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 99)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 100; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_100:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 100 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 100)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 101; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_101:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 101 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 101)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 102; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_102:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 102 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 102)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 103; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_103:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 103 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 103)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 104; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_104:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 104 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 104)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 105; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_105:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 105 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 105)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 106; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_106:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 106 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 106)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 107; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_107:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 107 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 107)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 108; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_108:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 108 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 108)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 109; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_109:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 109 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 109)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 110; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_110:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 110 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 110)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 111; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_111:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 111 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 111)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 112; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_112:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 112 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 112)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 113; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_113:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 113 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 113)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 114; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_114:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 114 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 114)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 115; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_115:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 115 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 115)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 116; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_116:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 116 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 116)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 117; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_117:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 117 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 117)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 118; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_118:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 118 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 118)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 119; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_119:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 119 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 119)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 120; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_120:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 120 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 120)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 121; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_121:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 121 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 121)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 122; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_122:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 122 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 122)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 123; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_123:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 123 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 123)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 124; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_124:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 124 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 124)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 125; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_125:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 125 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 125)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 126; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_126:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 126 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 126)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 127; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_127:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 127 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 127)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* Concrete medium size 128; opaque closure keeps symbolic states local. *)
Lemma memcpy_medium_case_128:
  forall st m d s t s1,
  models arm8typctx s1 -> memcpy_medium_input st m d s 128 s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_medium_invs st m d s 128)
    memcpy_medium_exit false ((Addr 0x19ab40,s1)::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

Theorem memcpy_medium_correct:
  forall st t st' x' m d s n
    (ENTRY: startof t (x',st') = (Addr 0x19ab40,st))
    (MDL: models arm8typctx st)
    (MEM: st V_MEM64 = m) (DEST: st R_X0 = d)
    (SRC: st R_X1 = s) (COUNT: st R_X2 = n)
    (DOMAIN: memcpy_medium_domain st d s n),
  satisfies_all e08___memcpy_generic_arm8
    (memcpy_medium_invs st m d s n) memcpy_medium_exit ((x',st')::t).
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

(* A trace-scoped exported frame, derived only from the actual generic entry
   theorem. A global noassign assertion would be false for this union map. *)
Theorem memcpy_medium_preserves_callee_saved:
  forall st t st' a m d s n,
    startof t (Addr a,st') = (Addr 0x19ab40,st) ->
    models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
    st R_X1 = s -> st R_X2 = n -> memcpy_medium_domain st d s n ->
    exec_prog e08___memcpy_generic_arm8 ((Addr a,st')::t) ->
    unterminated memcpy_medium_exit t ->
    In a [0x19abf8; 0x19ac38] ->
    memcpy_medium_frame st st'.
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)

Theorem memcpy_medium_at_ret:
  forall st t st' a m d s n,
    startof t (Addr a,st') = (Addr 0x19ab40,st) ->
    models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
    st R_X1 = s -> st R_X2 = n -> memcpy_medium_domain st d s n ->
    exec_prog e08___memcpy_generic_arm8 ((Addr a,st')::t) ->
    unterminated memcpy_medium_exit t ->
    In a [0x19abf8; 0x19ac38] ->
    memcpy_medium_post st m d s n st'.
Proof.
Abort.
(* Initial script preserved verbatim in notes/a-memcpy-medium/initial-proof.v.txt. *)
