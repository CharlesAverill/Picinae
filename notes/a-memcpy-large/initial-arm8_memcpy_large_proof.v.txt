(* __memcpy_generic, AArch64, large path: n > 128.

   Inherited provenance (NOT a binary-to-IL refinement theorem): Ubuntu ARM64
   /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Accepted e08 strict scalar Ghidra 11.4.2 map; model = ELF + 0x100000.
   Entry 0x19ab40, alignment/head 0x19ac40..6c, loop 0x19ac70..94,
   tail 0x19ac98..c4, exit AT RET 0x19acc8, before transfer to X30.
   Initial theorem/proof author: OpenAI gpt-6-astra, xhigh/default, 2026-11-03.
   One-shot validation and final status: notes/a-memcpy-large/README.md.

   AAPCS64 input: typed store, X0=d, X1=s, X2=n, n>128, original memory m;
   d+n<=2^64 and s+n<=2^64, modular nonoverlap, source readable and
   destination writable for each of the n bytes. No alignment, non-null,
   d/s>=16, strict end-pointer bound, CPU extension or tunable premise.
   We DERIVE n<=2^63 from two disjoint nonwrapping intervals. The equality
   case is permitted. Alignment cursors use modular subtraction. End pointers
   are modular, including 0 when the mathematical end equals 2^64.
   Output: X0=d; each destination byte equals the ORIGINAL source byte;
   every outside byte, SP, X19..X30, modeled R_LR, Z8..Z15 preserved.
   Sequential IL partial correctness only: no termination, hardware faults,
   cache/IRQ/concurrency, lifter soundness, medium/small/composition claim.

   At the loop/tail cut q is the first offset of the eight buffered qwords.
   W(q) = [0,16) union [0,q). X3+16=d+q, X1=s+q+48 (mod 2^64).
   The loop is selected iff n>q+128. One iteration writes [q,q+64),
   buffers [q+64,q+128), and advances q by 64. Tail requires
   q+64<=n<=q+128: draining the buffer plus [n-64,n) covers [0,n).
   Source loads after writes use nov and cpy_load, never current-source
   equality as an unproved hypothesis. No callee/helper execution contracts.
*)
Require Import Picinae_armv8.
Require Import e08___memcpy_generic_arm8.
Require Import arm8_memcpy_common.
Import ARM8Notations.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition memcpy_large_saved : list arm8var :=
  [R_SP; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
   R_X26; R_X27; R_X28; R_X29; R_X30; R_LR;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15].
Definition memcpy_large_frame (st0 st:store) :=
  forall v, In v memcpy_large_saved -> st v = st0 v.
Definition memcpy_large_domain (st:store) (d s n:N) :=
  128 < n /\ d+n <= 2^64 /\ s+n <= 2^64 /\ nov d s n /\
  (forall i, i<n -> mem_readable st (s ⊕ i)) /\
  (forall i, i<n -> mem_writable st (d ⊕ i)).
Definition memcpy_large_input (st0:store) (m d s n:N) (st:store) :=
  st V_MEM64 = m /\ st R_X0 = d /\ st R_X1 = s /\ st R_X2 = n /\
  memcpy_large_frame st0 st.
Definition memcpy_large_post (st0:store) (m d s n:N) (st:store) :=
  st R_X0 = d /\ copied m (st V_MEM64) d s n /\ memcpy_large_frame st0 st.
Definition memcpy_large_head (st0:store) (m d s n:N) (st:store) :=
  memcpy_large_input st0 m d s n st /\
  st R_X4 = s ⊕ n /\ st R_X5 = d ⊕ n.
Definition memcpy_large_written (q i:N) := i<16 \/ i<q.
Definition memcpy_large_buffer (st0:store) (m d s n q:N) (st:store) :=
  0<q /\ q+64<=n /\
  st R_X0 = d /\ st R_X3 = msub 64 (d ⊕ q) 16 /\
  st R_X1 = s ⊕ (q+48) /\ st R_X4 = s ⊕ n /\ st R_X5 = d ⊕ n /\
  st R_X6  = getmem 64 LittleE 8 m (s ⊕ q) /\
  st R_X7  = getmem 64 LittleE 8 m (s ⊕ (q+8)) /\
  st R_X8  = getmem 64 LittleE 8 m (s ⊕ (q+16)) /\
  st R_X9  = getmem 64 LittleE 8 m (s ⊕ (q+24)) /\
  st R_X10 = getmem 64 LittleE 8 m (s ⊕ (q+32)) /\
  st R_X11 = getmem 64 LittleE 8 m (s ⊕ (q+40)) /\
  st R_X12 = getmem 64 LittleE 8 m (s ⊕ (q+48)) /\
  st R_X13 = getmem 64 LittleE 8 m (s ⊕ (q+56)) /\
  cpy m (st V_MEM64) d s (memcpy_large_written q) /\
  memcpy_large_frame st0 st.
Definition memcpy_large_loop (st0:store) (m d s n:N) (st:store) :=
  exists q, memcpy_large_buffer st0 m d s n q st /\
            q+128<n /\ st R_X2 = n-(q+128).
Definition memcpy_large_tail (st0:store) (m d s n:N) (st:store) :=
  exists q, memcpy_large_buffer st0 m d s n q st /\ n<=q+128.
Definition memcpy_large_exit (t:trace) :=
  match t with (Addr 0x19acc8,_)::_ => true | _ => false end.
Definition memcpy_large_invs (st0:store) (m d s n:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0x19ab40 => Some (memcpy_large_input st0 m d s n st)
  | 0x19ac40 => Some (memcpy_large_head st0 m d s n st)
  | 0x19ac70 => Some (memcpy_large_loop st0 m d s n st)
  | 0x19ac98 => Some (memcpy_large_tail st0 m d s n st)
  | 0x19acc8 => Some (memcpy_large_post st0 m d s n st)
  | 0x19ab54 => Some False
  | _ => None end | _ => None end.

Theorem memcpy_large_nwc:
  forall s2 s1, e08___memcpy_generic_arm8 s1 = e08___memcpy_generic_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions memcpy_large_nwc.
Theorem memcpy_large_welltyped:
  welltyped_prog arm8typctx e08___memcpy_generic_arm8.
Proof. exact e08___memcpy_generic_arm8.welltyped. Qed.
Print Assumptions memcpy_large_welltyped.

(* Linear separation is a consequence of the modular NOV premise. *)
Lemma memcpy_large_separated:
  forall d s n, 0<n -> d+n<=2^64 -> s+n<=2^64 -> nov d s n ->
  d+n<=s \/ s+n<=d.
Proof.
  intros d s n POS DN SN NOV.
  destruct (N.le_gt_cases d s) as [DS|DS].
  - left. destruct (N.le_gt_cases (d+n) s) as [H|H]; [exact H|].
    exfalso. apply (NOV (s-d) 0); try lia.
    replace (d+(s-d)) with s by lia. rewrite N.add_0_r. reflexivity.
  - right. destruct (N.le_gt_cases (s+n) d) as [H|H]; [exact H|].
    exfalso. apply (NOV 0 (d-s)); try lia.
    replace (s+(d-s)) with d by lia. rewrite N.add_0_r. reflexivity.
Qed.
Print Assumptions memcpy_large_separated.
Lemma memcpy_large_size_bound:
  forall d s n, 0<n -> d+n<=2^64 -> s+n<=2^64 -> nov d s n -> n<=2^63.
Proof.
  intros d s n POS DN SN NOV.
  pose proof (memcpy_large_separated d s n POS DN SN NOV) as SEP.
  clear NOV. change (2^64) with 18446744073709551616 in *.
  change (2^63) with 9223372036854775808. destruct SEP; lia.
Qed.
Print Assumptions memcpy_large_size_bound.
Lemma memcpy_large_nov_of_separated:
  forall d s n, d+n<=2^64 -> s+n<=2^64 ->
  (d+n<=s \/ s+n<=d) -> nov d s n.
Proof.
  intros d s n DN SN SEP i j I J.
  rewrite !N.mod_small by lia. destruct SEP; lia.
Qed.
Print Assumptions memcpy_large_nov_of_separated.

Definition memcpy_large_witness (m d s n:N) : store :=
  update (update (update (update (update (update (fun _ => 0)
    A_READ (N.ones (2^64))) A_WRITE (N.ones (2^64)))
    V_MEM64 m) R_X0 d) R_X1 s) R_X2 n.
Theorem memcpy_large_witness_typed:
  forall m d s n, m<2^(8*2^64) -> d<2^64 -> s<2^64 -> n<2^64 ->
  models arm8typctx (memcpy_large_witness m d s n).
Proof.
  intros m d s n M D S NN. unfold memcpy_large_witness.
  apply models_update; [exact NN|].
  apply models_update; [exact S|].
  apply models_update; [exact D|].
  apply models_update; [exact M|].
  apply models_update; [apply ones_bound|].
  apply models_update; [apply ones_bound|].
  intros v w T. apply mp2_gt_0.
Qed.
Print Assumptions memcpy_large_witness_typed.
Theorem memcpy_large_entry_inhabited:
  forall m d s n, m<2^(8*2^64) -> 128<n ->
  d+n<=2^64 -> s+n<=2^64 -> nov d s n ->
  exists st, models arm8typctx st /\ memcpy_large_domain st d s n /\
             memcpy_large_input st m d s n st.
Proof.
  intros m d s n M NN DN SN NOV.
  pose proof (memcpy_large_size_bound d s n ltac:(lia) DN SN NOV) as SIZE.
  exists (memcpy_large_witness m d s n). split.
  - apply memcpy_large_witness_typed; try assumption.
    all: clear - NN DN SN SIZE;
      change (2^64) with 18446744073709551616 in *;
      change (2^63) with 9223372036854775808 in *; lia.
  - split.
    + unfold memcpy_large_domain. repeat split; try assumption.
      * intros i I. unfold mem_readable, memcpy_large_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
      * intros i I. unfold mem_writable, memcpy_large_witness.
        rewrite !update_frame by discriminate. rewrite update_updated.
        apply N.ones_spec_low. apply N.mod_lt. discriminate.
    + unfold memcpy_large_input. repeat split.
      all: try (unfold memcpy_large_witness;
                rewrite ?update_frame by discriminate;
                rewrite update_updated; reflexivity).
Qed.
Print Assumptions memcpy_large_entry_inhabited.
Theorem memcpy_large_zero_source_entry:
  exists st, models arm8typctx st /\ memcpy_large_domain st 4095 0 129 /\
             memcpy_large_input st 0 4095 0 129 st.
Proof.
  apply memcpy_large_entry_inhabited; try apply mp2_gt_0;
    try (change (2^64) with 18446744073709551616; lia).
  apply memcpy_large_nov_of_separated;
    change (2^64) with 18446744073709551616; lia.
Qed.
Print Assumptions memcpy_large_zero_source_entry.
Theorem memcpy_large_wrapped_end_entry:
  exists st, models arm8typctx st /\
    memcpy_large_domain st 0 (2^64-129) 129 /\
    memcpy_large_input st 0 0 (2^64-129) 129 st.
Proof.
  apply memcpy_large_entry_inhabited; try apply mp2_gt_0;
    try (change (2^64) with 18446744073709551616; lia).
  apply memcpy_large_nov_of_separated;
    change (2^64) with 18446744073709551616; lia.
Qed.
Print Assumptions memcpy_large_wrapped_end_entry.

Lemma memcpy_large_written_bound:
  forall n q i, 128<n -> q+64<=n -> memcpy_large_written q i -> i<n.
Proof. unfold memcpy_large_written. intros n q i NN Q [I|I]; lia. Qed.
Print Assumptions memcpy_large_written_bound.
Lemma memcpy_large_written_advance:
  forall q i, 0<q ->
  (memcpy_large_written q i \/ q<=i<q+64) <-> memcpy_large_written (q+64) i.
Proof. unfold memcpy_large_written. intros; lia. Qed.
Print Assumptions memcpy_large_written_advance.
Lemma memcpy_large_tail_cover:
  forall n q i, 128<n -> 0<q -> q+64<=n -> n<=q+128 ->
  (memcpy_large_written q i \/ q<=i<q+64 \/ n-64<=i<n) <-> i<n.
Proof. unfold memcpy_large_written. intros; lia. Qed.
Print Assumptions memcpy_large_tail_cover.
Lemma memcpy_large_source_unchanged:
  forall m M d s n q o L a,
  128<n -> q+64<=n -> nov d s n ->
  cpy m M d s (memcpy_large_written q) -> o+L<=n ->
  a mod 2^64 = (s+o) mod 2^64 ->
  getmem 64 LittleE L M a = getmem 64 LittleE L m a.
Proof.
  intros m M d s n q o L a NN Q NOV CP OL A.
  eapply (cpy_load m M d s (memcpy_large_written q) n o L a);
    try eassumption.
  intros i I. eapply memcpy_large_written_bound; eassumption.
Qed.
Print Assumptions memcpy_large_source_unchanged.

(* A value form of cpy_store separates load preservation from store framing. *)
Lemma memcpy_large_store_value:
  forall m M d s (W:N->Prop) o L a v,
  cpy m M d s W -> (forall i, W i -> i<2^64) ->
  0<L -> o+L<=2^64 -> a mod 2^64 = (d+o) mod 2^64 ->
  v = getmem 64 LittleE L m (s ⊕ o) ->
  cpy m (setmem 64 LittleE L M a v) d s
    (fun i => W i \/ o<=i<o+L).
Proof.
  intros m M d s W o L a v CP WB L0 OL A V. rewrite V.
  apply cpy_store; try assumption. apply N.mod_mod. discriminate.
Qed.
Print Assumptions memcpy_large_store_value.

Strategy 1000 [N.pow getmem setmem N.modulo N.land N.lor N.lxor
  N.shiftl N.shiftr].
Local Opaque getmem setmem.
Ltac ignore_vars v ::= constr:(match v with
  | R_TMPCY | R_TMPOV | R_TMPNG | R_TMPZR | R_NG | R_OV => true
  | _ => false end).

Ltac large_frame FRAME :=
  unfold memcpy_large_frame; intros v V;
  unfold memcpy_large_saved in V;
  repeat destruct V as [<-|V]; try contradiction;
  rewrite ?update_frame by discriminate;
  apply FRAME; unfold memcpy_large_saved; simpl; tauto.

(* Arithmetic is deliberately supplied a whitelist; memory is never sent to
   lia. QB packages all local scalar bounds, including branch inequalities. *)
Ltac large_arith SIZE DN SN QB :=
  try (revert I); clear - SIZE DN SN QB; intros;
  unfold msub, memcpy_large_written in *;
  change (2^64) with 18446744073709551616 in *;
  change (2^63) with 9223372036854775808 in *; lia.

(* Try only actual candidate offsets. Successful selection is certified by
   modular equality, not by an assumed output value. *)
Ltac large_offset offsets a base arith k :=
  lazymatch offsets with
  | ?o :: ?rest => first
    [ let EQ := fresh "OFFSET" in
      assert (EQ: a mod 2^64 = (base+o) mod 2^64) by arith; k o EQ
    | large_offset rest a base arith k ]
  | [] => fail "No certified large-copy offset"
  end.

Ltac large_chain m d s n M0 CP NOV offsets arith :=
  lazymatch goal with
  | |- cpy _ ?M _ _ _ => first
    [ constr_eq M M0; exact CP
    | constr_eq M m; apply cpy_empty
    | lazymatch M with
      | setmem 64 LittleE ?L ?M1 ?a ?v =>
        large_offset offsets a d arith ltac:(fun o EQ =>
          eapply (memcpy_large_store_value m M1 d s _ o L a v);
          [ large_chain m d s n M0 CP NOV offsets arith
          | intros i I; unfold memcpy_large_written in I; arith
          | arith | arith | exact EQ
          | lazymatch v with
            | getmem 64 LittleE L ?ML ?sa =>
              large_offset offsets sa s arith ltac:(fun so SEQ =>
                let LOAD := fresh "LOAD" in
                assert (LOAD: getmem 64 LittleE L ML sa =
                              getmem 64 LittleE L m sa) by
                  (eapply (cpy_load m ML d s _ n so L sa);
                   [large_chain m d s n M0 CP NOV offsets arith
                   |intros i I; unfold memcpy_large_written in I; arith
                   |exact NOV|arith|exact SEQ]);
                rewrite LOAD;
                rewrite <- (getmem_mod_l 64 LittleE L m sa),
                        <- (getmem_mod_l 64 LittleE L m (s ⊕ o));
                f_equal; arith)
            end ])
      end ]
  end.

(* The entry prefix contains no loads or stores. *)
Lemma memcpy_large_entry_step:
  forall st m d s n t s1,
  models arm8typctx s1 -> memcpy_large_domain st d s n ->
  memcpy_large_input st m d s n s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_large_invs st m d s n)
    memcpy_large_exit false ((Addr 0x19ab40,s1)::t).
Proof.
  intros st m d s n t s1 MDL1 [NN [DN [SN [NOV [READ WRITE]]]]]
    [MEM [DEST [SRC [COUNT FRAME]]]].
  pose proof (memcpy_large_size_bound d s n ltac:(lia) DN SN NOV) as SIZE.
  assert (CY: (128 <=? n) = true) by (apply N.leb_le; lia).
  assert (ZR: (msub 64 n 128 =? 0) = false).
  { apply N.eqb_neq. clear - NN SIZE. unfold msub.
    change (2^64) with 18446744073709551616 in *.
    change (2^63) with 9223372036854775808 in *; lia. }
  repeat arm8_step;
    rewrite ?CY, ?ZR in *;
    try (match goal with H: false = true |- _ => discriminate H
                       | H: true = false |- _ => discriminate H end).
  unfold memcpy_large_head, memcpy_large_input.
  repeat split; try assumption; try reflexivity; try (large_frame FRAME).
Qed.
Print Assumptions memcpy_large_entry_step.

(* Head and loop preserve a small abstract memory fact at each cut. The
   candidates include q+64..q+120 for newly prefetched loop data. *)
Lemma memcpy_large_head_step:
  forall st m d s n t s1,
  models arm8typctx s1 -> memcpy_large_domain st d s n ->
  memcpy_large_head st m d s n s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_large_invs st m d s n)
    memcpy_large_exit false ((Addr 0x19ac40,s1)::t).
Proof.
  intros st m d s n t s1 MDL1 [NN [DN [SN [NOV [READ WRITE]]]]]
    [[MEM [DEST [SRC [COUNT FRAME]]]] [SEND DEND]].
  pose proof (memcpy_large_size_bound d s n ltac:(lia) DN SN NOV) as SIZE.
  set (q := 16-d mod 16).
  assert (QB: 0<q /\ q<=16 /\ q+64<=n /\ q=16-d mod 16).
  { subst q. pose proof (N.mod_lt d 16 ltac:(discriminate)). lia. }
  pose proof (cpy_empty m d s) as CP.
  repeat arm8_step;
    unfold memcpy_large_loop, memcpy_large_tail;
    exists q; unfold memcpy_large_buffer; repeat split;
    try (large_frame FRAME);
    try (large_arith SIZE DN SN QB);
    try reflexivity.
  all: rewrite ?MEM, ?getmem_mod_l, ?getmem_mod_r,
               ?setmem_mod_l, ?setmem_mod_r.
  all: try (eapply cpy_equiv; [|large_chain m d s n m CP NOV
       [0;8;q;q+8;q+16;q+24;q+32;q+40;q+48;q+56]
       ltac:(large_arith SIZE DN SN QB)];
       intro i; unfold memcpy_large_written; lia).
  all: try (eapply (cpy_load m _ d s _ n);
    [large_chain m d s n m CP NOV
       [0;8;q;q+8;q+16;q+24;q+32;q+40;q+48;q+56]
       ltac:(large_arith SIZE DN SN QB)
    |intros i I; unfold memcpy_large_written in I; lia
    |exact NOV|large_arith SIZE DN SN QB|large_arith SIZE DN SN QB]).
Qed.
Print Assumptions memcpy_large_head_step.

Lemma memcpy_large_loop_step:
  forall st m d s n t s1,
  models arm8typctx s1 -> memcpy_large_domain st d s n ->
  memcpy_large_loop st m d s n s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_large_invs st m d s n)
    memcpy_large_exit false ((Addr 0x19ac70,s1)::t).
Proof.
  intros st m d s n t s1 MDL1 [NN [DN [SN [NOV [READ WRITE]]]]]
    [q [BUF [MORE COUNT]]].
  destruct BUF as [Q0 [QN [DEST [DC [SC [SEND [DEND
    [A0 [A1 [A2 [A3 [A4 [A5 [A6 [A7 [CP FRAME]]]]]]]]]]]]]]]].
  pose proof (memcpy_large_size_bound d s n ltac:(lia) DN SN NOV) as SIZE.
  assert (QB: 0<q /\ q+128<n) by lia.
  repeat arm8_step;
    unfold memcpy_large_loop, memcpy_large_tail;
    exists (q+64); unfold memcpy_large_buffer; repeat split;
    try (large_frame FRAME);
    try (large_arith SIZE DN SN QB); try reflexivity.
  all: rewrite ?getmem_mod_l, ?getmem_mod_r, ?setmem_mod_l, ?setmem_mod_r.
  all: try (eapply cpy_equiv; [|large_chain m d s n (s1 V_MEM64) CP NOV
    [q;q+8;q+16;q+24;q+32;q+40;q+48;q+56;
     q+64;q+72;q+80;q+88;q+96;q+104;q+112;q+120]
    ltac:(large_arith SIZE DN SN QB)];
    intro i; unfold memcpy_large_written; lia).
  all: try (eapply (cpy_load m _ d s _ n);
    [large_chain m d s n (s1 V_MEM64) CP NOV
      [q;q+8;q+16;q+24;q+32;q+40;q+48;q+56;
       q+64;q+72;q+80;q+88;q+96;q+104;q+112;q+120]
      ltac:(large_arith SIZE DN SN QB)
    |intros i I; unfold memcpy_large_written in I; lia
    |exact NOV|large_arith SIZE DN SN QB|large_arith SIZE DN SN QB]).
Qed.
Print Assumptions memcpy_large_loop_step.

Lemma memcpy_large_tail_step:
  forall st m d s n t s1,
  models arm8typctx s1 -> memcpy_large_domain st d s n ->
  memcpy_large_tail st m d s n s1 ->
  nextinv e08___memcpy_generic_arm8 (memcpy_large_invs st m d s n)
    memcpy_large_exit false ((Addr 0x19ac98,s1)::t).
Proof.
  intros st m d s n t s1 MDL1 [NN [DN [SN [NOV [READ WRITE]]]]]
    [q [BUF LAST]].
  destruct BUF as [Q0 [QN [DEST [DC [SC [SEND [DEND
    [A0 [A1 [A2 [A3 [A4 [A5 [A6 [A7 [CP FRAME]]]]]]]]]]]]]]]].
  pose proof (memcpy_large_size_bound d s n ltac:(lia) DN SN NOV) as SIZE.
  assert (QB: 128<n /\ 0<q /\ q+64<=n /\ n<=q+128) by lia.
  repeat arm8_step. unfold memcpy_large_post.
  split; [reflexivity|]. split; [|large_frame FRAME].
  rewrite ?getmem_mod_l, ?getmem_mod_r, ?setmem_mod_l, ?setmem_mod_r.
  eapply cpy_copied; cycle 1.
  - large_chain m d s n (s1 V_MEM64) CP NOV
      [q;q+8;q+16;q+24;q+32;q+40;q+48;q+56;
       n-64;n-56;n-48;n-40;n-32;n-24;n-16;n-8]
      ltac:(large_arith SIZE DN SN QB).
  - intro i. unfold memcpy_large_written. clear - QB. lia.
Qed.
Print Assumptions memcpy_large_tail_step.

Theorem memcpy_large_correct:
  forall st t st' x' m d s n
    (ENTRY: startof t (x',st') = (Addr 0x19ab40,st))
    (MDL: models arm8typctx st)
    (MEM: st V_MEM64 = m) (DEST: st R_X0 = d)
    (SRC: st R_X1 = s) (COUNT: st R_X2 = n)
    (DOMAIN: memcpy_large_domain st d s n),
  satisfies_all e08___memcpy_generic_arm8
    (memcpy_large_invs st m d s n) memcpy_large_exit ((x',st')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. arm8_step.
    unfold memcpy_large_input. repeat split; try assumption.
  - intros. erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption.
    apply memcpy_large_welltyped. intro MDL1.
    clear - PRE MDL1 DOMAIN. destruct_inv 64 PRE.
    + eapply memcpy_large_entry_step; eassumption.
    + eapply memcpy_large_head_step; eassumption.
    + eapply memcpy_large_loop_step; eassumption.
    + eapply memcpy_large_tail_step; eassumption.
Qed.
Print Assumptions memcpy_large_correct.

Theorem memcpy_large_returns_original_bytes:
  forall st t st' m d s n,
  startof t (Addr 0x19acc8,st') = (Addr 0x19ab40,st) ->
  models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
  st R_X1 = s -> st R_X2 = n -> memcpy_large_domain st d s n ->
  exec_prog e08___memcpy_generic_arm8 ((Addr 0x19acc8,st')::t) ->
  unterminated memcpy_large_exit t -> memcpy_large_post st m d s n st'.
Proof.
  intros st t st' m d s n ENTRY MDL MEM D S NN DOMAIN XP UT.
  pose proof (memcpy_large_correct st t st' (Addr 0x19acc8) m d s n
    ENTRY MDL MEM D S NN DOMAIN) as SA.
  pose proof (satall_trueif_inv _ _ _ _ SA XP UT) as POST.
  exact POST.
Qed.
Print Assumptions memcpy_large_returns_original_bytes.
Theorem memcpy_large_preserves_callee_saved:
  forall st t st' m d s n,
  startof t (Addr 0x19acc8,st') = (Addr 0x19ab40,st) ->
  models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
  st R_X1 = s -> st R_X2 = n -> memcpy_large_domain st d s n ->
  exec_prog e08___memcpy_generic_arm8 ((Addr 0x19acc8,st')::t) ->
  unterminated memcpy_large_exit t -> memcpy_large_frame st st'.
Proof.
  intros st t st' m d s n ENTRY MDL MEM D S NN DOMAIN XP UT.
  exact (proj2 (proj2 (memcpy_large_returns_original_bytes
    st t st' m d s n ENTRY MDL MEM D S NN DOMAIN XP UT))).
Qed.
Print Assumptions memcpy_large_preserves_callee_saved.
