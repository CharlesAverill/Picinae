(* AVX memmove: backward overlap and self-alias, n > 256.

   Provenance inherited, NOT independently validated here:
   /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9,
   __memmove_avx_unaligned_erms, Ghidra 0x2a0840/imagebase 0x100000,
   normalized entry 0; Ghidra 11.4.2 + pcode2coq amd64-fixes.
   Generated memmove_avx_amd64.v is unchanged.

   Author: OpenAI gpt-6-astra, xhigh/priority, initial one-shot attempt.
   Status: PARTIAL. First full build failed at bw_gap_examples.
   Only bw_suffix_unread and bw_domain_all_gaps reached Qed in that run.
   Remaining declarations are Abort, not exported facts. Exact initial
   proofs are in notes/x04-avx-overlap-backward/initial-attempt.v.txt.
   Final proof producer: none; requires a new Sol fixer.
   Alignment arithmetic and symbolic-execution structure adapted from
   Claude Opus 5.5's baseline amd64_memmove_avx_loops_proof.v.

   English specification: copy n original source bytes to destination,
   allowing s < d < s+n, and return d. Every byte outside destination is
   unchanged. System V input RDI=d, RSI=s, RDX=n, RSP=rsp; output at RET
   RAX=d, RSP=rsp. RBX,RBP,R12-R15 have a separate real execution frame.
   The additional self-alias theorem follows the early exit to RET 493
   and asserts unchanged whole memory, rather than just copied m m.

   Bounds: n>256, d+n<=2^64, s+n<=2^64, 128<=d for backward overlap.
   The source bound follows from s<d but is explicit. No NOV, no minimum
   gap, no arbitrary upper size limit, no CPU/tunable/DF hypothesis.
   Both 309 and 704 dispatch on d-s<n to 496 before reading NT/REP policy.
   Thus sizes above the REP threshold are included. The initial threshold
   at 0x31a3f8 may contain any value. ISA availability and physical mapped
   memory are outside the sequential IL model.
   The absolute 128<=d bound prevents cursor c-128 wrapping before the
   unsigned comparison at 590. It does NOT require d-s>=128.

   Unread source is derived from the suffix frame, not globally frozen:
   previously written destination offsets are >=k, and s<=d implies
   source[0,k) is disjoint from those writes. All four loads in an iteration
   precede all four stores. YMM0,5,6,7 save original head[0,128), YMM8 the
   original last 32 bytes. The final stores use those saved values.

   Sequential IL partial correctness only: no termination, executed RET,
   caller continuation, hardware faults, cache/timing/concurrency, or
   binary/lifter soundness claim. Existing functional extensionality must
   be reported by Print Assumptions; no assumed kernel/callee contracts.
 *)

Require Import Picinae_amd64 memmove_avx_amd64.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
From Stdlib Require Import NArith ZArith Lia List.
Import X64Notations ListNotations.
Open Scope N.

Definition bw_domain d s n :=
  256 < n /\ s < d < s+n /\ 128 <= d /\
  d+n <= 2^64 /\ s+n <= 2^64.

Definition bw_unread (m M:memory) s k :=
  forall o L a, o+L<=k -> a mod 2^64 = (s+o) mod 2^64 ->
    getmem 64 LittleE L M a = getmem 64 LittleE L m a.

(* Suffix frame implies preservation of every still-unread source load. *)
Lemma bw_suffix_unread:
  forall m M d s n k (W:N->Prop),
  cpy m M d s W -> (forall i, W i -> k <= i < n) ->
  s <= d -> d+n <= 2^64 -> k <= n -> bw_unread m M s k.
Proof.
  intros m M d s n k W [C F] WK SD NW KN o L a OL A.
  apply getmem_frame_mem. intros b B.
  rewrite <- !(getmem_1 64 LittleE).
  apply F. intro Wb.
  pose proof (WK _ Wb) as J.
  assert (I: o + msub 64 b a < k) by (clear - B OL; lia).
  assert (DB: d + msub 64 b d < 2^64) by (clear - J NW; lia).
  assert (SB: s + (o + msub 64 b a) < 2^64) by
    (clear - I SD NW KN; lia).
  assert (E: (d + msub 64 b d) mod 2^64 =
             (s + (o + msub 64 b a)) mod 2^64).
  { rewrite (addmsub b d).
    rewrite N.add_assoc, <- N.add_mod_idemp_l, <- A,
            N.add_mod_idemp_l by discriminate.
    rewrite !addmsub. reflexivity. }
  rewrite (N.mod_small _ _ DB), (N.mod_small _ _ SB) in E.
  clear - E J I SD. lia.
Qed.

(* Every gap in 1..n-1 is represented, including 1,31,32,127. *)
Lemma bw_domain_all_gaps:
  forall n gap, 256<n -> 0<gap<n -> 4096+gap+n<=2^64 ->
    bw_domain (4096+gap) 4096 n.
Proof. intros n gap BIG GAP NW. unfold bw_domain. lia. Qed.

Lemma bw_gap_examples:
  bw_domain 4097 4096 257 /\ bw_domain 4127 4096 257 /\
  bw_domain 4128 4096 257 /\ bw_domain 4223 4096 257.
Abort.

Definition bw_witness_store (gap:N) : store := fun v => match v with
  | R_RDI => 4096+gap | R_RSI => 4096 | R_RDX => 257
  | R_RSP => 8192 | _ => 0 end.

Lemma bw_typed_entry_witness:
  forall gap, 0<gap<257 -> exists st,
  models x64typctx st /\ st V_MEM64=0 /\ st R_RDI=4096+gap /\
  st R_RSI=4096 /\ st R_RDX=257 /\ st R_RSP=8192 /\
  bw_domain (4096+gap) 4096 257.
Abort.

Lemma bw_initial_memory_satisfiable:
  forall m d s n, cpy m m d s (fun _ => False) /\ bw_unread m m s n.
Abort.

Theorem memmove_avx_overlap_backward_nwc:
  forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Abort.

Theorem memmove_avx_overlap_backward_welltyped:
  welltyped_prog x64typctx memmove_avx_amd64.
Abort.

Theorem memmove_avx_overlap_backward_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => st v = st' v).
Abort.

Definition c0 (d n:N) := (d+n-129) - (d+n-129) mod 32.

Lemma land_align32: forall x, x < 2^64 -> x .& 18446744073709551584 = x - x mod 32.
Abort.


Lemma c0_bounds: forall d n, 160 <= d + n -> d + n - 160 <= c0 d n <= d + n - 129.
Abort.

(* RCX on entry to the backward loop: (d + n - 129) rounded down to 32. *)
Lemma rcx_c0: forall d n, 128 <= d -> 256 < n -> d + n <= 2^64 ->
  (d ⊖ 129 + n) .& 18446744073709551584 = c0 d n.
Abort.

Lemma rsi_c: forall s d c, d <= c -> d < 2^64 -> s ⊖ d ⊕ c = s ⊕ (c - d).
Abort.

(* Equal addresses mod 2^64 give equal loads. *)
Lemma getmem_addr: forall w e len (m:memory) a b, a mod 2^w = b mod 2^w -> getmem w e len m a = getmem w e len m b.
Abort.

Ltac bc_norm :=
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: (_ <=? _) = true |- _ => apply N.leb_le in H
  | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
  end;
  repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                       | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
  repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                       | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.

(* lia on just the arithmetic: drop memory, store and copy facts first. *)
Ltac alia :=
  repeat match goal with H: ?T |- _ =>
    lazymatch T with
    | context [setmem] => clear H
    | context [MemAcc] => clear H
    | cpy _ _ _ _ _ => clear H
    | nov _ _ _ => clear H
    | models _ _ => clear H
    | _ = _ :> store => clear H
    | context [V_MEM64] => clear H
    | context [getmem _ _ 32 _ _] => clear H
    end
  end; change (2^64) with 18446744073709551616 in *; lia.

(* Refute a path from one branch condition plus the size/threshold facts.
   lia must never see a getmem term: its preprocessing unfolds the load and
   runs out of memory. *)
Ltac refute B :=
  exfalso;
  match goal with H: ?T |- _ =>
    lazymatch T with context [getmem] => fail | context [V_MEM64] => fail | _ => idtac end;
    lazymatch T with _ < _ => idtac | _ <= _ => idtac | _ = _ :> N => idtac | _ <> _ => idtac end;
    clear - H B; lia
  end.

(* Keep only order/equality facts between numbers, then lia. *)
Ltac nlia :=
  repeat match goal with H: ?T |- _ =>
    lazymatch type of T with
    | Prop =>
        lazymatch T with
        | context [getmem] => clear H | context [V_MEM64] => clear H
        | _ < _ => fail | _ <= _ => fail | _ <> _ :> N => fail
        | _ = _ :> N => fail
        | _ => clear H
        end
    | _ => fail
    end
  end; lia.

Ltac step_prune := x64_step; try (bc_norm; first [discriminate | exfalso; alia]).

(* The JA (CF=0 and ZF=0) branch condition as lifted. *)
Lemma ja_not_taken: forall a b:bool,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = 0 -> a = true \/ b = true.
Abort.

Lemma ja_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = N.pos p -> a = false /\ b = false.
Abort.

Lemma msub_add_mod: forall a b c, b <= a -> a < 2^64 -> (msub 64 a b + c) mod 2^64 = (c + (a - b)) mod 2^64.
Abort.

Lemma bwd_rsi: forall s x, 128 <= x -> s ⊖ 128 ⊕ x = s ⊕ (x - 128).
Abort.

(* An arithmetic side condition, in a context already cleared down to the
   arithmetic facts. *)
Ltac aside :=
  lazymatch goal with
  | |- 0 < 32 => reflexivity
  | |- forall i, _ -> _ =>
      let i := fresh "i" in let Hi := fresh "Hi" in
      intros i Hi; cbv beta in Hi; repeat destruct Hi as [Hi|Hi];
      change (2^64) with 18446744073709551616 in *; lia
  | |- (?x mod 2^64) mod 2^64 = ?x mod 2^64 => apply N.mod_mod; discriminate
  | |- (msub 64 _ _ + _) mod 2^64 = _ mod 2^64 =>
      rewrite msub_add_mod by (change (2^64) with 18446744073709551616 in *; lia);
      f_equal; change (2^64) with 18446744073709551616 in *; lia
  | |- _ mod 2^64 = _ mod 2^64 => f_equal; change (2^64) with 18446744073709551616 in *; lia
  | |- _ => change (2^64) with 18446744073709551616 in *; lia
  end.

Lemma bw_store4:
  forall m M d s n k (W:N->Prop) o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4,
  cpy m M d s W -> (forall i, W i -> k <= i < n) -> s <= d -> d+n <= 2^64 -> k <= n -> n < 2^64 ->
  o1 + 32 <= k -> o2 + 32 <= k -> o3 + 32 <= k -> o4 + 32 <= k ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 ->
  a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 ->
  b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (M Ⓨ[b1])) a2 (M Ⓨ[b2])) a3 (M Ⓨ[b3])) a4 (M Ⓨ[b4])) d s
      (fun i => W i \/ o1 <= i < o1 + 32 \/ o2 <= i < o2 + 32 \/ o3 <= i < o3 + 32 \/ o4 <= i < o4 + 32).
Abort.


Definition bw_postcondition (m d s n rsp:N) (st:store) :=
  st R_RAX=d /\ st R_RSP=rsp /\ copied m (st V_MEM64) d s n.

Definition bw_exit (t:trace) :=
  match t with (Addr 623,_)::_ => true | _ => false end.

Definition bw_dispatch (m d s n rsp:N) (st:store) :=
  st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\
  st R_RSP=rsp /\ st R_RAX=d /\ st R_YMM0=m Ⓨ[s].

Definition bw_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\
               st R_RDX=n /\ st R_RSP=rsp)
  | 309 | 704 => Some (bw_dispatch m d s n rsp st)
  | 496 => Some (bw_dispatch m d s n rsp st /\ st R_RCX=d-s)
  | 544 => Some (exists c, d < c /\ c+128<=d+n /\ c<=c0 d n /\
      cpy m (st V_MEM64) d s (fun i => c-d+128<=i<c0 d n-d+128) /\
      st R_RCX=c /\ st R_RSI=s ⊕ (c-d) /\ st R_RDI=d /\ st R_RDX=n /\
      st R_RAX=d /\ st R_RSP=rsp /\
      st R_YMM0=m Ⓨ[s] /\ st R_YMM5=m Ⓨ[s ⊕ 32] /\
      st R_YMM6=m Ⓨ[s ⊕ 64] /\ st R_YMM7=m Ⓨ[s ⊕ 96] /\
      st R_YMM8=m Ⓨ[s ⊕ (n-32)])
  | 623 => Some (bw_postcondition m d s n rsp st)
  | 27 | 48 | 214 | 324 | 490 | 719 => Some False
  | _ => None end | _ => None end.

(* The loop's suffix memory invariant entails the actual unread prefix. *)
Lemma bw_loop_unread:
  forall m M d s n c,
  bw_domain d s n -> d<c -> c+128<=d+n -> c<=c0 d n ->
  cpy m M d s (fun i => c-d+128<=i<c0 d n-d+128) ->
  bw_unread m M s (c-d+128).
Abort.

Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true | _ => false end).

Ltac bw_dispatch_proof GAP :=
  destruct PRE as [MEM [D [S [Nn [RSP [RAX Y0]]]]]];
  repeat x64_step;
  rewrite GAP in *;
  try (match goal with |- False => idtac end; bc_norm; exfalso; nlia);
  repeat split; reflexivity || assumption.

Theorem memmove_avx_correct_overlap_backward:
  forall st t st' x' m d s n rsp
    (ENTRY: startof t (x',st') = (Addr 0,st))
    (MDL: models x64typctx st)
    (MEM: st V_MEM64=m) (D: st R_RDI=d) (S: st R_RSI=s)
    (Nn: st R_RDX=n) (RSP: st R_RSP=rsp)
    (DOM: bw_domain d s n),
  satisfies_all memmove_avx_amd64 (bw_invs m d s n rsp) bw_exit ((x',st')::t).
Abort.

(* Self-alias has its own exit, with no loop invariant and no memory stores. *)
Definition bw_self_exit (t:trace) :=
  match t with (Addr 493,_)::_ => true | _ => false end.
Definition bw_self_post (m d rsp:N) (st:store) :=
  st V_MEM64=m /\ st R_RAX=d /\ st R_RSP=rsp.
Definition bw_self_invs (m d n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=d /\
               st R_RDX=n /\ st R_RSP=rsp)
  | 309 | 704 => Some (bw_dispatch m d d n rsp st)
  | 496 => Some (bw_dispatch m d d n rsp st /\ st R_RCX=0)
  | 493 => Some (bw_self_post m d rsp st)
  | 27 | 48 | 214 | 324 | 501 | 719 => Some False
  | _ => None end | _ => None end.

Theorem memmove_avx_correct_self_alias:
  forall st t st' x' m d n rsp
    (ENTRY: startof t (x',st') = (Addr 0,st))
    (MDL: models x64typctx st)
    (MEM: st V_MEM64=m) (D: st R_RDI=d) (S: st R_RSI=d)
    (Nn: st R_RDX=n) (RSP: st R_RSP=rsp) (BIG: 256<n),
  satisfies_all memmove_avx_amd64 (bw_self_invs m d n rsp)
    bw_self_exit ((x',st')::t).
Abort.

(* Extract an explicit return-site spec from the main trace theorem. *)
Corollary memmove_avx_overlap_backward_at_ret:
  forall st t st' m d s n rsp,
  startof t (Addr 623,st')=(Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n ->
  st R_RSP=rsp -> bw_domain d s n ->
  exec_prog memmove_avx_amd64 ((Addr 623,st')::t) ->
  unterminated bw_exit t -> bw_postcondition m d s n rsp st'.
Abort.

Corollary memmove_avx_self_alias_at_ret:
  forall st t st' m d n rsp,
  startof t (Addr 493,st')=(Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=d -> st R_RDX=n ->
  st R_RSP=rsp -> 256<n ->
  exec_prog memmove_avx_amd64 ((Addr 493,st')::t) ->
  unterminated bw_self_exit t -> bw_self_post m d rsp st'.
Abort.
