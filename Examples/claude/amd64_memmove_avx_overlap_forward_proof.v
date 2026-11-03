(* Forward overlapping __memmove_avx_unaligned_erms: ordinary 128-byte loop.
   Initial author: OpenAI gpt-6-astra, xhigh/priority. Final producer: pending.
   Source: /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
   Symbol Ghidra address 0x2a0840, image base 0x100000, normalized entry 0.
   Inherited Ghidra 11.4.2 + pcode2coq provenance, NOT newly validated here.
   The generated memmove_avx_amd64.v is unchanged.

   Specification: memmove(d,s,n) copies the ORIGINAL n source bytes, permits
   overlap, and returns d. System V AMD64 RDI=d, RSI=s, RDX=n, RSP=rsp.
   At RET address 493 (before executing RET), RAX=d and RSP=rsp; every byte
   outside the destination is unchanged. RBX/RBP/R12-R15 are preserved by a
   separate all-execution frame and included in the explicit RET corollary.

   Scope: 256<n<2^63, d<s<d+n, s+n<=2^64 (hence d+n<2^64), and n no larger
   than the entry-memory REP and NT thresholds at 0x31a3f8 and 0x3215a8.
   The size ceiling is the signed object-size range used to prove that the
   dispatch XOR changes sign; this is NOT an all-size/all-tunable theorem.
   All distances 1<=s-d<n are allowed, including 1,31,32,127. No lower bound
   on d is needed: forward pointer subtraction is modular and its final
   value is in bounds. The backward path's d>=128 restriction is not used.
   DF and ISA feature bits are not tested on this selected IL path.

   The invariant records copied offsets [a0,k), a frame outside that set,
   and head/tail YMM values loaded from ORIGINAL memory before any stores.
   Its frame implies that source offsets >=k remain unread and unchanged.
   Four loads happen before the four row stores, including at distance 1.
   Tail stores can overlap the last row; cpy_store handles that overwrite.

   Sequential IL partial correctness only: no termination, RET execution,
   caller continuation, hardware ISA/fault/cache/timing/concurrency claim,
   nor binary/lifter refinement. Baseline functional extensionality must be
   reported by the assumptions audit. Arithmetic/tactic scaffolding below
   is adapted from Claude Opus 5.5's baseline loop proof; no NOV-dependent
   cpy_load/cpy_store4w theorem is imported or used.
 *)
Require Import Picinae_amd64 memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Import ListNotations.
Open Scope N.

Definition ofw_path (m d s n:N) :=
  256 < n /\ n < 2^63 /\ d < s /\ s < d+n /\ s+n <= 2^64 /\
  n <= m Ⓠ[0x31a3f8] /\ n <= m Ⓠ[0x3215a8].

Definition ofw_postcondition (m d s n rsp:N) (st:store) :=
  st R_RAX = d /\ st R_RSP = rsp /\ copied m (st V_MEM64) d s n.
Definition ofw_frame (st st':store) :=
  forall v, In v [R_RBX;R_RBP;R_R12;R_R13;R_R14;R_R15] -> st' v = st v.
Definition a0 (d:N) := 32 - d mod 32.
Definition ofw_exit (t:trace) :=
  match t with (Addr 493,_)::_ => true | _ => false end.
Definition ofw_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\ st R_RSP=rsp)
  | 309 => Some (st V_MEM64=m /\ st R_RDI=d /\ st R_RSI=s /\ st R_RDX=n /\
                 st R_RSP=rsp /\ st R_RAX=d /\ st R_YMM0=m Ⓨ[s])
  | 416 => Some (exists k, a0 d <= k < n-128 /\
      cpy m (st V_MEM64) d s (fun i => a0 d <= i < k) /\
      st R_RDI=d+k /\ st R_RSI=s ⊕ k /\ st R_RDX=d+n-128 /\ st R_RCX=d /\
      st R_RAX=d /\ st R_RSP=rsp /\ st R_YMM0=m Ⓨ[s] /\
      st R_YMM5=m Ⓨ[s ⊕ (n-32)] /\ st R_YMM6=m Ⓨ[s ⊕ (n-64)] /\
      st R_YMM7=m Ⓨ[s ⊕ (n-96)] /\ st R_YMM8=m Ⓨ[s ⊕ (n-128)])
  | 493 => Some (ofw_postcondition m d s n rsp st)
  | 496 | 501 | 704 | 813 => Some False
  | _ => None end | _ => None end.

Theorem ofw_welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. exact memmove_avx_welltyped. Qed.
Theorem ofw_nwc: forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. reflexivity. Qed.
Theorem ofw_preserves_callee_saved:
  forall_endstates memmove_avx_amd64 (fun _ st _ st' => ofw_frame st st').
Proof.
  intros t x st x' st' XP ENTRY v IN. symmetry.
  exact (memmove_avx_preserves_callee_saved v IN t x st x' st' XP ENTRY).
Qed.

(* Copy-set frames give the ORIGINAL unread bytes without a NOV premise. *)
Lemma ofw_load:
  forall m M d s n k (W:N->Prop) o L a,
  cpy m M d s W -> (forall i, W i -> i < k) ->
  d < s -> s+n <= 2^64 -> k <= o -> o+L <= n ->
  a mod 2^64 = (s+o) mod 2^64 ->
  getmem 64 LittleE L M a = getmem 64 LittleE L m a.
Proof.
  intros m M d s n k W o L a [C F] WK DS SN KO OL A.
  apply getmem_frame_mem. intros b B. rewrite <- !(getmem_1 64 LittleE).
  apply F. intro WB. specialize (WK _ WB).
  assert (E: (d + msub 64 b d) mod 2^64 =
             (s + (o + msub 64 b a)) mod 2^64).
  { rewrite addmsub. rewrite N.add_assoc, <- N.add_mod_idemp_l,
      <- A, N.add_mod_idemp_l, addmsub by discriminate. reflexivity. }
  clear - E WK DS SN KO OL B.
  rewrite !N.mod_small in E by (change (2^64) with 18446744073709551616 in *; lia).
  lia.
Qed.

Lemma ofw_store4:
  forall m M d s n k (W:N->Prop) o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4,
  cpy m M d s W -> (forall i, W i -> i < k) -> d < s -> s+n <= 2^64 -> n < 2^64 ->
  k <= o1 -> k <= o2 -> k <= o3 -> k <= o4 ->
  o1 + 32 <= n -> o2 + 32 <= n -> o3 + 32 <= n -> o4 + 32 <= n ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 ->
  a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 ->
  b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (M Ⓨ[b1])) a2 (M Ⓨ[b2])) a3 (M Ⓨ[b3])) a4 (M Ⓨ[b4])) d s
      (fun i => W i \/ o1 <= i < o1 + 32 \/ o2 <= i < o2 + 32 \/ o3 <= i < o3 + 32 \/ o4 <= i < o4 + 32).
Proof.
  intros m M d s n k W o1 o2 o3 o4 a1 a2 a3 a4 b1 b2 b3 b4 C WN DS SN NB K1 K2 K3 K4 O1 O2 O3 O4 A1 A2 A3 A4 B1 B2 B3 B4.
  rewrite (ofw_load m M d s n k W o1 32 b1 C WN DS SN K1 O1 B1).
  rewrite (ofw_load m M d s n k W o2 32 b2 C WN DS SN K2 O2 B2).
  rewrite (ofw_load m M d s n k W o3 32 b3 C WN DS SN K3 O3 B3).
  rewrite (ofw_load m M d s n k W o4 32 b4 C WN DS SN K4 O4 B4).
  assert (C4: cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (getmem 64 LittleE 32 m b1)) a2 (getmem 64 LittleE 32 m b2)) a3 (getmem 64 LittleE 32 m b3))
          a4 (getmem 64 LittleE 32 m b4)) d s
      (fun i => (((W i \/ o1 <= i < o1 + 32) \/ o2 <= i < o2 + 32) \/ o3 <= i < o3 + 32) \/ o4 <= i < o4 + 32)).
  { apply cpy_store; [apply cpy_store; [apply cpy_store; [apply cpy_store; [exact C|..]|..]|..]|..].
    all: try assumption.
    all: try (intros i Hi; clear - Hi WN NB K1 O1 O2 O3 O4; change (2^64) with 18446744073709551616 in *;
              repeat destruct Hi as [Hi|Hi]; try apply WN in Hi; lia).
    all: try (clear; lia).
    all: clear - NB O1 O2 O3 O4; change (2^64) with 18446744073709551616 in *; lia. }
  eapply cpy_equiv; [|exact C4]. intro i. tauto.
Qed.

Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true | _ => false end).
Lemma lor31: forall d, d .| 31 = d - d mod 32 + 31.
Proof.
  intro d.
  assert (E: d - d mod 32 = d >> 5 << 5).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^5) with 32.
    rewrite (N.div_mod d 32) at 1 by discriminate. lia. }
  assert (B: d .| 31 = (d >> 5 << 5) .| 31).
  { apply N.bits_inj. intro i. rewrite !N.lor_spec. destruct (N.ltb_spec i 5).
    - assert (T: N.testbit 31 i = true) by
        (assert (Hc: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia;
         repeat destruct Hc as [E0|Hc]; subst; reflexivity).
      rewrite T, !Bool.orb_true_r. reflexivity.
    - rewrite N.shiftl_spec_high by lia. rewrite N.shiftr_spec by lia.
      replace (i - 5 + 5) with i by lia. reflexivity. }
  rewrite B, E. apply lor_plus.
  apply N.bits_inj. intro i. rewrite N.land_spec, N.bits_0. destruct (N.ltb_spec i 5).
  - rewrite N.shiftl_spec_low by lia. reflexivity.
  - replace (N.testbit 31 i) with false. apply Bool.andb_false_r.
    symmetry. apply N.bits_above_log2. change (N.log2 31) with 4. lia.
Qed.

Lemma a0_bounds: forall d, 1 <= a0 d <= 32.
Proof. intro d. unfold a0. pose proof (N.mod_lt d 32 ltac:(discriminate)). lia. Qed.

(* Equal addresses mod 2^64 give equal loads. *)
Lemma getmem_addr: forall w e len (m:memory) a b, a mod 2^w = b mod 2^w -> getmem w e len m a = getmem w e len m b.
Proof. intros. rewrite <- getmem_mod_l, H, getmem_mod_l. reflexivity. Qed.

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
Proof. intros [|] [|]; cbn; intro H; first [discriminate | tauto]. Qed.

Lemma ja_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0)) .^ 1 = N.pos p -> a = false /\ b = false.
Proof. intros [|] [|] p; cbn; intro H; first [discriminate | tauto]. Qed.

Lemma msub_add_mod: forall a b c, b <= a -> a < 2^64 -> (msub 64 a b + c) mod 2^64 = (c + (a - b)) mod 2^64.
Proof.
  intros a b c BA AB. assert (BB: b < 2^64) by lia.
  rewrite msub_nowrap by (rewrite (N.mod_small a), (N.mod_small b) by assumption; exact BA).
  rewrite (N.mod_small a), (N.mod_small b) by assumption. f_equal. lia.
Qed.

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

(* The wrapped d-s is large; adding n crosses zero and flips its sign. *)
Lemma ofw_dispatch:
  forall d s n, d < s -> s < d+n -> s+n <= 2^64 -> n < 2^63 ->
  n <= d ⊖ s /\ (((d ⊖ s ⊕ n) .^ (d ⊖ s)) >> 63) = 1.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

Lemma ofw_heuristic_nonzero:
  forall q, ((q .& 3840) + 1) mod 2^32 <> 0.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

Theorem memmove_avx_correct_overlap_forward:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (BIG: 256 < n) (DS: d < s) (OV: s < d+n) (SN: s+n <= 2^64) (NS: n < 2^63)
         (THR1: n <= m Ⓠ[0x31a3f8]) (THR2: n <= m Ⓠ[0x3215a8]),
  satisfies_all memmove_avx_amd64 (ofw_invs m d s n rsp) ofw_exit ((x',s')::t).
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

Theorem memmove_avx_overlap_forward_at_ret:
  forall st t st' m d s n rsp,
  startof t (Addr 493,st') = (Addr 0,st) -> models x64typctx st ->
  st V_MEM64=m -> st R_RDI=d -> st R_RSI=s -> st R_RDX=n -> st R_RSP=rsp ->
  ofw_path m d s n -> exec_prog memmove_avx_amd64 ((Addr 493,st')::t) ->
  unterminated ofw_exit t ->
  ofw_postcondition m d s n rsp st' /\ ofw_frame st st'.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

(* Nonvacuity: a typed entry for EVERY positive distance below 512, including
   1,31,32,127. This constructs entry memory/ABI values, not an execution or
   a termination witness. Thresholds are concrete writable global values. *)
Definition ofw_witness_memory :=
  setmem 64 LittleE 8 (setmem 64 LittleE 8 0 0x31a3f8 512) 0x3215a8 512.
Definition ofw_witness_store (gap:N) : store := fun v =>
  match v with
  | V_MEM64 => ofw_witness_memory
  | R_RDI => 4096 | R_RSI => 4096+gap | R_RDX => 512 | R_RSP => 8192
  | _ => 0 end.

Lemma ofw_witness_thresholds:
  ofw_witness_memory Ⓠ[0x31a3f8] = 512 /\
  ofw_witness_memory Ⓠ[0x3215a8] = 512.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

Theorem ofw_entry_satisfiable:
  forall gap, 0 < gap < 512 -> exists st m,
    models x64typctx st /\ ofw_path m 4096 (4096+gap) 512 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=512 /\ st R_RSP=8192.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)

Corollary ofw_critical_distances:
  forall gap, In gap [1;31;32;127] -> exists st m,
    models x64typctx st /\ ofw_path m 4096 (4096+gap) 512 /\
    st V_MEM64=m /\ st R_RDI=4096 /\ st R_RSI=4096+gap /\
    st R_RDX=512 /\ st R_RSP=8192.
Abort. (* PARTIAL: exact initial proof is in notes/x03-avx-overlap-forward/initial-attempt.v.txt. *)
