(* __memchr_nosimd -- least occurrence of low8(X1) in X2 bytes at X0.

   PROVENANCE, inherited and NOT a verified binary/lifter refinement:
   /lib/aarch64-linux-gnu/libc.so.6, Ubuntu glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF entry 0x9c7c0; model image base +0x100000, entry 0x19c7c0.
   Exactly 56 instructions / 224 bytes, byte SHA256
   f7cf0af3105e36c28d27de9445f45afabd68e952ece7dbeb9729a9fef8aa63fb.
   Accepted e30 prerequisite bbad5922112dedaa192bbe1fd0ab97f3bcbb2ba9;
   Ghidra 11.4.2 strict scalar pipeline. Generated map stays unchanged.
   Manifest and raw bytes: lifter/scalar_ccmp/e30___memchr_nosimd_arm8.*
   Initial statement/proof author: OpenAI gpt-6-astra, xhigh/default.
   Final proof producer: UNESTABLISHED until a full successful kernel build.

   ENGLISH SPEC / AAPCS64 (64-bit pointers, distinct from x86 ABI):
   Entry X0=a, X1=c, X2=n, typed architectural state. On actual RET transfer
   to the original X30, X0 is a+k for the LEAST k<n with original byte[a+k]
   = c mod256, or zero iff no such byte exists. Includes n=0, every starting
   alignment, arbitrary matching/nonmatching prefix and suffix padding, and
   both halves of each paired 64-bit load. Memory, SP, X19..X29, X30, modeled
   R_LR, Z8..Z15 and permission maps remain unchanged. No callee contracts.

   DOMAIN: n=0 needs no readable memory or non-null input. Otherwise a>0,
   n<2^63 and a+n+15<2^64; EVERY byte in [16*(a/16),16*((a+n+15)/16))
   is readable. This aligned envelope follows the real LDPs at 0x19c7ec
   and 0x19c830. It makes no assumption about padding values. The +15
   nonwrap bound follows ADD X8,X7,#15. The signed size bound follows the
   CMP/MI tests, including the first unaligned block's CMP X0,X7. Positive
   a is required for NULL iff no match; zero length permits a=0. There is
   no fixed input alignment, SP alignment, return-address exclusion, buffer
   disjointness, CPU extension or tunable hypothesis. Code/data may overlap
   in this separate immutable IL-code model. The proof concerns this scalar
   selected body only, not generic/SIMD memchr or the IFUNC resolver.

   satisfies_all establishes partial correctness, not termination or a
   concrete CPU fault/timing/speculation/ABI-vector refinement theorem.
   mc_exit recognizes the state AFTER one of the two RET instructions, so
   the intended result includes the actual X30 transfer, even when X30
   numerically aliases an instruction of the function.
*)
Require Import Picinae_armv8 e30___memchr_nosimd_arm8 arm8_memchr_nosimd_spec.
From Stdlib Require Import NArith Lia List.
Import ARM8Notations ListNotations.
Open Scope N.

Definition mc_ones : N := 0x0101010101010101.
Definition mc_detector (w:N) :=
  (msub 64 w mc_ones) .& ((w .| 0x7f7f7f7f7f7f7f7f) .^ 0xffffffffffffffff).
Definition mc_lane (w j:N) := (w >> (8*j)) mod 256.
Definition mc_word_first (w j:N) :=
  j < 8 /\ mc_lane w j = 0 /\ forall i, i < j -> mc_lane w i <> 0.
Definition mc_mask_first (w j:N) :=
  j < 8 /\ N.testbit w (8*j+7) = true /\
  forall i, i < j -> N.testbit w (8*i+7) = false.

(* All bytes before a are filled with FF AFTER XOR, preventing false hits.
   This definition describes data at the loop cut; it does not replace IL. *)
Definition mc_scan_word (m a c b:N) :=
  let w := (getmem 64 LittleE 8 m b) .^ ((c mod 256)*mc_ones) in
  if b <? a then
    if a-b <? 8 then w .| (2^(8*(a-b))-1) else 0xffffffffffffffff
  else w.
Definition mc_scanned (m a c n b:N) :=
  forall i, i < n -> a+i < b -> mc_byte m a i <> c mod 256.
Definition mc_constants (a c n:N) (s:store) :=
  s R_X1 = (c mod 256)*mc_ones /\ s R_X10 = mc_ones /\
  s R_X7 = a+n /\ s R_X8 = mc_hi a n.
Definition mc_loop (s0:store) (a c n:N) (s:store) :=
  0 < n /\ mc_frame s0 s /\ mc_constants a c n s /\
  exists b, s R_X6 = b /\ b mod 16 = 0 /\
    a <= b /\ mc_lo a <= b < mc_hi a n /\
    mc_scanned (s0 V_MEM64) a c n b.
Definition mc_block (s0:store) (a c n:N) (s:store) :=
  0 < n /\ mc_frame s0 s /\ mc_constants a c n s /\
  exists b, s R_X6 = b+16 /\ b mod 16 = 0 /\
    mc_lo a <= b /\ b+16 <= mc_hi a n /\
    mc_scanned (s0 V_MEM64) a c n b /\
    s R_X11 = mc_scan_word (s0 V_MEM64) a c b /\
    s R_X12 = mc_scan_word (s0 V_MEM64) a c (b+8) /\
    (s R_X9 = 0 <-> b+16 = mc_hi a n) /\
    s R_ZR = (if b+16 =? mc_hi a n then 1 else 0).
Definition mc_detected (s0:store) (a c n:N) (s:store) :=
  0 < n /\ mc_frame s0 s /\ mc_constants a c n s /\
  exists b, s R_X6 = b+16 /\ b mod 16 = 0 /\
    mc_lo a <= b /\ b+16 <= mc_hi a n /\
    mc_scanned (s0 V_MEM64) a c n b /\
    s R_X13 = mc_detector (mc_scan_word (s0 V_MEM64) a c b) /\
    s R_X14 = mc_detector (mc_scan_word (s0 V_MEM64) a c (b+8)) /\
    (s R_X9 = 0 <-> b+16 = mc_hi a n) /\
    (s R_X13 <> 0 \/ s R_X14 <> 0 \/ b+16 = mc_hi a n).
Definition mc_invs (s0:store) (a c n:N) (t:trace) :=
  if mc_exit t then
    match t with (x,s)::_ => Some (x = Addr (s0 R_X30) /\ mc_post s0 a c n s)
    | _ => None end
  else match t with (Addr pc,s)::_ => match pc with
  | 0x19c7c0 => Some (mc_input s0 a c n s)
  | 0x19c830 => Some (mc_loop s0 a c n s)
  | 0x19c840 => Some (mc_block s0 a c n s)
  | 0x19c864 => Some (mc_detected s0 a c n s)
  | 0x19c894 | 0x19c89c => Some (mc_post s0 a c n s)
  | _ => None end | _ => None end.

Ltac mc_interval x bound :=
  let rec go k :=
    lazymatch eval compute in (k <? bound) with
    | true => destruct (N.eq_dec x k) as [->|?];
        [idtac | let next := eval compute in (k+1) in go next]
    | false => exfalso; lia
    end in go 0.

(* Word-at-a-time subtraction may flag an 01 byte following a zero because
   of a borrow. Only FIRST flagged byte, not every flagged byte, is sound.
   This is the algebraic interface needed by REV+CLZ and by loop advance. *)
Lemma mc_detector_correct : forall w, w < 2^64 ->
  (mc_detector w = 0 <-> forall i, i < 8 -> mc_lane w i <> 0) /\
  (forall j, mc_word_first w j <-> mc_mask_first (mc_detector w) j).
(* PARTIAL: exact initial proof is preserved in notes/a-memchr-nosimd/. *)
Abort.

(* Entry, loop, detector and RET cuts form the one-shot initial attempt.
   Every generated instruction is still stepped from the accepted map. *)
Theorem memchr_nosimd_correct :
  forall s0 t s' x' a c n
    (ENTRY: startof t (x',s') = (Addr 0x19c7c0,s0))
    (MDL: models arm8typctx s0)
    (INPUT: mc_input s0 a c n s0)
    (DOMAIN: mc_domain s0 a n),
  satisfies_all e30___memchr_nosimd_arm8 (mc_invs s0 a c n)
    mc_exit ((x',s')::t).
(* PARTIAL: exact initial proof is preserved in notes/a-memchr-nosimd/. *)
Abort.
