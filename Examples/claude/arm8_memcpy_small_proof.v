(* PARTIAL Astra handoff: first full build failed; no repair cycle or rebuild.
   Unchecked declarations are aborted, not exported proof constants. *)
(* __memcpy_generic, AArch64, actual size partition 0 <= n <= 32.

   PROVENANCE (inherited, not a binary/lifter-refinement theorem):
   Ubuntu ARM64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Ghidra 11.4.2 explicit strict scalar replacement, e08 accepted artifacts.
   Model addresses = ELF addresses + 0x100000. Generic entry 0x19ab40
   (ELF 0x9ab40). The unchanged generated map contains 99 generic instructions
   plus nine mempcpy-wrapper instructions; this proof never enters the wrapper.
   Initial author: OpenAI gpt-6-astra, xhigh/priority, 2026-11-03.
   Final proof model is recorded only following a successful full .vo build.

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
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

Theorem memcpy_small_welltyped:
  welltyped_prog arm8typctx e08___memcpy_generic_arm8.
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

(* This witness is symbolic: the enormous permission mask must never be
   evaluated into a concrete integer. It is a finite N value in the model. *)
Definition memcpy_small_witness (m d s n:N) : store :=
  update (update (update (update (update (update (fun _ => 0)
    A_READ (N.ones (2^64))) A_WRITE (N.ones (2^64)))
    V_MEM64 m) R_X0 d) R_X1 s) R_X2 n.

Theorem memcpy_small_witness_typed:
  forall m d s n, m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> n < 2^64 ->
  models arm8typctx (memcpy_small_witness m d s n).
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

Theorem memcpy_small_entry_inhabited:
  forall m d s n,
  m < 2^(8*2^64) -> d < 2^64 -> s < 2^64 -> n <= 32 ->
  d+n <= 2^64 -> s+n <= 2^64 -> nov d s n ->
  exists st, models arm8typctx st /\ memcpy_small_domain st d s n /\
             memcpy_small_input st m d s n st.
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

Theorem memcpy_small_zero_entry:
  exists st, models arm8typctx st /\ memcpy_small_domain st 0 0 0 /\
             memcpy_small_input st 0 0 0 0 st.
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

(* Initial stepping/store-chain tactics are preserved in the initial-attempt archive. *)

Theorem memcpy_small_correct:
  forall st t st' x' m d s n
    (ENTRY: startof t (x',st') = (Addr 0x19ab40,st))
    (MDL: models arm8typctx st)
    (MEM: st V_MEM64 = m) (DEST: st R_X0 = d)
    (SRC: st R_X1 = s) (COUNT: st R_X2 = n)
    (DOMAIN: memcpy_small_domain st d s n),
  satisfies_all e08___memcpy_generic_arm8
    (memcpy_small_invs st m d s n) memcpy_small_exit ((x',st')::t).
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)

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
Abort. (* PARTIAL: exact initial attempt archived under notes/a-memcpy-small/. *)
