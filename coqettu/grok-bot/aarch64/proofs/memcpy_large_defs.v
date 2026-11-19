(* memcpy, n > 128 (aligned 64-byte loop) -- definitions.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memcpy_armv8.
From Grok.proofs Require Import memcpy_defs.
From Grok.lib Require Import GrokCov.
Import ARM8Notations.
Open Scope N.

Definition mcl_pre (mem d src n sp raddr : N) (s:store) :=
  s R_X0 = d /\ s R_X1 = src /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
  128 < n /\ d + n < 2^64 /\ src + n < 2^64 /\ (src + n <= d \/ d + n <= src).

(* common part: L bytes of dest done; x6..x13 hold the next 64 source bytes *)
Definition mcl_regs (mem d src n sp raddr L : N) (s:store) :=
  s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X4 = src + n /\ s R_X5 = d + n /\
  16 <= d + L /\ s R_X3 = d + L - 16 /\ 0 < L /\
  d + n < 2^64 /\ src + n < 2^64 /\ (src + n <= d \/ d + n <= src) /\
  s R_X6 = mem Ⓠ[src + L] /\ s R_X7 = mem Ⓠ[src + L + 8] /\
  s R_X8 = mem Ⓠ[src + L + 16] /\ s R_X9 = mem Ⓠ[src + L + 24] /\
  s R_X10 = mem Ⓠ[src + L + 32] /\ s R_X11 = mem Ⓠ[src + L + 40] /\
  s R_X12 = mem Ⓠ[src + L + 48] /\ s R_X13 = mem Ⓠ[src + L + 56] /\
  cov mem (s V_MEM64) src d n (fun i => i < L).

Section Invariants.
  Variables (mem d src n sp raddr : N).
  Definition mcl_inv_fn T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118270 => Inv 0 (mcl_pre mem d src n sp raddr s)
    | 0x1183a0 => Inv 0 (∃ L, mcl_regs mem d src n sp raddr L s /\ L + 128 < n /\
                              s R_X1 = src + L + 48 /\ s R_X2 = n - L - 128)
    | 0x1183c8 => Inv 0 (∃ L, mcl_regs mem d src n sp raddr L s /\ L + 64 < n /\ n <= L + 128)
    | 0x1182a0 | 0x1182b8 | 0x1182d4 | 0x1182f8 | 0x118328 | 0x118368 | 0x1183f8 =>
        Post 0 (memcpy_post mem d src n sp raddr s)
    | _ => NoInv
    end.
  Definition mcl_exits := make_exits 0 memcpy_armv8 mcl_inv_fn.
  Definition mcl_invs := make_invs 0 memcpy_armv8 mcl_inv_fn.
End Invariants.
