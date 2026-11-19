(* memmove, overlapping / equal / empty case (no tail call to memcpy):
   precondition and invariants.  Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memmove_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memcpy_defs.
From Grok.proofs Require Import memmove_lib.
Import ARM8Notations.
Open Scope N.

Theorem memmove_welltyped: welltyped_prog arm8typctx memmove_armv8.
Proof. Picinae_typecheck. Qed.

Section Invariants.
  Variables (mem d src n sp raddr : N).
  Definition mv_base (s:store) :=
    s R_SP = sp /\ s R_X30 = raddr /\ s R_X5 = d /\ d + n < 2^64 /\ src + n < 2^64 /\ n < 2^62.
  Definition mva_pre (s:store) :=
    s R_X0 = d /\ s R_X1 = src /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
    d + n < 2^64 /\ src + n < 2^64 /\ n < 2^62 /\ (n = 0 \/ (d < src + n /\ src < d + n)).
  Definition mva_inv_fn T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e708 => Inv 0 (mva_pre s)
    | 0x15e750 => Inv 0 False
    | 0x15e7ac => Inv 0 (mv_base s /\ d < src /\ ∃ k0 j, s R_X1 = d + k0 /\ s R_X4 = src + k0 /\ s R_X0 = j /\
                         s R_X3 = n - k0 /\ k0 + j <= n /\ fwd mem (s V_MEM64) src d n (k0 + j))
    | 0x15e758 => Inv 0 (mv_base s /\ d < src /\ ∃ k, s R_X0 = d + k /\ s R_X4 = src + k /\ s R_X3 = n - k /\
                         k <= n /\ fwd mem (s V_MEM64) src d n k)
    | 0x15e788 => Inv 0 (mv_base s /\ d < src /\ ∃ k0 j, s R_X0 = d + k0 /\ s R_X4 = src + k0 /\ s R_X3 = n - k0 /\
                         s R_X2 = j /\ s R_X6 = (n - k0) - (n - k0) mod 8 /\ j mod 8 = 0 /\
                         k0 <= n /\ j <= (n - k0) - (n - k0) mod 8 /\ fwd mem (s V_MEM64) src d n (k0 + j))
    | 0x15e7c0 => Inv 0 (mv_base s /\ src < d /\ s R_X4 = src /\ ∃ k, s R_X3 = k /\ k <= n /\ bwd mem (s V_MEM64) src d n k)
    | 0x15e7f8 => Inv 0 (mv_base s /\ src < d /\ s R_X4 = src /\ ∃ k0 j, s R_X3 = k0 /\ s R_X0 = j /\ s R_X2 = k0 mod 8 /\
                         k0 mod 8 <= j /\ j <= k0 /\ (k0 - j) mod 8 = 0 /\ k0 <= n /\ bwd mem (s V_MEM64) src d n j)
    | 0x15e814 => Inv 0 (mv_base s /\ src < d /\ s R_X4 = src /\ ∃ k, s R_X3 = k /\ k <= n /\ bwd mem (s V_MEM64) src d n k)
    | 0x15e7b4 => Inv 0 (mv_base s /\ copied mem (s V_MEM64) src d n)
    | 0x15e7b8 => Post 0 (memcpy_post mem d src n sp raddr s)
    | _ => NoInv
    end.
  Definition mva_exits := make_exits 0 memmove_armv8 mva_inv_fn.
  Definition mva_invs := make_invs 0 memmove_armv8 mva_inv_fn.
End Invariants.
