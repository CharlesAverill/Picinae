(* memrchr (scalar path): precondition, postcondition and invariants.
   Written by Grok Bot (agent coqettu) and machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memrchr_armv8.
Import ARM8Notations.
Open Scope N.

(* No byte equal to c in [p+k, p+n). *)
Definition nomatch_above (m:memory) (p c k n:N) := ∀ i, k <= i -> i < n -> m Ⓑ[p + i] ≠ c.

Section Invariants.
  Variables (lv sp mem raddr x19 x29 p c n : N).
  Definition c8 := c mod 2^8.
  Definition mrc_pre (s:store) :=
    s R_X0 = p /\ s R_X1 = c /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
    0 < p /\ p + n < 2^64 /\ (n <= 14 \/ (p + n) mod 16 <> 0) /\ s R_X19 = x19 /\ s R_X29 = x29.
  Definition mrc_post (s:store) :=
    ((∃ k, k < n /\ s R_X0 = p + k /\ mem Ⓑ[p + k] = c8 /\ nomatch_above mem p c8 (k + 1) n) \/
     (s R_X0 = 0 /\ nomatch_above mem p c8 0 n)) /\
    s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X29 = x29.
  (* scalar loop at 0x15e924 (mov x0,x2): X2 = p+k-1 is the next byte to test;
     bytes [p+k, p+n) do not match. *)
  Definition mrc_loop (s:store) :=
    ∃ k, k <= n /\ s R_X2 = p + k - 1 /\ s R_X4 = p - 1 /\ s R_X1 = c8 /\
         0 < p /\ p + n < 2^64 /\ nomatch_above mem p c8 k n /\
         s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X19 = x19 /\ s R_X29 = x29.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e83c => Inv lv (mrc_pre s)
    (* NEON block path: excluded by the precondition *)
    | 0x15e85c => Inv lv False
    | 0x15e924 => Inv lv (mrc_loop s)
    | 0x15e948 => Post lv (mrc_post s)
    | _ => NoInv
    end.
  (* lv: invariant-family level (0 for memrchr itself, 1 inside strrchr). *)
  Definition memrchr_exits := make_exits lv memrchr_armv8 invs.
  Definition memrchr_invs := make_invs lv memrchr_armv8 invs.
End Invariants.
