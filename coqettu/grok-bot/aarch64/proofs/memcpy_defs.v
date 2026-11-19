(* memcpy (n <= 128) -- precondition, postcondition, invariants.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memcpy_armv8.
Import ARM8Notations.
Open Scope N.

Definition memcpy_pre (mem d src n sp raddr : N) (s:store) :=
  s R_X0 = d /\ s R_X1 = src /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
  n <= 128 /\ d + n < 2^64 /\ src + n < 2^64.

(* M is mem with n bytes copied from src to d *)
Definition copied mem M (src d n : N) :=
  (∀ i, i < n -> M Ⓑ[d + i] = mem Ⓑ[src + i]) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> M Ⓑ[a] = mem Ⓑ[a]).

Definition memcpy_post (mem d src n sp raddr : N) (s:store) :=
  s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\ copied mem (s V_MEM64) src d n.

Section Invariants.
  Variables (mem d src n sp raddr : N).
  Definition memcpy_inv_fn T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118270 => Inv 0 (memcpy_pre mem d src n sp raddr s)
    | 0x118370 => Inv 0 False
    | 0x1182a0 | 0x1182b8 | 0x1182d4 | 0x1182f8 | 0x118328 | 0x118368 =>
        Post 0 (memcpy_post mem d src n sp raddr s)
    | _ => NoInv
    end.
  Definition memcpy_exits := make_exits 0 memcpy_armv8 memcpy_inv_fn.
  Definition memcpy_invs := make_invs 0 memcpy_armv8 memcpy_inv_fn.
End Invariants.
