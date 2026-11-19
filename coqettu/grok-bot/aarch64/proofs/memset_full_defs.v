(* memset (full) definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Side condition mf_side and invariant set mf_invs for proofs/memset_full_proof.v
   (see the header there for semantics, man page, provenance and the I/O specification).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memset_proof.
Import ARM8Notations.
Open Scope N.

(* side condition: the dczid_el0 / dc zva region (Nop-lifted) is never entered *)
Definition mf_side (c n : N) := n <= 96 \/ c mod 2^8 <> 0 \/ n < 160.

Section Invariants.
  Variables (mem d c n sp raddr : N).
  Definition fbase (s:store) := s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\
                         4096 <= d /\ d + n < 2^64 /\ splat_bytes (s R_Z0) c 16.
  Definition mfb (s:store) := fbase s /\ s R_X2 = n /\ n <= 96.
  Definition mf_loop (s:store) :=
    fbase s /\ s R_X4 = d + n /\ 96 < n /\ d <= s R_X3 + 32 /\ s R_X3 + 96 < d + n /\
    s R_X2 = d + n - s R_X3 - 96 /\
    (∀ i, d <= i -> i < s R_X3 + 32 -> s V_MEM64 Ⓑ[i] = c mod 2^8) /\
    (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).
  Definition mf_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118400 => Inv 0 (s R_X0 = d /\ s R_X1 = c /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         mf_side c n /\ 4096 <= d /\ d + n < 2^64)
    | 0x118404 => Inv 0 (s R_X0 = d /\ s R_X1 = c /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         mf_side c n /\ 4096 <= d /\ d + n < 2^64 /\ splat_bytes (s R_Z0) c 16)
    | 0x118418 => Inv 0 (mfb s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 16)
    | 0x118430 => Inv 0 (mfb s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 8 /\ s R_X1 = s R_Z0 mod 2^64)
    | 0x118440 => Inv 0 (mfb s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ n < 4 /\ s R_X1 = s R_Z0 mod 2^64)
    | 0x118454 => Inv 0 (mfb s /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ 16 <= n)
    | 0x118470 => Inv 0 (mfb s /\ s R_X4 = d + n /\ s V_MEM64 = setmem 64 LittleE 16 mem d (s R_Z0) /\ 64 <= n)
    | 0x118480 => Inv 0 (fbase s /\ s R_X1 = c /\ s R_X2 = n /\ s R_X4 = d + n /\ s V_MEM64 = mem /\ 96 < n /\ mf_side c n)
    | 0x118498 => Inv 0 False
    | 0x1184e8 => Inv 0 (mf_loop s)
    | 0x118428 | 0x11843c | 0x118450 | 0x11846c | 0x11847c | 0x1184d8 | 0x118500 => Post 0 (memset_post mem d c n sp raddr s)
    | _ => NoInv
    end.
  Definition mf_exits := make_exits 0 memset_armv8 mf_invs.
  Definition mf_invs0 := make_invs 0 memset_armv8 mf_invs.
End Invariants.

