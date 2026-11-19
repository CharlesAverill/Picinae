(* explicit_bzero (full memset) definitions -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64.
   Invariant set ebf_invs for proofs/explicit_bzero_full_proof.v (see the header there).
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require explicit_bzero_armv8 memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memset_proof memset_full_defs memset_full_proof explicit_bzero_proof.
Import ARM8Notations.
Open Scope N.

Section Invariants.
  Variables (sp mem raddr d n x29 c : N).
  Definition ebf_invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e108 => Inv 1 (s R_X0 = d /\ s R_X1 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
                         n < 160 /\ 4096 <= d /\ d + n < 2^64)
    | 0x15e120 => Post 1 (eb_post sp mem raddr d n x29 s)
    | _ => memset_full_defs.mf_invs (frame_mem sp mem raddr x29) d c n (sp ⊖ 16) 0x15e11c T Inv Post NoInv s a
    end.
  Definition ebf_exits0 := make_exits 0 eb_prog ebf_invs.
  Definition ebf_invs0 := make_invs 0 eb_prog ebf_invs.
  Definition ebf_exits1 := make_exits 1 eb_prog ebf_invs.
  Definition ebf_invs1 := make_invs 1 eb_prog ebf_invs.
End Invariants.
