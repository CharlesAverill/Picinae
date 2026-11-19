(* mempcpy (n <= 128) -- program, frame, invariants.
   Written by Grok Bot (agent coqettu); machine-checked by Rocq. *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require mempcpy_armv8 memcpy_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
From Grok.proofs Require Import memcpy_defs memcpy_proof.
Import ARM8Notations.
Open Scope N.

Definition mp_prog : program := updateall2 mempcpy_armv8.mempcpy_armv8 memcpy_armv8.memcpy_armv8.

Lemma mp_prog_contains: mempcpy_armv8.mempcpy_armv8 ⊆2 mp_prog.
Proof.
  intros s a insn SC. unfold mp_prog, updateall2, updateall, memcpy_armv8.memcpy_armv8.
  repeat first
  [ exact SC | discriminate SC
  | match goal with |- context [match ?n with _ => _ end] => is_var n; destruct n end ].
Qed.

Theorem mp_prog_welltyped: welltyped_prog arm8typctx mp_prog.
Proof.
  intros s a. unfold mp_prog, updateall2, updateall.
  destruct (memcpy_armv8.memcpy_armv8 s a) as [[sz q]|] eqn:TL.
    pose proof (memcpy_welltyped s a) as WT. rewrite TL in WT. exact WT.
    apply mempcpy_armv8.welltyped.
Qed.

Section Invariants.
  Variables (sp mem raddr d src n x29 : N).
  (* memory at the call to memcpy: x29, x30 saved at sp-32, sp-24 and n at sp-8 *)
  Definition mp_fm := mem [Ⓠ sp ⊖ 32 := x29] [Ⓠ sp ⊖ 24 := raddr] [Ⓠ sp ⊖ 8 := n].
  Definition mp_pre (s:store) :=
    s R_X0 = d /\ s R_X1 = src /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\
    n <= 128 /\ d + n < 2^64 /\ src + n < 2^64 /\ 32 <= sp /\ sp < 2^64 /\ (d + n <= sp - 32 \/ sp <= d).
  Definition mp_post (s:store) :=
    s R_X0 = d + n /\ s R_SP = sp /\ s R_X30 = raddr /\ s R_X29 = x29 /\ copied mp_fm (s V_MEM64) src d n.
  Definition mp_inv_fn T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x15e81c => Inv 1 (mp_pre s)
    | 0x15e838 => Post 1 (mp_post s)
    | _ => memcpy_inv_fn mp_fm d src n (sp ⊖ 32) 0x15e82c T Inv Post NoInv s a
    end.
  Definition mp_exits0 := make_exits 0 mp_prog mp_inv_fn.
  Definition mp_invs0 := make_invs 0 mp_prog mp_inv_fn.
  Definition mp_exits1 := make_exits 1 mp_prog mp_inv_fn.
  Definition mp_invs1 := make_invs 1 mp_prog mp_inv_fn.
End Invariants.
