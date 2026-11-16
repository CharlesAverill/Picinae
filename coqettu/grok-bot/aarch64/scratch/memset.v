From Stdlib Require Import Utf8 NArith Lia.
Require Import Picinae_armv8.
From Grok.lifted Require Import memset_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokStr GrokFrame GrokFill.
Import ARM8Notations.
Open Scope N.
Set Printing Depth 100000.

Theorem memset_welltyped: welltyped_prog arm8typctx memset_armv8.
Proof. Picinae_typecheck. Qed.

Definition memset_post (mem d c n sp raddr : N) (s:store) :=
  s R_X0 = d /\ s R_SP = sp /\ s R_X30 = raddr /\
  (∀ i, i < n -> s V_MEM64 Ⓑ[d + i] = c mod 2^8) /\
  (∀ a, a < 2^64 -> (a < d \/ d + n <= a) -> s V_MEM64 Ⓑ[a] = mem Ⓑ[a]).

Section Invariants.
  Variables (mem d c n sp raddr : N).
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (s:store) (a:addr) : T :=
    match a with
    | 0x118400 => Inv 0 (s R_X0 = d /\ s R_X1 = c /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         n <= 96 /\ d + n <= 2^64)
    | 0x118404 => Inv 0 (s R_X0 = d /\ s R_X2 = n /\ s V_MEM64 = mem /\ s R_SP = sp /\ s R_X30 = raddr /\
                         n <= 96 /\ d + n <= 2^64 /\ splat_bytes (s R_Z0) c 16)
    | 0x118428 | 0x11843c | 0x118450 | 0x11846c | 0x11847c => Post 0 (memset_post mem d c n sp raddr s)
    | _ => NoInv
    end.
  Definition memset_exits := make_exits 0 memset_armv8 invs.
  Definition memset_invs := make_invs 0 memset_armv8 invs.
End Invariants.

Theorem memset_partial_correctness:
  ∀ prog s mem d c n sp raddr t xs'
    (PROG: memset_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x118400, s))
    (MDL: models arm8typctx s)
    (X0: s R_X0 = d) (X1: s R_X1 = c) (X2: s R_X2 = n) (MEM: s V_MEM64 = mem) (SP: s R_SP = sp) (X30: s R_X30 = raddr)
    (SMALL: n <= 96) (NW: d + n <= 2^64),
  satisfies_all prog (memset_invs mem d c n sp raddr) (memset_exits mem d c n sp raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=memset_armv8). exact PROG.
    intros a s1 t1 EXIT NOCODE. unfold memset_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL X0 X1 X2 MEM SP X30 SMALL NW START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & X2 & MEM & SP & X30 & SMALL & NW).
    arm8_step. splits; try assumption. idtac "SPLATGOAL"; match goal with |- ?g => let h := constr:(g) in idtac "RAW"; match h with | splat_bytes _ _ _ => idtac "IS SPLAT" | ?f ?x => idtac "APP" f | _ => idtac "OTHER" end end. admit.
  - destruct PRE as (X0 & X2 & MEM & SP & X30 & SMALL & NW & ZS).
    pose proof (MDL1 R_X0 64 eq_refl) as D64. pose proof (MDL1 R_X2 64 eq_refl) as N64.
    rewrite X0 in D64. rewrite X2 in N64. simpl in D64, N64.
    repeat grok_step.
    all: idtac "POSTGOAL"; dump_ctx.
Admitted.
