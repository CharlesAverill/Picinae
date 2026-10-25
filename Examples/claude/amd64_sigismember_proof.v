(* sigismember -- test membership in a signal set

   SEMANTICS
   ---------
   sigismember(set, signum) returns bit signum-1 of the first 64-bit word of
   sigset_t.  It fails with errno = EINVAL for signum outside 1..64 or a NULL
   set.  Unlike sigaddset/sigdelset it accepts signals 32 and 33.

   SPECIFICATION (man 3 sigsetops, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int sigismember(const sigset_t *set, int signum);

     sigismember() tests whether signum is a member of set.

     sigismember() returns 1 if signum is a member of set, 0 if signum is
     not a member, and -1 on error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigismember at 0x142f40 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigismember_amd64.v.  Offsets are relative
            to the entry; the errno GOT slot was resolved to 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set, ESI = signum (n = RSI mod 2^32), FS_BASE = fs.
   Output:  If 1 <= n <= 64 and set <> NULL: RAX = 1 if bit n-1 of the first
            word is set, else 0; memory unchanged.  Otherwise RAX = 0xffffffff
            (-1) and errno = EINVAL (22).  RSP is unchanged.
 *)

Require Import Picinae_amd64.
Require Import sigismember_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigismember_nwc: forall s2 s1, sigismember_amd64 s1 = sigismember_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigismember_welltyped: welltyped_prog x64typctx sigismember_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigismember_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigismember_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition errno_slot := 0x319e10.
Definition einval (m:memory) (fs:N) := m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22].

Definition sigismember_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 34 | 59 => true | _ => false end | _ => false end.

Definition sigismember_post (m:memory) (set n fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (1 <= n <= 64 -> set <> 0 ->
     s R_RAX = (if N.testbit (m Ⓠ[set]) (n - 1) then 1 else 0) /\ s V_MEM64 = m) /\
  (~ (1 <= n <= 64 /\ set <> 0) -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition sigismember_invs (m:memory) (set n fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_RSI mod 2^32 = n /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 34 | 59 => Some (sigismember_post m set n fs rsp s)
  | _ => None
  end | _ => None end.

Theorem sigismember_correct:
  forall s t s' x' m set n fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (SIG: s R_RSI mod 2^32 = n)
         (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all sigismember_amd64 (sigismember_invs m set n fs rsp) sigismember_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigismember_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [SET [SIG [FS RSP]]]].
  repeat x64_step.
  all: repeat match goal with
       | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
       | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
       | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
       end.
  all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                            | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end.
  all: repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                            | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.
  all: try discriminate.
  all: split; [assumption|].
  all: unfold msub in *; change (2^6) with 64 in *; change (2^32) with 4294967296 in *.
  all: split; intros.
  all: try (exfalso; lia).
  all: try (exfalso; match goal with H: ~ _ |- _ => apply H; split; [lia | assumption] end).
  all: try (split; [reflexivity | unfold einval, errno_slot; rewrite setmem_mod_l; reflexivity]).
  all: assert (K: (s1 R_RSI + (64 - 1 mod 64)) mod 64 = n - 1) by lia.
  all: rewrite K, N.shiftl_1_l, pow2_land_eqb0.
  all: split; [destruct (N.testbit _ _); reflexivity | reflexivity].
Qed.
