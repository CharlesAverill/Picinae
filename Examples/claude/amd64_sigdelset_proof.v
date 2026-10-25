(* sigdelset -- remove a signal from a signal set

   SEMANTICS
   ---------
   sigdelset(set, signum) clears bit sig-1 of the first word of sigset_t (signal n is bit n-1; see
   amd64_sigemptyset_proof.v).  It fails with errno = EINVAL when signum is
   outside 1..64, when set is NULL, and also when signum is 32 or 33: glibc
   reserves those two real-time signals for its threading library (SIGCANCEL
   and SIGSETXID) and refuses to let applications add or remove them.  The
   man page does not mention this; it only says EINVAL means "sig is not a
   valid signal".

   SPECIFICATION (man 3 sigsetops, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int sigdelset(sigset_t *set, int signum);

     sigaddset() and sigdelset() add and delete respectively signal signum from set.

     sigemptyset(), sigfillset(), sigaddset(), and sigdelset() return 0 on
     success and -1 on error.

     EINVAL sig is not a valid signal.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigdelset at 0x142ef0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigdelset_amd64.v.  Offsets are relative
            to the entry; the errno GOT slot was resolved to 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set, ESI = signum (n = RSI mod 2^32), FS_BASE = fs.
   Output:  If 1 <= n <= 64, n <> 32, n <> 33 and set <> NULL: RAX = 0 and
            the first word of the set becomes N.clearbit word (n-1).
            Otherwise: RAX = 0xffffffff (-1) and errno = EINVAL (22).
            RSP is unchanged; no other memory changes.
 *)

Require Import Picinae_amd64.
Require Import sigdelset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigdelset_nwc: forall s2 s1, sigdelset_amd64 s1 = sigdelset_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigdelset_welltyped: welltyped_prog x64typctx sigdelset_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigdelset_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigdelset_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition errno_slot := 0x319e10.
Definition einval (m:memory) (fs:N) := m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22].

Definition sigdelset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 40 | 67 => true | _ => false end | _ => false end.

Definition sig_ok (n:N) := 1 <= n <= 64 /\ n <> 32 /\ n <> 33.

Definition sigdelset_post (m:memory) (set n fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (sig_ok n -> set <> 0 -> s R_RAX = 0 /\ s V_MEM64 = m [Ⓠ set := N.clearbit (m Ⓠ[set]) (n - 1)]) /\
  (~ (sig_ok n /\ set <> 0) -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition sigdelset_invs (m:memory) (set n fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_RSI mod 2^32 = n /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 40 | 67 => Some (sigdelset_post m set n fs rsp s)
  | _ => None
  end | _ => None end.

(* ROL of 0xfffffffffffffffe by k clears exactly bit k (mod 2^64). *)
Lemma rol_clear: forall x k, k < 64 ->
  (x .& (18446744073709551614 << k .| 18446744073709551614 >> (64 - k))) mod 2^64 =
  N.clearbit x k mod 2^64.
Proof.
  intros x k K.
  assert (V: forall j, N.testbit 18446744073709551614 j = (j <? 64) && negb (j =? 0)).
  { intro j. change 18446744073709551614 with (N.ldiff (N.ones 64) 1).
    rewrite N.ldiff_spec. destruct (N.ltb_spec j 64).
    - rewrite N.ones_spec_low by lia. destruct j as [|p]; [reflexivity | destruct p; reflexivity].
    - rewrite N.ones_spec_high by lia. reflexivity. }
  apply N.bits_inj. intro i. destruct (N.ltb_spec i 64) as [I|I].
  - rewrite !N.mod_pow2_bits_low by exact I.
    rewrite N.land_spec, N.lor_spec, N.clearbit_eqb, N.shiftr_spec by lia.
    rewrite V. destruct (N.ltb_spec i k) as [H|H].
    + rewrite (N.shiftl_spec_low _ k i) by exact H. rewrite (proj2 (N.ltb_lt (i + (64 - k)) 64)) by lia.
      replace (k =? i) with false by (symmetry; apply N.eqb_neq; lia).
      replace (i + (64 - k) =? 0) with false by (symmetry; apply N.eqb_neq; lia).
      destruct (N.testbit x i); reflexivity.
    + rewrite (N.shiftl_spec_high' 18446744073709551614 k i H). rewrite V.
      replace (i + (64 - k) <? 64) with false by (symmetry; apply N.ltb_ge; lia).
      replace (i - k <? 64) with true by (symmetry; apply N.ltb_lt; lia).
      destruct (N.eqb_spec k i) as [E|E].
      * subst. replace (i - i =? 0) with true by (symmetry; apply N.eqb_eq; lia).
        destruct (N.testbit x i); reflexivity.
      * replace (i - k =? 0) with false by (symmetry; apply N.eqb_neq; lia).
        destruct (N.testbit x i); reflexivity.
  - rewrite !N.mod_pow2_bits_high by exact I. reflexivity.
Qed.

Theorem sigdelset_correct:
  forall s t s' x' m set n fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (SIG: s R_RSI mod 2^32 = n)
         (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all sigdelset_amd64 (sigdelset_invs m set n fs rsp) sigdelset_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigdelset_welltyped. intro MDL1.
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
  all: unfold sig_ok, msub in *; change (2^6) with 64 in *; change (2^8) with 256 in *;
       change (2^32) with 4294967296 in *.
  all: split; intros.
  all: try (exfalso; lia).
  all: try (exfalso; match goal with H: ~ _ |- _ => apply H; split; [lia | assumption] end).
  all: try (split; [reflexivity | unfold einval, errno_slot; rewrite setmem_mod_l; reflexivity]).
  all: assert (K: (s1 R_RSI + (64 - 1 mod 64)) mod 64 = n - 1) by lia.
  all: assert (K2: (64 + (256 - (n - 1) mod 256)) mod 256 = 64 - (n - 1)) by lia.
  all: rewrite K, K2; split; [reflexivity|].
  all: rewrite <- (setmem_mod_r 64 LittleE 8 m set (N.clearbit _ _)).
  all: rewrite <- (setmem_mod_r 64 LittleE 8 m set (m Ⓠ[set] .& _)).
  all: f_equal; apply rol_clear; lia.
Qed.
