(* sigfillset -- fill a signal set

   SEMANTICS
   ---------
   sigfillset(set) stores 0xfffffffe7fffffff into the first 64-bit word of
   sigset_t: every signal 1..64 except 32 and 33, which glibc reserves for
   its threading library (SIGCANCEL, SIGSETXID).  The other 120 bytes of the
   set are not written.  A NULL set fails with errno = EINVAL.

   SPECIFICATION (man 3 sigsetops, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int sigfillset(sigset_t *set);

     sigfillset() initializes set to full, including all signals.

     sigemptyset(), sigfillset(), sigaddset(), and sigdelset() return 0 on
     success and -1 on error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigfillset at 0x142e70 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigfillset_amd64.v.  Offsets are relative
            to the entry; the errno GOT slot was resolved to 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = set, FS_BASE = fs.
   Output:  set <> NULL: RAX = 0, memory = m[set := 0xfffffffe7fffffff]
              (8-byte store), so sigfillset_members: signal n in 1..64 is a
              member iff n <> 32 and n <> 33.
            set = NULL: RAX = 0xffffffff (-1) and errno = EINVAL (22).
            RSP is unchanged.
 *)

Require Import Picinae_amd64.
Require Import sigfillset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigfillset_nwc: forall s2 s1, sigfillset_amd64 s1 = sigfillset_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigfillset_welltyped: welltyped_prog x64typctx sigfillset_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigfillset_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigfillset_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition errno_slot := 0x319e10.
Definition einval (m:memory) (fs:N) := m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22].

Definition sigfillset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 24 | 44 => true | _ => false end | _ => false end.

Definition FULL := 0xfffffffe7fffffff.

Definition sigfillset_post (m:memory) (set fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (set <> 0 -> s R_RAX = 0 /\ s V_MEM64 = m [Ⓠ set := FULL]) /\
  (set = 0 -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition sigfillset_invs (m:memory) (set fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = set /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 24 | 44 => Some (sigfillset_post m set fs rsp s)
  | _ => None
  end | _ => None end.

Theorem sigfillset_correct:
  forall s t s' x' m set fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SET: s R_RDI = set) (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all sigfillset_amd64 (sigfillset_invs m set fs rsp) sigfillset_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigfillset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [SET [FS RSP]]].
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
  all: split; intros; try contradiction.
  all: try (split; [reflexivity | unfold einval, errno_slot; rewrite setmem_mod_l; reflexivity]).
  all: split; reflexivity.
Qed.

(* Members after sigfillset: every signal 1..64 except 32 and 33. *)
Theorem sigfillset_members:
  forall n, 1 <= n <= 64 -> N.testbit FULL (n - 1) = negb ((n =? 32) || (n =? 33)).
Proof.
  intros n N.
  assert (H: forallb (fun n => Bool.eqb (N.testbit FULL (n - 1)) (negb ((n =? 32) || (n =? 33))))
                     (map N.of_nat (seq 1 64)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop, H, in_map_iff. exists (N.to_nat n).
  split. apply N2Nat.id. apply in_seq. lia.
Qed.
