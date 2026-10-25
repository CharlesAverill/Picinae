(* sigdescr_np -- return the description of a signal

   SEMANTICS
   ---------
   sigdescr_np(sig) returns the description (e.g. "Interrupt") of signal sig, or NULL if sig is out of
   range.  glibc compares sig (unsigned, 32-bit) against 64 and otherwise
   loads entry sig of the pointer table _sys_siglist (in .data.rel.ro).
   Entries for unnamed signals hold NULL, so the table itself decides the
   result for in-range signals; the theorem states the load exactly.

   SPECIFICATION (man 3 strsignal, Linux man-pages 5.10, Ubuntu 22.04)
   --------------------------------------------------------------------

     const char *sigdescr_np(int sig);
     const char *sigabbrev_np(int sig);

     The sigdescr_np() function returns a string describing the signal
     number passed in the argument sig.  Unlike strsignal() this string is
     not influenced by the current locale.

     The sigabbrev_np() function returns the abbreviated name of the signal,
     sig.  For example, given the value SIGINT, it returns the string "INT".

     The sigdescr_np() and sigabbrev_np() functions return the appropriate
     description string.  The returned string is statically allocated and
     valid for the lifetime of the program.  These functions return NULL
     for an invalid signal number.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigdescr_np at 0x1b17a0 (Ghidra image base 0x100000); _sys_siglist
            at 0x318c80
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigdescr_np_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI = sig (n = RDI mod 2^32); m = memory.
   Output:  RAX = m[0x318c80 + 8n] (8 bytes) if n <= 64, else 0 (NULL).
            RSP and memory are unchanged.
 *)

Require Import Picinae_amd64.
Require Import sigdescr_np_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigdescr_np_nwc: forall s2 s1, sigdescr_np_amd64 s1 = sigdescr_np_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigdescr_np_welltyped: welltyped_prog x64typctx sigdescr_np_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigdescr_np_preserves_memory:
  forall_endstates sigdescr_np_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem sigdescr_np_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigdescr_np_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition TABLE := 3247232.

Definition sigdescr_np_exit (t:trace) :=
  match t with (Addr 1775545,_)::_ => true | _ => false end.

Definition sigdescr_np_invs (m:memory) (n rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 1775520 => Some (s V_MEM64 = m /\ s R_RDI mod 2^32 = n /\ s R_RSP = rsp)
  | 1775545 => Some (s R_RAX = (if n <=? 64 then m Ⓠ[TABLE + 8 * n] else 0) /\ s R_RSP = rsp)
  | _ => None
  end | _ => None end.

Theorem sigdescr_np_correct:
  forall s t s' x' m n rsp
         (ENTRY: startof t (x',s') = (Addr 1775520, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (SIG: s R_RDI mod 2^32 = n) (RSP: s R_RSP = rsp),
  satisfies_all sigdescr_np_amd64 (sigdescr_np_invs m n rsp) sigdescr_np_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigdescr_np_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [SIG RSP]].
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
  all: split; [|assumption].
  all: rewrite ?N.shiftr_0_r, ?SIG in *.
  all: destruct (N.leb_spec n 64).
  all: try (exfalso; lia).
  all: try reflexivity.
  all: rewrite scast_32_64_small by lia; unfold TABLE; f_equal; lia.
Qed.
