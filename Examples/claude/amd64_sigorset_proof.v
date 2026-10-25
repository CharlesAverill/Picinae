(* sigorset -- union of two signal sets (GNU extension)

   SEMANTICS
   ---------
   sigorset(dest, left, right) stores the union of the first 64-bit words of
   left and right into the first word of dest (signals 1..64; the other 120
   bytes of sigset_t are not touched).  If any pointer is NULL it fails with
   errno = EINVAL.

   SPECIFICATION (man 3 sigsetops, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------

     int sigorset(sigset_t *dest, const sigset_t *left, const sigset_t *right);

     sigandset() places the intersection of the sets left and right in dest.
     sigorset() places the union of the sets left and right in dest.

     sigandset() and sigorset() return 0 on success, and -1 on failure.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol sigorset at 0x1430e0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see sigorset_amd64.v.  Offsets are relative
            to the entry; the errno GOT slot was resolved to 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = left, RDX = right, FS_BASE = fs.
   Output:  All three nonzero: RAX = 0 and memory = m[dest := m[left] .|
            m[right]] (8-byte store).  Otherwise RAX = 0xffffffff (-1) and
            errno = EINVAL (22).  RSP is unchanged.
 *)

Require Import Picinae_amd64.
Require Import sigorset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem sigorset_nwc: forall s2 s1, sigorset_amd64 s1 = sigorset_amd64 s2.
Proof. reflexivity. Qed.

Theorem sigorset_welltyped: welltyped_prog x64typctx sigorset_amd64.
Proof. Picinae_typecheck. Qed.

Theorem sigorset_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates sigorset_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition errno_slot := 0x319e10.
Definition einval (m:memory) (fs:N) := m [Ⓓ fs ⊕ m Ⓠ[errno_slot] := 22].

Definition sigorset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 36 | 59 => true | _ => false end | _ => false end.

Definition sigorset_post (m:memory) (d l r fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (d <> 0 -> l <> 0 -> r <> 0 -> s R_RAX = 0 /\ s V_MEM64 = m [Ⓠ d := m Ⓠ[l] .| m Ⓠ[r]]) /\
  (~ (d <> 0 /\ l <> 0 /\ r <> 0) -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition sigorset_invs (m:memory) (d l r fs rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = l /\ s R_RDX = r /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 36 | 59 => Some (sigorset_post m d l r fs rsp s)
  | _ => None
  end | _ => None end.

Theorem sigorset_correct:
  forall s t s' x' m d l r fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (L: s R_RSI = l) (R: s R_RDX = r)
         (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all sigorset_amd64 (sigorset_invs m d l r fs rsp) sigorset_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply sigorset_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [D [L [R [FS RSP]]]]].
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
  all: split; intros.
  all: try (exfalso; lia).
  all: try (exfalso; match goal with H: ~ _ |- _ => apply H; split; [|split]; assumption end).
  all: try (split; [reflexivity | unfold einval, errno_slot; rewrite setmem_mod_l; reflexivity]).
  all: split; reflexivity.
Qed.
