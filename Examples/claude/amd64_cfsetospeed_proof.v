(* cfsetospeed -- set the output baud rate in a termios structure

   SEMANTICS
   ---------
   cfsetospeed(t, speed) checks that speed is a baud-rate code, then stores
   it in t->c_ospeed (offset 56) and in the CBAUD bits of t->c_cflag
   (offset 8): c_cflag = (c_cflag & ~CBAUD) | speed.  An invalid speed sets
   errno = EINVAL and returns -1 without touching t.  The binary also accepts
   0x1000 (BOTHER, "arbitrary rate"), which lies inside CBAUD.

   SPECIFICATION (man 3 termios, Linux man-pages 5.10, Ubuntu 22.04)
   -----------------------------------------------------------------

     int cfsetospeed(struct termios *termios_p, speed_t speed);

     cfsetospeed() sets the output baud rate stored in the termios structure
     pointed to by termios_p to speed, which must be one of these constants:
     B0, B50, B75, ..., B38400, B57600, B115200, ..., B4000000.

     cfsetispeed() and cfsetospeed() return 0 if successful and -1 on error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol cfsetospeed at 0x119c60 (Ghidra address 0x219c60, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see cfsetospeed_amd64.v.  Offsets are
            relative to the entry; the errno GOT slot is 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = t, ESI = speed (n = RSI mod 2^32), FS_BASE = fs.
   Output:  If speed_ok n (see amd64_termios.v): RAX = 0, and memory becomes
            m [Ⓓ t+56 := n] [Ⓓ t+8 := (m Ⓓ[t+8] & 0xffffeff0) | n].
            Otherwise: RAX = 0xffffffff (-1) and errno = EINVAL (22).
            RSP is unchanged; no other memory changes.
 *)

Require Import Picinae_amd64.
Require Import cfsetospeed_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_termios.
Import ListNotations.
Open Scope N.

Theorem cfsetospeed_nwc: forall s2 s1, cfsetospeed_amd64 s1 = cfsetospeed_amd64 s2.
Proof. reflexivity. Qed.

Theorem cfsetospeed_welltyped: welltyped_prog x64typctx cfsetospeed_amd64.
Proof. Picinae_typecheck. Qed.

Theorem cfsetospeed_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates cfsetospeed_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition cfsetospeed_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 41 | 61 => true | _ => false end | _ => false end.

Definition cfsetospeed_post (m:memory) (a n fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (speed_ok n -> s R_RAX = 0 /\
     s V_MEM64 = m [Ⓓ 56 + a := n] [Ⓓ 8 + a := m Ⓓ[8 + a] .& 0xffffeff0 .| n]) /\
  (~ speed_ok n -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition cfsetospeed_invs (m:memory) (a n fs rsp:N) (t:trace) :=
  match t with (Addr x,s)::_ => match x with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = a /\ s R_RSI mod 2^32 = n /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 41 | 61 => Some (cfsetospeed_post m a n fs rsp s)
  | _ => None
  end | _ => None end.

Theorem cfsetospeed_correct:
  forall s t s' x' m a n fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (A: s R_RDI = a) (SPD: s R_RSI mod 2^32 = n)
         (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all cfsetospeed_amd64 (cfsetospeed_invs m a n fs rsp) cfsetospeed_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfsetospeed_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [A [SPD [FS RSP]]]].
  repeat x64_step.
  all: split; [assumption|].
  (* inside CBAUD *)
  - apply N.eqb_eq in BC. rewrite mask_mod, SPD in BC.
    split; [intros _|intro NOK; exfalso; apply NOK; left; exact BC].
    split. reflexivity.
    rewrite (setmem_dword _ (8 + a)), cflag_mod, SPD, (setmem_dword _ (56 + a)), SPD. reflexivity.
  (* B57600..B4000000 *)
  - apply ja_speed_not_taken in BC0. rewrite SPD in BC0.
    split; [intros _|intro NOK; exfalso; apply NOK; right; exact BC0].
    split. reflexivity.
    rewrite (setmem_dword _ (8 + a)), cflag_mod, SPD, (setmem_dword _ (56 + a)), SPD. reflexivity.
  (* invalid *)
  - apply N.eqb_neq in BC. rewrite mask_mod, SPD in BC.
    apply ja_speed_taken in BC0. rewrite SPD in BC0.
    split; [intros [OK|OK]; exfalso; [apply BC|apply BC0]; exact OK|intros _].
    split. reflexivity. unfold einval, errno_slot. rewrite setmem_mod_l. reflexivity.
Time Qed.
