(* cfsetispeed -- set the input baud rate in a termios structure

   SEMANTICS
   ---------
   cfsetispeed(t, speed) checks speed exactly as cfsetospeed does, then
   stores it in t->c_ispeed (offset 52).  Speed 0 means "same as the output
   speed": glibc records it by setting its private IBAUD0 bit (2^31) in
   t->c_iflag (offset 0) and leaves c_cflag alone.  A nonzero speed clears
   IBAUD0 and sets the CBAUD bits of t->c_cflag (offset 8) to speed, as
   cfsetospeed does.  An invalid speed sets errno = EINVAL and returns -1
   without touching t.

   SPECIFICATION (man 3 termios, Linux man-pages 5.10, Ubuntu 22.04)
   -----------------------------------------------------------------

     int cfsetispeed(struct termios *termios_p, speed_t speed);

     cfsetispeed() sets the input baud rate stored in the termios structure
     to speed, which must be specified as one of the Bnnn constants listed
     above for cfsetospeed().  If the input baud rate is set to zero, the
     input baud rate will be equal to the output baud rate.

     cfsetispeed() and cfsetospeed() return 0 if successful and -1 on error.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol cfsetispeed at 0x119ca0 (Ghidra address 0x219ca0, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see cfsetispeed_amd64.v.  Offsets are
            relative to the entry; the errno GOT slot is 0x319e10.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = t, ESI = speed (n = RSI mod 2^32), FS_BASE = fs.
   Output:  n = 0: RAX = 0 and memory becomes
              m [Ⓓ t+52 := 0] [Ⓓ t := m Ⓓ[t] | 0x80000000].
            speed_ok n and n <> 0: RAX = 0 and memory becomes
              m [Ⓓ t+52 := n] [Ⓓ t := m Ⓓ[t] & 0x7fffffff]
                [Ⓓ t+8 := (m Ⓓ[t+8] & 0xffffeff0) | n].
            Otherwise: RAX = 0xffffffff (-1) and errno = EINVAL (22).
            RSP is unchanged; no other memory changes.
 *)

Require Import Picinae_amd64.
Require Import cfsetispeed_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_termios.
Import ListNotations.
Open Scope N.

Theorem cfsetispeed_nwc: forall s2 s1, cfsetispeed_amd64 s1 = cfsetispeed_amd64 s2.
Proof. reflexivity. Qed.

Theorem cfsetispeed_welltyped: welltyped_prog x64typctx cfsetispeed_amd64.
Proof. Picinae_typecheck. Qed.

Theorem cfsetispeed_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates cfsetispeed_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition cfsetispeed_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with 47 | 66 | 86 => true | _ => false end | _ => false end.

Definition cfsetispeed_post (m:memory) (a n fs rsp:N) (s:store) :=
  s R_RSP = rsp /\
  (n = 0 -> s R_RAX = 0 /\ s V_MEM64 = m [Ⓓ 52 + a := 0] [Ⓓ a := m Ⓓ[a] .| 0x80000000]) /\
  (speed_ok n -> n <> 0 -> s R_RAX = 0 /\
     s V_MEM64 = m [Ⓓ 52 + a := n] [Ⓓ a := m Ⓓ[a] .& 0x7fffffff]
                   [Ⓓ 8 + a := m Ⓓ[8 + a] .& 0xffffeff0 .| n]) /\
  (~ speed_ok n -> s R_RAX = 0xffffffff /\ s V_MEM64 = einval m fs).

Definition cfsetispeed_invs (m:memory) (a n fs rsp:N) (t:trace) :=
  match t with (Addr x,s)::_ => match x with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = a /\ s R_RSI mod 2^32 = n /\ s R_FS_BASE = fs /\ s R_RSP = rsp)
  | 47 | 66 | 86 => Some (cfsetispeed_post m a n fs rsp s)
  | _ => None
  end | _ => None end.

Theorem cfsetispeed_correct:
  forall s t s' x' m a n fs rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (A: s R_RDI = a) (SPD: s R_RSI mod 2^32 = n)
         (FS: s R_FS_BASE = fs) (RSP: s R_RSP = rsp),
  satisfies_all cfsetispeed_amd64 (cfsetispeed_invs m a n fs rsp) cfsetispeed_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfsetispeed_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [A [SPD [FS RSP]]]].
  repeat x64_step.
  all: split; [assumption|].
  (* speed 0: set IBAUD0 *)
  - rewrite SPD in BC0. apply N.eqb_eq in BC0. apply N.eqb_eq in BC. rewrite mask_mod, SPD in BC.
    split; [intros _|split; [intros _ NZ; contradiction|intro NOK; exfalso; apply NOK; left; exact BC]].
    split. reflexivity. rewrite (setmem_dword _ (52 + a)), SPD, BC0. reflexivity.
  (* nonzero speed inside CBAUD *)
  - rewrite SPD in BC0. apply N.eqb_neq in BC0. apply N.eqb_eq in BC. rewrite mask_mod, SPD in BC.
    split; [intro; contradiction|split; [intros _ _|intro NOK; exfalso; apply NOK; left; exact BC]].
    split. reflexivity.
    rewrite (setmem_dword _ (8 + a)), cflag_mod, SPD, (setmem_dword _ (52 + a)), SPD. reflexivity.
  (* B57600..B4000000 *)
  - apply ja_speed_not_taken in BC0. rewrite SPD in BC0.
    split; [intro; lia|split; [intros _ _|intro NOK; exfalso; apply NOK; right; exact BC0]].
    split. reflexivity.
    rewrite (setmem_dword _ (8 + a)), cflag_mod, SPD, (setmem_dword _ (52 + a)), SPD. reflexivity.
  (* invalid *)
  - apply N.eqb_neq in BC. rewrite mask_mod, SPD in BC.
    apply ja_speed_taken in BC0. rewrite SPD in BC0.
    assert (NOK: ~ speed_ok n) by (intros [OK|OK]; [apply BC|apply BC0]; exact OK).
    split; [intro Z; exfalso; apply NOK; left; rewrite Z; reflexivity|].
    split; [intro; contradiction|intros _].
    split. reflexivity. unfold einval, errno_slot. rewrite setmem_mod_l. reflexivity.
Time Qed.
