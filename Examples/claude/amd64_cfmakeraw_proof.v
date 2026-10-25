(* cfmakeraw -- put a termios structure into "raw" mode

   SEMANTICS
   ---------
   cfmakeraw(t) clears and sets flag bits in the four flag words of *t and
   sets c_cc[VTIME] = 0 and c_cc[VMIN] = 1.  glibc's struct termios on
   x86-64 has c_iflag at 0, c_oflag at 4, c_cflag at 8, c_lflag at 12 and
   c_cc at 17; VTIME = 5 and VMIN = 6, so c_cc[VTIME], c_cc[VMIN] are the
   bytes at 22 and 23 (one 16-bit store of 0x0100).  The compiler reads all
   four flag words, masks them, and writes them back with a single 16-byte
   MOVUPS.  The proof splits that store into four dword stores.

   SPECIFICATION (man 3 termios, Linux man-pages 5.10, Ubuntu 22.04)
   -----------------------------------------------------------------

     void cfmakeraw(struct termios *termios_p);

     cfmakeraw() sets the terminal to something like the "raw" mode of the
     old Version 7 terminal driver: input is available character by
     character, echoing is disabled, and all special processing of terminal
     input and output characters is disabled.  The terminal attributes are
     set as follows:

         termios_p->c_iflag &= ~(IGNBRK | BRKINT | PARMRK | ISTRIP
                         | INLCR | IGNCR | ICRNL | IXON);
         termios_p->c_oflag &= ~OPOST;
         termios_p->c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
         termios_p->c_cflag &= ~(CSIZE | PARENB);
         termios_p->c_cflag |= CS8;

   With the Linux values these masks are ~0x5eb = 0xfffffa14,
   ~OPOST = 0xfffffffe, ~0x804b = 0xffff7fb4, ~0x130 = 0xfffffecf and
   CS8 = 0x30.  The man page does not list the c_cc changes, but glibc's
   source does (c_cc[VMIN] = 1; c_cc[VTIME] = 0).

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol cfmakeraw at 0x11a220 (Ghidra address 0x21a220, image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see cfmakeraw_amd64.v (global addresses).
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = t.
   Output:  memory becomes cfmakeraw_mem m t (below); RSP is unchanged.
            Nothing else in memory changes.
 *)

Require Import Picinae_amd64.
Require Import cfmakeraw_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_ieee.
Import ListNotations.
Open Scope N.

Theorem cfmakeraw_nwc: forall s2 s1, cfmakeraw_amd64 s1 = cfmakeraw_amd64 s2.
Proof. reflexivity. Qed.

Theorem cfmakeraw_welltyped: welltyped_prog x64typctx cfmakeraw_amd64.
Proof. Picinae_typecheck. Qed.

Theorem cfmakeraw_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates cfmakeraw_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

Definition cfmakeraw_mem (m:memory) (t:N) :=
  m [Ⓦ 22 + t := 0x100]
    [Ⓓ t      := m Ⓓ[t] .& 0xfffffa14]
    [Ⓓ t + 4  := m Ⓓ[4 + t] .& 0xfffffffe]
    [Ⓓ t + 8  := m Ⓓ[8 + t] .& 0xfffffecf .| 0x30]
    [Ⓓ t + 12 := m Ⓓ[12 + t] .& 0xffff7fb4].

(* Bit packing, as PUNPCKLDQ/PUNPCKLQDQ build the 16-byte value
   (lor_shiftl_add and lor32 are in amd64_ieee.v). *)
Lemma land32: forall x k, k < 2^32 -> x .& k < 2^32.
Proof.
  intros x k K. apply N.le_lt_trans with k; [|exact K].
  apply N.land_le_r.
Qed.

Lemma mod32_add: forall x y, y < 2^32 -> (x * 2^32 + y) mod 2^32 = y.
Proof. intros. rewrite N.add_comm, N.mod_add, N.mod_small by (lia || discriminate). reflexivity. Qed.

Lemma shr32_add: forall x y, y < 2^32 -> (x * 2^32 + y) >> 32 = x.
Proof.
  intros. rewrite N.shiftr_div_pow2, N.add_comm, N.div_add, N.div_small by (lia || discriminate). reflexivity.
Qed.

(* One 16-byte store of four packed dwords = four dword stores. *)
Lemma setmem16_split: forall (m:memory) p i o c l,
  i < 2^32 -> o < 2^32 -> c < 2^32 -> l < 2^32 ->
  m [Ⓧ p := ((l << 32 .| c) << 64) .| ((o << 32) .| i)] =
  m [Ⓓ p := i] [Ⓓ p + 4 := o] [Ⓓ p + 8 := c] [Ⓓ p + 12 := l].
Proof.
  intros m p i o c l I O C L.
  rewrite (lor_shiftl_add o i 32 I), (lor_shiftl_add l c 32 C), lor_shiftl_add.
  2: { change (2^64) with (2^32 * 2^32). pose proof (N.mul_le_mono_r o (2^32 - 1) (2^32)). lia. }
  replace ((l * 2^32 + c) * 2^64 + (o * 2^32 + i)) with
          (((l * 2^32 + c) * 2^32 + o) * 2^32 + i) by (change (2^64) with (2^32 * 2^32); ring).
  change 16 with (4 + 12). rewrite setmem_split. change (4 * 8) with 32.
  rewrite mod32_add, shr32_add by exact I.
  change 12 with (4 + 8). rewrite setmem_split. change (4 * 8) with 32.
  rewrite mod32_add, shr32_add by exact O.
  change 8 with (4 + 4) at 1. rewrite setmem_split. change (4 * 8) with 32.
  rewrite mod32_add, shr32_add by exact C.
  rewrite <- !N.add_assoc. reflexivity.
Qed.

Definition cfmakeraw_exit (t:trace) :=
  match t with (Addr 2204269,_)::_ => true | _ => false end.

Definition cfmakeraw_invs (m:memory) (a rsp:N) (t:trace) :=
  match t with (Addr x,s)::_ => match x with
  | 2204192 => Some (s V_MEM64 = m /\ s R_RDI = a /\ s R_RSP = rsp)
  | 2204269 => Some (s R_RSP = rsp /\ s V_MEM64 = cfmakeraw_mem m a)
  | _ => None
  end | _ => None end.

Theorem cfmakeraw_correct:
  forall s t s' x' m a rsp
         (ENTRY: startof t (x',s') = (Addr 2204192, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (A: s R_RDI = a) (RSP: s R_RSP = rsp),
  satisfies_all cfmakeraw_amd64 (cfmakeraw_invs m a rsp) cfmakeraw_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply cfmakeraw_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [A RSP]].
  repeat x64_step.
  split. assumption.
  unfold cfmakeraw_mem. rewrite <- setmem16_split.
  2-5: repeat first [apply lor32 | apply land32]; reflexivity.
  reflexivity.
Time Qed.
