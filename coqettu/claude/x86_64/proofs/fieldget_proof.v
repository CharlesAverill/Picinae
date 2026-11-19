(* cfgetospeed cfgetispeed dirfd telldir ns_get16 -- field readers
   (musl x86_64, C)

   SEMANTICS
   ---------
   musl:  speed_t cfgetospeed(const struct termios *tio)
          { return tio->c_cflag & CBAUD; }
          speed_t cfgetispeed(const struct termios *tio)
          { return (tio->c_cflag & CIBAUD) >> 16; }
          int dirfd(DIR *d) { return d->fd; }
          long telldir(DIR *dir) { return dir->tell; }
          unsigned ns_get16(const unsigned char *cp) { return cp[0]<<8 | cp[1]; }
   (src/termios/cfgetospeed.c, src/dirent/dirfd.c, telldir.c,
   src/network/ns_parse.c).  c_cflag is the 32-bit
   field at offset 8 of struct termios, CBAUD = 0x100f, CIBAUD = CBAUD<<16;
   the compiler reads the upper half of c_cflag as the word at offset 10.
   DIR's fd is the int at offset 8 and tell the long at offset 0.

   SPECIFICATION (man 3 termios, man 3 dirfd, Linux man-pages 6.9.1,
   paraphrased)
   ------------------------------------------------------------------
     speed_t cfgetospeed(const struct termios *termios_p);
     speed_t cfgetispeed(const struct termios *termios_p);
     return the output / input baud rate stored in the termios structure.
     int dirfd(DIR *dirp);  returns the file descriptor associated with the
     directory stream dirp.  long telldir(DIR *dirp);  returns the current
     location associated with the directory stream dirp.  ns_get16 (resolver
     helper, no man page) reads a 16-bit network-order (big-endian) value.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            cfgetospeed at 0x6634d, cfgetispeed at 0x66356, dirfd at 0x41c0f,
            telldir at 0x42022, ns_get16 at 0x5ab35 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/{cfgetospeed,cfgetispeed,dirfd,telldir,ns_get16}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = p (the struct pointer); m = memory.  No precondition.
   Output:  At the RET: cfgetospeed: RAX = m[p+8 .. p+12) .& 0x100f;
            cfgetispeed: RAX = m[p+10 .. p+12) .& 0x100f (= (c_cflag &
            CIBAUD) >> 16); dirfd: RAX = the dword at p+8; telldir: RAX =
            the qword at p; ns_get16: RAX = the big-endian word at p
            (getmem 64 BigE 2 m p).  Memory, RSP and
            RBX, RBP, R12-R15 unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.cfgetospeed_amd64 CoqEtTu.programs.cfgetispeed_amd64 CoqEtTu.programs.dirfd_amd64
               CoqEtTu.programs.telldir_amd64 CoqEtTu.programs.ns_get16_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Definition fg_exit (r:N) (t:trace) :=
  match t with (Addr a,_)::_ => a =? r | _ => false end.

Definition fg_invs (e r:N) (f:memory -> N -> N) (s0:store) (m p:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if a =? r then Some (s R_RAX = f m p /\ s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Ltac fg_tac wt :=
  intros prog s0 t s' x' m p P ENTRY MDL MEM Pp;
  eapply satisfies_all_pmono; [exact P| |];
  [ intros a s1 t1 EXIT NOCODE; unfold fg_invs, fg_exit in *;
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]
  | ];
  intros [x1 s1] t1 START; rewrite ENTRY in START;
  apply prove_invs;
  [ simpl; rewrite START; x64_step; conj_tac; apply callee_saved_eq_refl
  | intros tt1 aa1 ss1 tt2 UT SPL PRE;
    erewrite startof_prefix in START; try eassumption;
    eapply models_at_invariant; try eassumption; [exact wt|]; intro MDL1;
    destruct_inv 64 PRE;
    destruct PRE as [MEM' [Pp' [RSP CS]]];
    repeat x64_step; conj_tac ].

Theorem cfgetospeed_correct:
  forall prog s t s' x' m p (P: cfgetospeed_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x16634d, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (Pp: s R_RDI = p),
  satisfies_all prog (fg_invs 0x16634d 0x166355 (fun m p => m Ⓓ[8 + p] .& 0x100f) s m p)
                (fg_exit 0x166355) ((x',s')::t).
Proof. fg_tac cfgetospeed_amd64.welltyped. Qed.

Theorem cfgetispeed_correct:
  forall prog s t s' x' m p (P: cfgetispeed_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x166356, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (Pp: s R_RDI = p),
  satisfies_all prog (fg_invs 0x166356 0x16635f (fun m p => m Ⓦ[10 + p] .& 0x100f) s m p)
                (fg_exit 0x16635f) ((x',s')::t).
Proof. fg_tac cfgetispeed_amd64.welltyped. Qed.

Theorem dirfd_correct:
  forall prog s t s' x' m p (P: dirfd_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x141c0f, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (Pp: s R_RDI = p),
  satisfies_all prog (fg_invs 0x141c0f 0x141c12 (fun m p => m Ⓓ[8 + p]) s m p)
                (fg_exit 0x141c12) ((x',s')::t).
Proof. fg_tac dirfd_amd64.welltyped. Qed.

Theorem telldir_correct:
  forall prog s t s' x' m p (P: telldir_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x142022, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (Pp: s R_RDI = p),
  satisfies_all prog (fg_invs 0x142022 0x142025 (fun m p => m Ⓠ[p]) s m p)
                (fg_exit 0x142025) ((x',s')::t).
Proof. fg_tac telldir_amd64.welltyped. Qed.

Lemma be16: forall (m:memory) p, getmem 64 BigE 2 m p = m Ⓑ[p] << 8 .| m Ⓑ[1 + p].
Proof.
  intros. change 2 with (1 + 1). rewrite getmem_split. unfold cbits.
  rewrite !getmem_1, (N.add_comm p 1). reflexivity.
Qed.

Theorem ns_get16_correct:
  forall prog s t s' x' m p (P: ns_get16_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15ab35, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (Pp: s R_RDI = p),
  satisfies_all prog (fg_invs 0x15ab35 0x15ab3f (fun m p => getmem 64 BigE 2 m p) s m p)
                (fg_exit 0x15ab3f) ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p P ENTRY MDL MEM Pp.
  eapply satisfies_all_pmono; [exact P| |].
  { intros a s1 t1 EXIT NOCODE; unfold fg_invs, fg_exit in *.
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]. }
  intros [x1 s1] t1 START; rewrite ENTRY in START.
  apply prove_invs.
  simpl; rewrite START; x64_step; conj_tac; apply callee_saved_eq_refl.
  intros tt1 aa1 ss1 tt2 UT SPL PRE.
  erewrite startof_prefix in START; try eassumption.
  eapply models_at_invariant; try eassumption; [exact ns_get16_amd64.welltyped|]; intro MDL1.
  destruct_inv 64 PRE. destruct PRE as [MEM' [Pp' [RSP CS]]].
  repeat x64_step. rewrite be16. conj_tac.
Qed.
