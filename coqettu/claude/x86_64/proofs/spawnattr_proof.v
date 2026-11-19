(* posix_spawnattr_{destroy,getflags,setflags,getpgroup,setpgroup,
   getschedparam,setschedparam,getschedpolicy,setschedpolicy} -- spawn
   attribute accessors (musl x86_64, C)

   SEMANTICS
   ---------
   musl (src/process/posix_spawnattr_*.c), with posix_spawnattr_t
   { int __flags; pid_t __pgrp; sigset_t __def, __mask; ... }:

       int posix_spawnattr_destroy(posix_spawnattr_t *attr) { return 0; }
       int posix_spawnattr_getflags(const posix_spawnattr_t *restrict attr, short *restrict flags)
       { *flags = attr->__flags; return 0; }
       int posix_spawnattr_setflags(posix_spawnattr_t *attr, short flags)
       { const unsigned all_flags = POSIX_SPAWN_RESETIDS | ... | POSIX_SPAWN_SETSID;   (= 0xff)
         if (flags & ~all_flags) return EINVAL;
         attr->__flags = flags; return 0; }
       int posix_spawnattr_getpgroup(const posix_spawnattr_t *restrict attr, pid_t *restrict pgrp)
       { *pgrp = attr->__pgrp; return 0; }
       int posix_spawnattr_setpgroup(posix_spawnattr_t *attr, pid_t pgrp)
       { attr->__pgrp = pgrp; return 0; }
       int posix_spawnattr_{get,set}sched{param,policy}(...) { return ENOSYS; }

   (setflags is compiled as a sign extension of the short and one unsigned
   compare with 0xff.)

   SPECIFICATION (man 3 posix_spawn, POSIX.1-2017 posix_spawnattr_*,
   paraphrased)
   ------------------------------------------------------------------
     These functions get and set the attributes of a spawn attributes
     object; they return 0 on success or an error number (EINVAL for
     invalid flags; musl does not support the scheduling attributes and
     returns ENOSYS).

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            (addresses: each theorem's entry; Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/posix_spawnattr_*_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = attr, RSI = the second argument; m = memory.  No
            precondition.
   Output:  At the RET: RAX = the return value and memory = the stated
            update of m (sa_invs: fr, fm); RSP and RBX, RBP, R12-R15
            unchanged.  EINVAL = 22, ENOSYS = 38.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.posix_spawnattr_destroy_amd64 CoqEtTu.programs.posix_spawnattr_getflags_amd64
               CoqEtTu.programs.posix_spawnattr_setflags_amd64 CoqEtTu.programs.posix_spawnattr_getpgroup_amd64
               CoqEtTu.programs.posix_spawnattr_setpgroup_amd64 CoqEtTu.programs.posix_spawnattr_getschedparam_amd64
               CoqEtTu.programs.posix_spawnattr_setschedparam_amd64 CoqEtTu.programs.posix_spawnattr_getschedpolicy_amd64
               CoqEtTu.programs.posix_spawnattr_setschedpolicy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia Bool.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Require Import CoqEtTu.proofs.divs_proof.
Open Scope N.

Lemma sc16: forall v, scast 16 64 v mod 2^32 = scast 16 32 v.
Proof. intros. unfold scast. exact (ofZ_hi_lo 32 _). Qed.

Lemma sc16': forall v, scast 16 64 v mod 2^(4*8) = scast 16 32 v.
Proof. exact sc16. Qed.

Ltac num_bc :=
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  end.

Definition sa_exit (r1 r2:N) (t:trace) :=
  match t with (Addr a,_)::_ => (a =? r1) || (a =? r2) | _ => false end.

Definition sa_invs (e r1 r2:N) (fr:memory -> N -> N -> N) (fm:memory -> N -> N -> memory)
           (s0:store) (m x y:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s V_MEM64 = m /\ s R_RDI = x /\ s R_RSI = y /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if (a =? r1) || (a =? r2) then
      Some (s R_RAX = fr m x y /\ s V_MEM64 = fm m x y /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Ltac sa_tac wt :=
  intros prog s0 t s' x' m x y P ENTRY MDL MEM X Y;
  eapply satisfies_all_pmono; [exact P| |];
  [ intros a s1 t1 EXIT NOCODE; unfold sa_invs, sa_exit in *;
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
    destruct PRE as [MEM' [X' [Y' [RSP CS]]]];
    repeat x64_step ].

Theorem posix_spawnattr_destroy_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_destroy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15ccc1, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15ccc1 0x15ccc3 0x15ccc3 (fun _ _ _ => 0) (fun m _ _ => m) s m x y)
                (sa_exit 0x15ccc3 0x15ccc3) ((x',s')::t).
Proof. sa_tac posix_spawnattr_destroy_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_getflags_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_getflags_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15ccc4, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15ccc4 0x15cccb 0x15cccb (fun _ _ _ => 0) (fun m x y => m [Ⓦy := m Ⓓ[x]]) s m x y)
                (sa_exit 0x15cccb 0x15cccb) ((x',s')::t).
Proof. sa_tac posix_spawnattr_getflags_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_setflags_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_setflags_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cda3, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cda3 0x15cdb7 0x15cdb7
                        (fun _ _ y => if 255 <? scast 16 32 (y mod 2^16) then 22 else 0)
                        (fun m x y => if 255 <? scast 16 32 (y mod 2^16) then m else m [Ⓓx := scast 16 32 (y mod 2^16)]) s m x y)
                (sa_exit 0x15cdb7 0x15cdb7) ((x',s')::t).
Proof.
  sa_tac posix_spawnattr_setflags_amd64.welltyped.
  all: bc_norm; rewrite ?N.shiftr_0_r in *; rewrite ?sc16 in *; num_bc.
  all: destruct (N.ltb_spec 255 (scast 16 32 (y mod 2^16))); try (exfalso; lia).
  all: split; [reflexivity | split; [ first [ sreflexivity | exact MEM'
         | (rewrite <- (setmem_mod_r 64 LittleE 4 m x (scast 16 64 (y mod 2^16))), sc16'; sreflexivity) ] | conj_tac ]].
Qed.

Theorem posix_spawnattr_getpgroup_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_getpgroup_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cccc, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cccc 0x15ccd3 0x15ccd3 (fun _ _ _ => 0) (fun m x y => m [Ⓓy := m Ⓓ[4 + x]]) s m x y)
                (sa_exit 0x15ccd3 0x15ccd3) ((x',s')::t).
Proof. sa_tac posix_spawnattr_getpgroup_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_setpgroup_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_setpgroup_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cdb8, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cdb8 0x15cdbd 0x15cdbd (fun _ _ _ => 0) (fun m x y => m [Ⓓ4 + x := y]) s m x y)
                (sa_exit 0x15cdbd 0x15cdbd) ((x',s')::t).
Proof. sa_tac posix_spawnattr_setpgroup_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_getschedparam_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_getschedparam_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cd8b, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cd8b 0x15cd90 0x15cd90 (fun _ _ _ => 38) (fun m _ _ => m) s m x y)
                (sa_exit 0x15cd90 0x15cd90) ((x',s')::t).
Proof. sa_tac posix_spawnattr_getschedparam_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_setschedparam_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_setschedparam_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cd91, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cd91 0x15cd96 0x15cd96 (fun _ _ _ => 38) (fun m _ _ => m) s m x y)
                (sa_exit 0x15cd96 0x15cd96) ((x',s')::t).
Proof. sa_tac posix_spawnattr_setschedparam_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_getschedpolicy_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_getschedpolicy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cd97, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cd97 0x15cd9c 0x15cd9c (fun _ _ _ => 38) (fun m _ _ => m) s m x y)
                (sa_exit 0x15cd9c 0x15cd9c) ((x',s')::t).
Proof. sa_tac posix_spawnattr_getschedpolicy_amd64.welltyped. all: conj_tac. Qed.

Theorem posix_spawnattr_setschedpolicy_correct:
  forall prog s t s' x' m x y (P: posix_spawnattr_setschedpolicy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15cd9d, s)) (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (sa_invs 0x15cd9d 0x15cda2 0x15cda2 (fun _ _ _ => 38) (fun m _ _ => m) s m x y)
                (sa_exit 0x15cda2 0x15cda2) ((x',s')::t).
Proof. sa_tac posix_spawnattr_setschedpolicy_amd64.welltyped. all: conj_tac. Qed.
