(* setjmp + longjmp -- "execution continues as if setjmp() had returned for
   a second time" (musl x86_64)

   SEMANTICS
   ---------
   This file composes the separately proved contracts of setjmp
   (setjmp_proof.v) and longjmp (longjmp_proof.v).  If setjmp ran from entry
   state s0 with return address ra = m[rsp] and wrote env, and later longjmp
   is called on env, with any memory m2 in which the 64 bytes of env are
   still the ones setjmp wrote, then longjmp's final JMP goes to ra with RSP,
   RBX, RBP, R12-R15 exactly as setjmp's own RET leaves them, and with RAX
   the nonzero value val ? val : 1 instead of 0.

   SPECIFICATION (man 3 setjmp, Linux man-pages 6.9.1)
   ---------------------------------------------------
            Following a successful longjmp(), execution continues as if
            setjmp() had returned for a second time.  This "fake" return can
            be distinguished from a true setjmp() call because the "fake"
            return returns the value provided in val.  If the programmer
            mistakenly passes the value 0 in val, the "fake" return will
            instead return 1.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            setjmp at 0x5eeed, longjmp at 0x5eec8 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/setjmp_amd64.v, longjmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   s0 = state on entry to setjmp (RDI = env, RSP = rsp, m = memory,
            env disjoint from [rsp, rsp+8)); s1 = state at setjmp's RET.
            Later, longjmp is entered with RDI = env, ESI = val and memory m2
            that agrees with s1's memory on [env, env+64).
   Output:  (setjmp_longjmp_correct) longjmp satisfies its contract with the
            jmp_buf values setjmp saved.  (setjmp_returns_twice) the state
            after longjmp's JMP and the state after setjmp's RET have the same
            control target ra, the same RSP = rsp + 8 and the same RBX, RBP,
            R12-R15; RAX is 0 after the real return and val ? val : 1 (never
            0) after the fake one.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.setjmp_amd64 CoqEtTu.programs.longjmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_jmpbuf.
Require Import CoqEtTu.proofs.setjmp_proof CoqEtTu.proofs.longjmp_proof.
Open Scope N.

(* The jmp_buf contents written by a setjmp entered in state s0 with memory m. *)
Definition saved_invs (s0:store) (m m2 env val:N) :=
  longjmp_invs m2 env val (s0 R_RBX) (s0 R_RBP) (s0 R_R12) (s0 R_R13)
               (s0 R_R14) (s0 R_R15) (s0 R_RSP ⊕ 8) (m Ⓠ[s0 R_RSP]).

Theorem setjmp_longjmp_correct:
  forall s0 m env s1 prog s t s' x' m2 val
         (MDL0: models x64typctx s0) (SJ: setjmp_post s0 m env s1)
         (LONGJMP: longjmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15eec8, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m2) (ENV: s R_RDI = env) (VAL: s R_RSI = val)
         (KEEP: forall a, msub 64 a env < 64 -> m2 Ⓑ[a] = (s1 V_MEM64) Ⓑ[a]),
  satisfies_all prog (saved_invs s0 m m2 env val) longjmp_exit ((x',s')::t).
Proof.
  intros. unfold saved_invs. eapply longjmp_correct; try eassumption.
  eapply jmpbuf_holds_frame. exact KEEP.
  apply (setjmp_saves s0 m env s1 MDL0 SJ).
Qed.

(* The fake return looks exactly like the real one, except for RAX. *)
Theorem setjmp_returns_twice:
  forall prog s0 m env s1 x1 s1' m2 val s2 x2 s2'
         (SETJMP: setjmp_amd64 ⊆2 prog) (LONGJMP: longjmp_amd64 ⊆2 prog)
         (NOV: ~ overlap 64 (s0 R_RSP) 8 env 64)
         (SJ: setjmp_post s0 m env s1)
         (RET: can_step prog ((x1, s1'), (Addr 0x15ef17, s1)))
         (LJ: longjmp_post m2 env val (s0 R_RBX) (s0 R_RBP) (s0 R_R12) (s0 R_R13)
                (s0 R_R14) (s0 R_R15) (s0 R_RSP ⊕ 8) (m Ⓠ[s0 R_RSP]) s2)
         (JMP: can_step prog ((x2, s2'), (Addr 0x15eeea, s2))),
  x2 = x1 /\ s2' R_RSP = s1' R_RSP /\
  callee_saved_eq s1' s2' /\
  s1' R_RAX = 0 /\ s2' R_RAX = longjmp_ret val /\ s2' R_RAX <> 0.
Proof.
  intros.
  destruct (setjmp_ret_target prog s0 m env s1 x1 s1' SETJMP NOV SJ RET)
    as (X1 & SP1 & RAX1 & CS1 & _).
  destruct (longjmp_jump_target prog s2 x2 s2' m2 env val _ _ _ _ _ _ _ _ LONGJMP LJ JMP)
    as (X2 & B & P & A & C & D & E & SP2 & RAX2 & _).
  destruct CS1 as (B1 & P1 & A1 & C1 & D1 & E1).
  subst x1 x2. split. reflexivity. split. congruence.
  split. unfold callee_saved_eq. repeat split; congruence.
  split. exact RAX1. split. exact RAX2. rewrite RAX2. apply longjmp_ret_nonzero.
Qed.
