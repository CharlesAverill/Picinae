(* setjmp -- save the calling environment (musl x86_64 assembly)

   SEMANTICS
   ---------
   musl's setjmp (src/setjmp/x86_64/setjmp.s; also exported as _setjmp and
   __setjmp) stores the six callee-saved registers RBX, RBP, R12-R15 into
   env[0..5], the stack pointer the caller will have after setjmp returns
   (RSP+8) into env[6], and setjmp's own return address [RSP] into env[7]; it
   then returns 0.  It does not save the signal mask (POSIX leaves that
   unspecified for setjmp; sigsetjmp is the variant that can).

   SPECIFICATION (man 3 setjmp, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <setjmp.h>
            int setjmp(jmp_buf env);

     DESCRIPTION
            The setjmp() function saves various information about the calling
            environment (typically, the stack pointer, the instruction
            pointer, possibly the values of other registers and the signal
            mask) in the buffer env for later use by longjmp().  In this
            case, setjmp() returns 0.

     RETURN VALUE
            setjmp() and sigsetjmp() return 0 when called directly; on the
            "fake" return that occurs after longjmp() or siglongjmp(), the
            nonzero value specified in val is returned.

   The "fake return" half of this specification is the composition theorem
   in setjmp_longjmp_proof.v.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            setjmp = _setjmp = __setjmp at 0x5eeed (Ghidra image base 0x100000:
            0x15eeed)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/setjmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = env; RSP = rsp, where [rsp] holds the return address ra;
            m = memory on entry.  Precondition: the 64-byte env does not
            overlap the return-address slot [rsp, rsp+8) (otherwise setjmp
            would save a return address it had just overwritten).
   Output:  At the RET (0x15ef17): RAX = 0; RSP = rsp; RBX, RBP, R12-R15 are
            unchanged; and memory is exactly m with the eight quadwords
            RBX, RBP, R12, R13, R14, R15, rsp+8, ra written at env, env+8, ...,
            env+56 (jmpbuf_write).  Corollaries: env then holds those values
            (setjmp_saves), and no byte outside [env, env+64) changed.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.setjmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_jmpbuf.
Open Scope N.

Theorem setjmp_nwc: forall s2 s1, setjmp_amd64 s1 = setjmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem setjmp_welltyped: welltyped_prog x64typctx setjmp_amd64.
Proof. exact welltyped. Qed.

Definition setjmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x15ef17 => true
  | _ => false end | _ => false end.

Definition setjmp_post (s0:store) (m env:N) (s:store) :=
  s R_RAX = 0 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\
  s V_MEM64 = jmpbuf_write m env (s0 R_RBX) (s0 R_RBP) (s0 R_R12) (s0 R_R13)
                (s0 R_R14) (s0 R_R15) (8 + s0 R_RSP) (m Ⓠ[s0 R_RSP]).

Definition setjmp_invs (s0:store) (m env:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15eeed => Some (s V_MEM64 = m /\ s R_RDI = env /\ s R_RSP = s0 R_RSP /\
                      callee_saved_eq s0 s)
  | 0x15ef17 => Some (setjmp_post s0 m env s)
  | _ => None
  end | _ => None end.

Theorem setjmp_correct:
  forall prog s t s' x' m env
         (SETJMP: setjmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15eeed, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (ENV: s R_RDI = env)
         (NOV: ~ overlap 64 (s R_RSP) 8 env 64),
  satisfies_all prog (setjmp_invs s m env) setjmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m env SETJMP ENTRY MDL MEM ENV NOV.
  eapply satisfies_all_pmono with (p1:=setjmp_amd64); [exact SETJMP| |].
    intros a s1 t1 EXIT NOCODE. unfold setjmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m env MDL MEM ENV NOV START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; try assumption; apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply setjmp_welltyped. intro MDL1.
  clear - PRE MDL1 NOV. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [ENV [RSP CS]]].
  repeat x64_step.
  split. reflexivity. split. reflexivity. split. callee_saved_tac.
  destruct CS as (B & P & A & C & D & E).
  rewrite <- RSP, B, P, A, C, D, E.
  rewrite <- RSP in NOV.
  set (rsp := s1 R_RSP) in *. clearbody rsp.
  unfold jmpbuf_write. f_equal.
  repeat (rewrite getmem_noverlap;
    [|intros [x [y [X [Y E']]]]; apply NOV;
      lazymatch type of E' with
      | _ = (?k + env + y) mod _ => exists x, (k + y); repeat split; [assumption|lia|rewrite E'; f_equal; lia]
      | _ = (env + y) mod _ => exists x, y; repeat split; [assumption|lia|assumption]
      end]).
  reflexivity.
Qed.

(* After setjmp, env holds the saved environment, and every other byte of
   memory is as it was on entry. *)
Theorem setjmp_saves:
  forall s0 m env s, models x64typctx s0 -> setjmp_post s0 m env s ->
  jmpbuf_holds (s V_MEM64) env (s0 R_RBX) (s0 R_RBP) (s0 R_R12) (s0 R_R13)
               (s0 R_R14) (s0 R_R15) (s0 R_RSP ⊕ 8) (m Ⓠ[s0 R_RSP]) /\
  (forall a, 64 <= msub 64 a env -> (s V_MEM64) Ⓑ[a] = m Ⓑ[a]).
Proof.
  intros s0 m env s MDL (_ & _ & _ & MEM). rewrite MEM. split.
  - rewrite (N.add_comm 8 (s0 R_RSP)), <- jmpbuf_write_sp_mod.
    apply jmpbuf_write_holds;
      try (apply (MDL _ 64); reflexivity); try apply N.mod_lt; try discriminate;
      apply getmem_bound.
  - intros. apply jmpbuf_write_frame. assumption.
Qed.

(* Executing setjmp's RET from the postcondition state returns to ra = m[rsp]
   with RSP = rsp + 8, RAX = 0 and the callee-saved registers of the caller. *)
Theorem setjmp_ret_target:
  forall prog s0 m env s x' s'
         (SETJMP: setjmp_amd64 ⊆2 prog)
         (NOV: ~ overlap 64 (s0 R_RSP) 8 env 64)
         (POST: setjmp_post s0 m env s)
         (STEP: can_step prog ((x', s'), (Addr 0x15ef17, s))),
  x' = Addr (m Ⓠ[s0 R_RSP]) /\ s' R_RSP = s0 R_RSP ⊕ 8 /\ s' R_RAX = 0 /\
  callee_saved_eq s0 s' /\ s' V_MEM64 = s V_MEM64.
Proof.
  intros. inversion STEP as [a s1 sz q c' s'' x LU XS]; subst.
  rewrite (SETJMP s 0x15ef17 _ (eq_refl (setjmp_amd64 s 0x15ef17))) in LU.
  apply inj_prog_stmt in LU. destruct LU; subst sz q.
  destruct POST as (RAX & RSP & CS & MEM).
  repeat (ISA_step_and_simplify XS).
  destruct XS as [XS XX]. subst x. rewrite XS.
  rewrite jmpbuf_write_read_frame by exact NOV. rewrite exitof_some.
  split. reflexivity.
  split. rewrite update_updated. rewrite N.add_comm. reflexivity.
  split. rewrite !update_frame by discriminate. exact RAX.
  split.
    destruct CS as (B & P & A & C & D & E).
    repeat split; rewrite ?update_frame by discriminate; assumption.
    rewrite !update_frame by discriminate. rewrite update_updated. symmetry. exact MEM.
Qed.
