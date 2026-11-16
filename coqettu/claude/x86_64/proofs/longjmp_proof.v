(* longjmp -- nonlocal goto (musl x86_64 assembly)

   SEMANTICS
   ---------
   musl's longjmp (src/setjmp/x86_64/longjmp.s; also exported as _longjmp)
   computes the value the "fake" setjmp return will deliver with
       xor eax,eax ; cmp esi,1 ; adc eax,esi
   i.e. EAX = val + (val <u 1) = (val == 0 ? 1 : val) on the low 32 bits of
   val, then reloads RBX, RBP, R12-R15 and RSP from env[0..6] and jumps
   indirectly to env[7].  It writes no memory and never returns.

   SPECIFICATION (man 3 longjmp, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <setjmp.h>
            [[noreturn]] void longjmp(jmp_buf env, int val);

     DESCRIPTION
            The longjmp() function uses the information saved in env to
            transfer control back to the point where setjmp() was called and
            to restore ("rewind") the stack to its state at the time of the
            setjmp() call.  [...]
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
            longjmp = _longjmp at 0x5eec8 (Ghidra image base 0x100000: 0x15eec8)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/longjmp_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = env, ESI = val (an int, the low 32 bits of RSI); m = memory
            on entry, in which env holds the eight quadwords
            rbx, rbp, r12, r13, r14, r15, sp, pc (jmpbuf_holds).
   Output:  At the final indirect JMP (0x15eeea), which is longjmp's exit
            (the analogue of a RET-site postcondition): RBX, RBP, R12-R15 = rbx,
            rbp, r12-r15; RSP = sp; RAX = (val mod 2^32 = 0 ? 1 : val mod 2^32);
            memory is unchanged (= m); and the JMP's target, the quadword at
            RDI+0x38, is pc.  longjmp_jump_target shows that executing that
            JMP transfers control to pc with these registers.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.longjmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_jmpbuf.
Open Scope N.

Theorem longjmp_nwc: forall s2 s1, longjmp_amd64 s1 = longjmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem longjmp_welltyped: welltyped_prog x64typctx longjmp_amd64.
Proof. exact welltyped. Qed.

Theorem longjmp_preserves_memory:
  forall_endstates longjmp_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* The value delivered by the fake return of setjmp. *)
Definition longjmp_ret (val:N) :=
  if val mod 2^32 =? 0 then 1 else val mod 2^32.

Lemma longjmp_ret_nonzero: forall val, longjmp_ret val <> 0.
Proof. intros. unfold longjmp_ret. destruct (N.eqb_spec (val mod 2^32) 0); lia. Qed.

Definition longjmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x15eeea => true
  | _ => false end | _ => false end.

Definition longjmp_post (m env val rbx rbp r12 r13 r14 r15 sp pc:N) (s:store) :=
  s R_RBX = rbx /\ s R_RBP = rbp /\ s R_R12 = r12 /\ s R_R13 = r13 /\
  s R_R14 = r14 /\ s R_R15 = r15 /\ s R_RSP = sp /\ s R_RAX = longjmp_ret val /\
  s V_MEM64 = m /\ s R_RDI = env /\ m Ⓠ[56 + env] = pc.

Definition longjmp_invs (m env val rbx rbp r12 r13 r14 r15 sp pc:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x15eec8 => Some (s V_MEM64 = m /\ s R_RDI = env /\ s R_RSI = val /\
                      jmpbuf_holds m env rbx rbp r12 r13 r14 r15 sp pc)
  | 0x15eeea => Some (longjmp_post m env val rbx rbp r12 r13 r14 r15 sp pc s)
  | _ => None
  end | _ => None end.

Theorem longjmp_correct:
  forall prog s t s' x' m env val rbx rbp r12 r13 r14 r15 sp pc
         (LONGJMP: longjmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15eec8, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (ENV: s R_RDI = env) (VAL: s R_RSI = val)
         (JB: jmpbuf_holds m env rbx rbp r12 r13 r14 r15 sp pc),
  satisfies_all prog (longjmp_invs m env val rbx rbp r12 r13 r14 r15 sp pc)
                longjmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m env val rbx rbp r12 r13 r14 r15 sp pc LONGJMP ENTRY MDL MEM ENV VAL JB.
  eapply satisfies_all_pmono with (p1:=longjmp_amd64); [exact LONGJMP| |].
    intros a s1 t1 EXIT NOCODE. unfold longjmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m env val rbx rbp r12 r13 r14 r15 sp pc MDL MEM ENV VAL JB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. refine (conj _ (conj _ (conj _ _))); assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply longjmp_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [MEM [ENV [VAL JB]]].
  repeat x64_step.
  destruct JB as (B & P & A & C & D & E & SP & PC).
  unfold longjmp_post.
  rewrite B, P, A, C, D, E, SP, PC.
  repeat split; try reflexivity; try assumption.
  unfold longjmp_ret. rewrite <- VAL.
  destruct (N.ltb_spec (s1 R_RSI mod 2^32) 1) as [L|L].
  - replace (s1 R_RSI mod 2^32) with 0 by lia. cbn [N.eqb].
    rewrite <- N.add_mod_idemp_r by discriminate. replace (s1 R_RSI mod 2^32) with 0 by lia.
    reflexivity.
  - destruct (N.eqb_spec (s1 R_RSI mod 2^32) 0). lia.
    reflexivity.
Qed.

(* Executing the final JMP from the postcondition state transfers control to
   pc with every architectural register and the memory unchanged. *)
Theorem longjmp_jump_target:
  forall prog s x' s' m env val rbx rbp r12 r13 r14 r15 sp pc
         (LONGJMP: longjmp_amd64 ⊆2 prog)
         (POST: longjmp_post m env val rbx rbp r12 r13 r14 r15 sp pc s)
         (STEP: can_step prog ((x', s'), (Addr 0x15eeea, s))),
  x' = Addr pc /\
  s' R_RBX = rbx /\ s' R_RBP = rbp /\ s' R_R12 = r12 /\ s' R_R13 = r13 /\
  s' R_R14 = r14 /\ s' R_R15 = r15 /\ s' R_RSP = sp /\
  s' R_RAX = longjmp_ret val /\ s' V_MEM64 = m.
Proof.
  intros. inversion STEP as [a s0 sz q c' s'' x LU XS]; subst.
  rewrite (LONGJMP s 0x15eeea _ (eq_refl (longjmp_amd64 s 0x15eeea))) in LU. apply inj_prog_stmt in LU. destruct LU; subst sz q.
  destruct POST as (B & P & A & C & D & E & SP & RAX & MEM & ENV & PC).
  repeat (ISA_step_and_simplify XS).
  destruct XS as [XS XX]. subst x. try rewrite exitof_some.
  rewrite XS, PC. split. reflexivity.
  rewrite <- MEM, <- B, <- P, <- A, <- C, <- D, <- E, <- SP, <- RAX, <- ENV.
  repeat split; rewrite ?update_frame by discriminate; try reflexivity;
    rewrite update_updated; reflexivity.
Qed.
