Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Import PIL32Notations.
Require Import p32_addloop.

Definition add_loop_start : N :=  0.
Definition add_loop_end   : N := 16.

Section Invariants.
  Variables inp1 inp2 : N.
  Variable  s0 : store.
  Hypothesis s_inp1 : s0 R_R1 = Ⓓ inp1.
  Hypothesis s_inp2 : s0 R_R2 = Ⓓ inp2. 
  
  Definition postcondition (s:store) := s R_R1 = Ⓓ(inp1 ⊕ inp2).
  Definition mem_unchanged (s:store) := s V_MEM32 = s0 V_MEM32.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ => match a with
      | 0 => Some (s R_R1 = Ⓓ inp1 /\ s R_R2 = Ⓓ inp2 /\ mem_unchanged s)
      | 1 => Some (exists r1 r2, s R_R1 = Ⓓr1 /\ s R_R2 = Ⓓr2
                                 /\ r1 ⊕ r2 = inp1 ⊕ inp2 /\ mem_unchanged s)
      | 16 => Some (postcondition s)
      | _ => None end
    | _ => None end.
End Invariants.

Definition addloop_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 16 => true
  | _ => false
  end | _ => false end.

Definition addloop : store -> addr -> N := fun _ => p32_addloop'.

(* Check forall_endstates.
Theorem addloop_preserves_memory:
  forall_endstates p32_prog (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed. *)

Theorem addloop_correctness:
  forall s inp1 inp2 t s' x'
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models pil32typctx s)
         (MEM: s V_MEM32 = Ⓜ p32_addloop')
         (INP1: s R_R1 = Ⓓinp1)
         (INP2: s R_R2 = Ⓓinp2)
,
(* We define our program as p32_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-15 with all other bytes 0.
*)
  satisfies_all p32_prog (invs inp1 inp2 s) addloop_exit ((x',s')::t).
Proof.
Local Ltac step := time pil32_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY. step. repeat (split; try assumption).

  (* Inductive cases *)
  intros.
  (* somehow `startof_prefix` is bound to the wrong theorem here... 
     In the strspn example the theorem is preferentially bound to
     Picinae.Picinae_armv8_pcode.Theory_arm8.startof_prefix
     rather than the alternative Picinae.Picinae_theory.startof_prefix.
     Here it is the opposite, so we must specify the arch-specific version*)
  eapply Picinae.Picinae_pilbox32.Theory_pil32.startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply welltyped_p32prog).
  clear - PRE MDL MEM. rename s into s0, t1 into t, s1 into s.
  
  (* TODO: continue here - destruct_inv is hanging, maybe using the new
  definitions in the funccall branch will fix it? *)
  unfold true_inv, get_precondition, p32_prog in PRE.
  simpl_inv PRE 0.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 32 PRE.
  destruct PRE as [MEM [BITMAP_0 [STR [ACPT [ACPT_0 BMP]]]]].
  step. step. step. step.



    