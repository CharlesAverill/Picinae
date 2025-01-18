Require Import NArith.
Require Import ZArith.
Require Import Picinae_pilbox32_interpreter.
Import PIL32Notations.
Require Import p32_dynamicli.

Definition dynamic_li_start : N :=  0.
Definition dynamic_li_end   : N := 16.

Section Invariants.
  Variables inp1 inp2 : N.
  Variable  s0 : store.
  
  Definition postcondition (s:store) := s R_R5 = Ⓓ(777).
  Definition mem_unchanged (s:store) := s V_MEM32 = s0 V_MEM32 /\ s A_EXEC = s0 A_EXEC.
  Definition invs (t:trace) : option Prop:=
    match t with (Addr a, s) :: _ => match a with
      | 0 => Some (mem_unchanged s)
      | 16 => Some (postcondition s)
      | _ => None end
    | _ => None end.
End Invariants.

Definition dynamicli_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 16 => true
  | _ => false
  end | _ => false end.

Definition exec_bits : addr -> N :=
  fun a => match a with
  | 0 | 4 | 8 | 12 => 1
  | _ => 0 end.

Theorem dynamicli_correctness:
  forall s t s' x'
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models pil32typctx s)
         (MEM: s V_MEM32 = Ⓜ p32_dynamicli')
         (EXEC: s A_EXEC = Ⓜ exec_bits)
,
(* We define our program as p32_prog, a function that looks into
   a given store's memory and page-execute permissions to determine
   what the next instruction is.
   Above we specified that the memory of the initial store is exactly
   our program, which is held in bytes 0-12 with all other bytes 0.
*)
  satisfies_all p32_prog (invs s) dynamicli_exit ((x',s')::t).
Proof.
Local Ltac step := time pil32_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY.
  step. repeat (split; try assumption).

  (* Inductive cases *)
  intros.
  (* somehow `startof_prefix` is bound to the wrong theorem here... 
     In the strspn example the theorem is preferentially bound to
     Picinae.Picinae_armv8_pcode.Theory_arm8.startof_prefix
     rather than the alternative Picinae.Picinae_theory.startof_prefix.
     Here it is the opposite, so we must specify the arch-specific version*)
  eapply Picinae.Picinae_pilbox32.Theory_pil32.startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply welltyped_p32prog).
  clear - PRE MDL MEM EXEC. rename s into s0, t1 into t, s1 into s.

  destruct_inv 32 PRE.
  destruct PRE as [MEMSAME EXECSAME].
  step.
  step.
  step.
  (* Notice our address, 12, is exactly the location where we stored a 
     value, 12443, in memory. 12433 corresponds exactly to`PIL_li r5 777,`
     the instruction for loading the immediate 777 into register 5.
  *)
  step.
  reflexivity.
Qed.