Require Import Picinae_armv7.
Require Import NArith.
Open Scope N.
Open Scope stmt_scope.

Definition cleanByVA : program := fun _ a => match a with

(* 0xc0000034: ldr r0, [sp] *)
| 0 => Some (4,
    Move R_R0 (Load (Var V_MEM32) (Var R_SP) LittleE 4)
  )

(* 0xc0000038: mcr p15, #0x0, r0, c7, c10, #0x1 *)
| 4 => Some (4,
    Nop (* Special: unsupported: MCR *)
  )

(* 0xc000003c: mcr p15, #0x0, r0, c7, c10, #0x1 *)
| 8 => Some (4,
    Nop (* Special: unsupported: MCR *)
  )

(* 0xc0000040: dmb sy *)
| 12 => Some (4,
    Nop
  )

| _ => None
end.

Theorem cleanByVA_proof :
  forall s m n w,
  s V_MEM32 = VaM m w
  -> s R_SP = VaN n w
  -> (forall x, x < 4 -> mem_readable s (n + x))
  -> exists s', exec_prog (fun _ => Some tt) cleanByVA 0 s 4 s' (Exit 16)
                /\ forall v, v <> R_R0 -> s v = s' v.
  intros.
  eexists.
  split; [|intros;rewrite update_frame;[reflexivity|eassumption]].
  econstructor; [reflexivity|constructor|reflexivity|repeat econstructor].
  econstructor; [rewrite <- H|rewrite <- H0|intuition]; econstructor.
Qed.
