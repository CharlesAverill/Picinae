Require Import Picinae_amd64.
Require Import CoqEtTu.programs.setjmp_amd64 CoqEtTu.programs.longjmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.

Definition sj_exit (t:trace) := match t with (Addr a,_)::_ => match a with 0x15ef17 => true | _ => false end | _ => false end.
Definition sj_invs (s0:store) (t:trace) := match t with (Addr a,s)::_ => match a with
  | 0x15eeed => Some (s = s0)
  | 0x15ef17 => Some (s V_MEM64 = 0 /\ s R_RAX = 0 /\ s R_RSP = 0)
  | _ => None end | _ => None end.
Goal forall s0 s1 t, s1 = s0 ->
  nextinv setjmp_amd64 (sj_invs s0) sj_exit false ((Addr 0x15eeed, s1)::t).
intros. subst s1. repeat x64_step. match goal with |- ?G => idtac "SJ:" G end. Abort.

Definition lj_exit (t:trace) := match t with (Addr a,_)::_ => match a with 0x15eeea => true | _ => false end | _ => false end.
Definition lj_invs (s0:store) (t:trace) := match t with (Addr a,s)::_ => match a with
  | 0x15eec8 => Some (s = s0)
  | 0x15eeea => Some (s V_MEM64 = 0 /\ s R_RAX = 0 /\ s R_RSP = 0 /\ s R_RBX = 0 /\ s R_R15 = 0)
  | _ => None end | _ => None end.
Goal forall s0 s1 t, s1 = s0 ->
  nextinv longjmp_amd64 (lj_invs s0) lj_exit false ((Addr 0x15eec8, s1)::t).
intros. subst s1. repeat x64_step. match goal with |- ?G => idtac "LJ:" G end. Abort.
