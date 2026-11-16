Require Import Picinae_amd64.
Require Import CoqEtTu.programs.strlen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.
Definition ex (t:trace) := match t with (Addr a,_)::_ => match a with 0x13492c => true | _ => false end | _ => false end.
Definition iv (t:trace) := match t with (Addr a,s)::_ => match a with
  | 0x134904 => Some (s R_RAX = 0)
  | 0x134924 => Some (s R_RAX = 1)
  | 0x13492c => Some (s R_RAX = 2)
  | _ => None end | _ => None end.
Goal forall s1 t, nextinv strlen_amd64 iv ex false ((Addr 0x134904, s1)::t).
intros. repeat x64_step. all: match goal with |- ?G => idtac "G:" G end.
all: (repeat match goal with H: ?T |- _ => idtac "H:" H T; clear H end). Abort.
