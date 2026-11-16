Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcslen_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import CoqEtTu.lib.x64_abi.
Open Scope N.
Definition ex (t:trace) := match t with (Addr a,_)::_ => match a with 0x13c3a1 => true | _ => false end | _ => false end.
Definition iv p (t:trace) := match t with (Addr a,s)::_ => match a with
  | 0x13c394 => Some (exists k, s R_RAX = p ⊕ 4*k /\ s R_RDI = p)
  | 0x13c3a1 => Some (s R_RAX = 2)
  | _ => None end | _ => None end.
Goal forall p s1 t k, s1 R_RAX = p ⊕ 4*k -> s1 R_RDI = p -> nextinv wcslen_amd64 (iv p) ex false ((Addr 0x13c394, s1)::t).
intros. repeat x64_step. all: bc_norm. all: match goal with |- ?G => idtac "G:" G end.
all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
