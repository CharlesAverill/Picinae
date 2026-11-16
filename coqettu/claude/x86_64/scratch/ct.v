Require Import Picinae_amd64.
Require Import CoqEtTu.programs.isalpha_amd64.
Require Import CoqEtTu.programs.isdigit_amd64.
Require Import CoqEtTu.programs.isalnum_amd64.
Require Import CoqEtTu.programs.isupper_amd64.
Require Import CoqEtTu.programs.islower_amd64.
Require Import CoqEtTu.programs.isspace_amd64.
Require Import CoqEtTu.programs.isxdigit_amd64.
Require Import CoqEtTu.programs.isprint_amd64.
Require Import CoqEtTu.programs.isgraph_amd64.
Require Import CoqEtTu.programs.iscntrl_amd64.
Require Import CoqEtTu.programs.isblank_amd64.
Require Import CoqEtTu.programs.toupper_amd64.
Require Import CoqEtTu.programs.tolower_amd64.
Require Import CoqEtTu.programs.isascii_amd64.
Require Import CoqEtTu.programs.toascii_amd64.
Import X64Notations. From Stdlib Require Import NArith. Open Scope N.
Definition ex_isalpha (t:trace) := match t with (Addr a,_)::_ => match a with 0x001415bc => true | _ => false end | _ => false end.
Definition iv_isalpha (t:trace) := match t with (Addr a,s)::_ => match a with 0x001415bc => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isalpha_amd64 iv_isalpha ex_isalpha false ((Addr 0x1415ae, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isalpha:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isdigit (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141604 => true | _ => false end | _ => false end.
Definition iv_isdigit (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141604 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isdigit_amd64 iv_isdigit ex_isdigit false ((Addr 0x1415f9, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isdigit:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isalnum (t:trace) := match t with (Addr a,_)::_ => match a with 0x001415a8 => true | _ => false end | _ => false end.
Definition iv_isalnum (t:trace) := match t with (Addr a,s)::_ => match a with 0x001415a8 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isalnum_amd64 iv_isalnum ex_isalnum false ((Addr 0x141589, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isalnum:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isupper (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141688 => true | _ => false end | _ => false end.
Definition iv_isupper (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141688 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isupper_amd64 iv_isupper ex_isupper false ((Addr 0x14167d, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isupper:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_islower (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141626 => true | _ => false end | _ => false end.
Definition iv_islower (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141626 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv islower_amd64 iv_islower ex_islower false ((Addr 0x14161b, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "islower:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isspace (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141677 => true | _ => false end | _ => false end.
Definition iv_isspace (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141677 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isspace_amd64 iv_isspace ex_isspace false ((Addr 0x141663, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isspace:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isxdigit (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141918 => true | _ => false end | _ => false end.
Definition iv_isxdigit (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141918 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isxdigit_amd64 iv_isxdigit ex_isxdigit false ((Addr 0x1418fd, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isxdigit:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isprint (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141637 => true | _ => false end | _ => false end.
Definition iv_isprint (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141637 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isprint_amd64 iv_isprint ex_isprint false ((Addr 0x14162c, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isprint:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isgraph (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141615 => true | _ => false end | _ => false end.
Definition iv_isgraph (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141615 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isgraph_amd64 iv_isgraph ex_isgraph false ((Addr 0x14160a, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isgraph:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_iscntrl (t:trace) := match t with (Addr a,_)::_ => match a with 0x001415f3 => true | _ => false end | _ => false end.
Definition iv_iscntrl (t:trace) := match t with (Addr a,s)::_ => match a with 0x001415f3 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv iscntrl_amd64 iv_iscntrl ex_iscntrl false ((Addr 0x1415e2, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "iscntrl:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isblank (t:trace) := match t with (Addr a,_)::_ => match a with 0x001415dc => true | _ => false end | _ => false end.
Definition iv_isblank (t:trace) := match t with (Addr a,s)::_ => match a with 0x001415dc => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isblank_amd64 iv_isblank ex_isblank false ((Addr 0x1415cb, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isblank:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_toupper (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141946 => true | _ => false end | _ => false end.
Definition iv_toupper (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141946 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv toupper_amd64 iv_toupper ex_toupper false ((Addr 0x141938, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "toupper:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_tolower (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141932 => true | _ => false end | _ => false end.
Definition iv_tolower (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141932 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv tolower_amd64 iv_tolower ex_tolower false ((Addr 0x141924, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "tolower:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_isascii (t:trace) := match t with (Addr a,_)::_ => match a with 0x001415ca => true | _ => false end | _ => false end.
Definition iv_isascii (t:trace) := match t with (Addr a,s)::_ => match a with 0x001415ca => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv isascii_amd64 iv_isascii ex_isascii false ((Addr 0x1415c2, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "isascii:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
Definition ex_toascii (t:trace) := match t with (Addr a,_)::_ => match a with 0x00141923 => true | _ => false end | _ => false end.
Definition iv_toascii (t:trace) := match t with (Addr a,s)::_ => match a with 0x00141923 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv toascii_amd64 iv_toascii ex_toascii false ((Addr 0x14191e, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "toascii:" G end. all: (repeat match goal with H: ?T |- _ => lazymatch T with context [list] => fail | context [store] => fail | _ => idtac "H:" H T; clear H end end). Abort.
