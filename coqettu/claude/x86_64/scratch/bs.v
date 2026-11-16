Require Import Picinae_amd64.
Require Import CoqEtTu.programs.labs_amd64.
Require Import CoqEtTu.programs.llabs_amd64.
Require Import CoqEtTu.programs.imaxabs_amd64.
Require Import CoqEtTu.programs.htonl_amd64.
Require Import CoqEtTu.programs.htons_amd64.
Require Import CoqEtTu.programs.ntohl_amd64.
Require Import CoqEtTu.programs.ntohs_amd64.
Import X64Notations. From Stdlib Require Import NArith. Open Scope N.
Definition ex_labs (t:trace) := match t with (Addr a,_)::_ => match a with 0x00165009 => true | _ => false end | _ => false end.
Definition iv_labs (t:trace) := match t with (Addr a,s)::_ => match a with 0x00165009 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv labs_amd64 iv_labs ex_labs false ((Addr 0x00164fff, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "labs:" G end. Abort.
Definition ex_llabs (t:trace) := match t with (Addr a,_)::_ => match a with 0x0016501d => true | _ => false end | _ => false end.
Definition iv_llabs (t:trace) := match t with (Addr a,s)::_ => match a with 0x0016501d => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv llabs_amd64 iv_llabs ex_llabs false ((Addr 0x00165013, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "llabs:" G end. Abort.
Definition ex_imaxabs (t:trace) := match t with (Addr a,_)::_ => match a with 0x00164ff5 => true | _ => false end | _ => false end.
Definition iv_imaxabs (t:trace) := match t with (Addr a,s)::_ => match a with 0x00164ff5 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv imaxabs_amd64 iv_imaxabs ex_imaxabs false ((Addr 0x00164feb, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "imaxabs:" G end. Abort.
Definition ex_htonl (t:trace) := match t with (Addr a,_)::_ => match a with 0x00159deb => true | _ => false end | _ => false end.
Definition iv_htonl (t:trace) := match t with (Addr a,s)::_ => match a with 0x00159deb => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv htonl_amd64 iv_htonl ex_htonl false ((Addr 0x00159de7, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "htonl:" G end. Abort.
Definition ex_htons (t:trace) := match t with (Addr a,_)::_ => match a with 0x00159df2 => true | _ => false end | _ => false end.
Definition iv_htons (t:trace) := match t with (Addr a,s)::_ => match a with 0x00159df2 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv htons_amd64 iv_htons ex_htons false ((Addr 0x00159dec, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "htons:" G end. Abort.
Definition ex_ntohl (t:trace) := match t with (Addr a,_)::_ => match a with 0x0015af42 => true | _ => false end | _ => false end.
Definition iv_ntohl (t:trace) := match t with (Addr a,s)::_ => match a with 0x0015af42 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv ntohl_amd64 iv_ntohl ex_ntohl false ((Addr 0x0015af3e, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "ntohl:" G end. Abort.
Definition ex_ntohs (t:trace) := match t with (Addr a,_)::_ => match a with 0x0015af49 => true | _ => false end | _ => false end.
Definition iv_ntohs (t:trace) := match t with (Addr a,s)::_ => match a with 0x0015af49 => Some (s R_RAX = 0) | _ => None end | _ => None end.
Goal forall s1 t, nextinv ntohs_amd64 iv_ntohs ex_ntohs false ((Addr 0x0015af43, s1)::t). intros. repeat x64_step. all: match goal with |- ?G => idtac "ntohs:" G end. Abort.
