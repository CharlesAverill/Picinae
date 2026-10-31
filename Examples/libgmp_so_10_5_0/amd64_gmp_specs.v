(* Mathematical specifications and proof cut points shared by the GMP lifts.
   All numeric arrays are little-endian sequences of 64-bit limbs. *)
Require Import Picinae_amd64.
From Stdlib Require Import NArith Lia.
Import X64Notations.
Open Scope N.

Module GMPArrayParams <: LimbArrayParams.
  Definition w := 64.
  Definition bytes := 8.
  Global Transparent w bytes.
End GMPArrayParams.
Module GMPArrays := LimbArrays GMPArrayParams.
Import GMPArrays.

Definition nc_equation (sub : bool) (result a b cin cout k : N) :=
  if sub then result+b+cin = a+radix k*cout
         else result+radix k*cout = a+b+cin.
Definition nc_post sub m0 d u v n cin (s : store) :=
  s R_RAX <= 1 /\
  nc_equation sub (value (s V_MEM64) d n)
    (value m0 u n) (value m0 v n) cin (s R_RAX) n.
(* __gmpn_add_nc postcondition *)
Definition add_nc_post := nc_post false.
(* __gmpn_sub_nc postcondition *)
Definition sub_nc_post := nc_post true.
(* __gmpn_add_n_sub_n postcondition *)
Definition add_n_sub_n_post m0 sum diff u v n (s : store) :=
  exists cy borrow,
    cy <= 1 /\ borrow <= 1 /\ s R_RAX = 2*cy+borrow /\
    nc_equation false (value (s V_MEM64) sum n)
      (value m0 u n) (value m0 v n) 0 cy n /\
    nc_equation true (value (s V_MEM64) diff n)
      (value m0 u n) (value m0 v n) 0 borrow n.

(* The prefix may be buffered in registers before it is stored.  [done] is
   the number of committed limbs, [pending] the number of computed limbs. *)
Definition buffered (s : store) pending :=
  match pending with
  | 0 => 0
  | 1 => s R_R8
  | 2 => cbits (s R_R9) 64 (s R_R8)
  | 3 => cbits (s R_R10) 128 (cbits (s R_R9) 64 (s R_R8))
  | _ => cbits (s R_R11) 192 (cbits (s R_R10) 128 (cbits (s R_R9) 64 (s R_R8)))
  end.
Definition nc_prefix sub m0 d u v cin done pending (s : store) :=
  s R_CF <= 1 /\ pending <= 4 /\
  nc_equation sub (value (s V_MEM64) d done + radix done * buffered s pending)
    (value m0 u (done+pending)) (value m0 v (done+pending)) cin
    (s R_CF) (done+pending).
Definition unread m0 m u v n k :=
  value m (u+8*k) (n-k) = value m0 (u+8*k) (n-k) /\
  value m (v+8*k) (n-k) = value m0 (v+8*k) (n-k).
Definition nc_ptrs d u v k si (s : store) :=
  s R_RDI = (d+8*k) mod 2^64 /\
  s R_RSI = (u+8*si) mod 2^64 /\
  s R_RDX = (v+8*k) mod 2^64.
Definition preloaded m0 u k count (s : store) :=
  (1 <= count -> s R_R8 = value m0 (u+8*k) 1) /\
  (2 <= count -> s R_R9 = value m0 (u+8*(k+1)) 1) /\
  (3 <= count -> s R_R10 = value m0 (u+8*(k+2)) 1) /\
  (4 <= count -> s R_R11 = value m0 (u+8*(k+3)) 1).

(* Address normalization lets the addition and subtraction lifts share the
   invariant map; subtraction is exactly 0x260 bytes above addition. *)
Definition nc_invset_core (sub : bool) m0 d u v n cin (t : trace) :=
  match t with (Addr pc,s)::_ =>
  let a := if sub then pc-0x260 else pc in
  match a with
  (* __gmpn_add_nc precondition *)
  (* __gmpn_sub_nc precondition *)
  | 0x1284e0 => Some (s V_MEM64=m0 /\ s R_RDI=d /\ s R_RSI=u /\ s R_RDX=v /\ s R_RCX=n /\ s R_R8=cin)
  (* __gmpn_add_n precondition *)
  (* __gmpn_sub_n precondition *)
  | 0x128500 => Some (s V_MEM64=m0 /\ s R_RDI=d /\ s R_RSI=u /\ s R_RDX=v /\ s R_RCX=n /\ cin=0)
  | 0x128517 => Some (exists k,
      k<n /\ n-k<=3 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 0 s /\ s R_RAX=n-k)
  | 0x128527 => Some (exists k,
      k+2<=n /\ n-k<=3 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 0 s /\ s R_RAX=n-k-1 /\ preloaded m0 u k 1 s)
  | 0x128532 => Some (exists k,
      n=k+2 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 1 s /\ s R_RAX=0 /\ s R_R9=value m0 (u+8*(k+1)) 1)
  | 0x128540 => Some (exists k,
      n=k+3 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 0 s /\ s R_RAX=1 /\ preloaded m0 u k 2 s)
  | 0x12854b => Some (exists k,
      n=k+3 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 2 s /\ s R_RAX=1 /\ s R_R10=value m0 (u+8*(k+2)) 1)
  | 0x128594 => Some (exists k,
      k+4<=n /\ k mod 4=0 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 0 s /\ s R_RAX=n mod 4 /\
      s R_RCX=(n-k)/4-1 /\ s R_ZF=(if s R_RCX =? 0 then 1 else 0) /\ preloaded m0 u k 2 s)
  | 0x128560 | 0x128567 | 0x12856f => Some (exists k,
      k+8<=n /\ k mod 4=0 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k (if a =? 0x128560 then 0 else if a =? 0x128567 then 2 else 4) s /\
      s R_RAX=n mod 4 /\ s R_RCX=(n-k)/4-1 /\
      (a=0x128560 -> preloaded m0 u k 4 s) /\
      (a=0x128567 -> s R_R10=value m0 (u+8*(k+2)) 1 /\ s R_R11=value m0 (u+8*(k+3)) 1))
  | 0x12859e | 0x1285a9 | 0x1285b1 => Some (exists k,
      k+4<=n /\ n-k<8 /\ k mod 4=0 /\
      nc_ptrs d u v k (if a =? 0x12859e then k else k+4) s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k (if a =? 0x12859e then 0 else if a =? 0x1285a9 then 2 else 4) s /\
      s R_RAX=n mod 4 /\ s R_RCX=0 /\
      (a=0x12859e -> preloaded m0 u k 4 s) /\
      (a=0x1285a9 -> s R_R10=value m0 (u+8*(k+2)) 1 /\ s R_R11=value m0 (u+8*(k+3)) 1))
  | 0x1285ca => Some (exists k,
      k<=n /\ n-k<4 /\ k mod 4=0 /\ nc_ptrs d u v k k s /\ unread m0 (s V_MEM64) u v n k /\
      nc_prefix sub m0 d u v cin k 0 s /\ s R_RAX=n-k+1)
  (* __gmpn_add_nc postcondition *)
  (* __gmpn_sub_nc postcondition *)
  (* __gmpn_add_n postcondition *)
  (* __gmpn_sub_n postcondition *)
  | 0x128526 | 0x12853f | 0x12855d | 0x1285d4 => Some (nc_post sub m0 d u v n cin s)
  | _ => None end | _ => None end.

Definition nc_cf_post sub m0 d u v n cin (s : store) :=
  s R_CF<=1 /\ nc_equation sub (value (s V_MEM64) d n)
    (value m0 u n) (value m0 v n) cin (s R_CF) n.
Definition nc_stage sub m0 d u v n cin k pending si (s : store) :=
  k<=n /\ nc_ptrs d u v k si s /\ unread m0 (s V_MEM64) u v n k /\
  nc_prefix sub m0 d u v cin k pending s.
Definition remaining_inputs m0 u k pending count (s : store) :=
  forall i, pending<=i -> i<count ->
  (match i with 0 => s R_R8 | 1 => s R_R9 | 2 => s R_R10 | _ => s R_R11 end)
    = value m0 (u+8*(k+i)) 1.

(* Additional cuts around individual ADC/SBB instructions keep kernel checking
   linear in the carry chain length. Their equations describe the same prefix. *)
Definition nc_aux_invset (sub : bool) m0 d u v n cin (t : trace) :=
  match t with (Addr pc,s)::_ =>
  let a := if sub then pc-0x260 else pc in
  match a with
  | 0x12851e | 0x128521 => Some (exists k,
      n=k+1 /\ nc_stage sub m0 d u v n cin k (if a=?0x12851e then 0 else 1) k s /\
      s R_RAX=0 /\ (a=0x12851e -> preloaded m0 u k 1 s))
  | 0x128524 | 0x12853d | 0x1285d2 => Some (nc_cf_post sub m0 d u v n cin s /\ s R_RAX=0)
  | 0x12855a => Some (nc_cf_post sub m0 d u v n cin s /\ s R_RAX=1)
  | 0x12852f | 0x128536 => Some (exists k,
      n=k+2 /\ nc_stage sub m0 d u v n cin k (if a=?0x12852f then 0 else 2) k s /\
      s R_RAX=0 /\ (a=0x12852f -> preloaded m0 u k 2 s))
  | 0x128544 | 0x128547 | 0x12854f => Some (exists k,
      n=k+3 /\ nc_stage sub m0 d u v n cin k
        (if a=?0x128544 then 0 else if a=?0x128547 then 1 else 3) k s /\
      s R_RAX=1 /\ remaining_inputs m0 u k
        (if a=?0x128544 then 0 else if a=?0x128547 then 1 else 3) 3 s)
  | 0x128563 | 0x12856b => Some (exists k,
      k+8<=n /\ k mod 4=0 /\ nc_stage sub m0 d u v n cin k (if a=?0x128563 then 1 else 3) k s /\
      s R_RAX=n mod 4 /\ s R_RCX=(n-k)/4-1 /\
      remaining_inputs m0 u k (if a=?0x128563 then 1 else 3) 4 s)
  | 0x1285a2 | 0x1285a5 | 0x1285ad => Some (exists k,
      k+4<=n /\ n-k<8 /\ k mod 4=0 /\
      nc_stage sub m0 d u v n cin k
        (if a=?0x1285a2 then 0 else if a=?0x1285a5 then 1 else 3) (k+4) s /\
      s R_RAX=n mod 4 /\ s R_RCX=0 /\
      remaining_inputs m0 u k
        (if a=?0x1285a2 then 0 else if a=?0x1285a5 then 1 else 3) 4 s)
  | _ => None end | _ => None end.

Definition nc_invset sub m0 d u v n cin t :=
  match nc_aux_invset sub m0 d u v n cin t with
  | Some P => Some P | None => nc_invset_core sub m0 d u v n cin t end.

Lemma add_nc_post_equation : forall m0 d u v n cin s,
  add_nc_post m0 d u v n cin s ->
  value (s V_MEM64) d n + radix n*s R_RAX = value m0 u n + value m0 v n+cin.
Proof. intros; exact (proj2 H). Qed.
Lemma sub_nc_post_equation : forall m0 d u v n cin s,
  sub_nc_post m0 d u v n cin s ->
  value (s V_MEM64) d n + value m0 v n+cin = value m0 u n + radix n*s R_RAX.
Proof. intros; exact (proj2 H). Qed.
