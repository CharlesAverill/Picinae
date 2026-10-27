(* Concrete chunk predicates for the add_n_sub_n wrapper.  The machine index
   advances by 170 even when the last committed chunk is shorter. *)
Require Import Picinae_amd64.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_specs.
Require Import Picinae.Examples.libgmp_so_10_5_0.amd64_gmp_call_support.
From Stdlib Require Import NArith Lia.
Import X64Notations GMPArrays.
Open Scope N.

Definition wrapper_sum (r : store) := r R_RDI.
Definition wrapper_diff (r : store) := r R_RSI.
Definition wrapper_u (r : store) := r R_RDX.
Definition wrapper_v (r : store) := r R_RCX.
Definition wrapper_n (r : store) := r R_R8.
Definition wrapper_frame (r : store) := r R_RSP-0x5a8.
Definition wrapper_stack (r : store) := r R_RSP-0x5b0.
Definition chunk_size n k := N.min 170 (n-k).
Definition chunk_end n k := k+chunk_size n k.
Definition limb_ptr p k := (p+8*k) mod 2^64.
Definition array_separate p q n := ~overlap 64 p (8*n) q (8*n).
Definition exact_or_separate p q n := p=q \/ array_separate p q n.

(* __gmpn_add_n_sub_n precondition *)
Definition wrapper_pre (r : store) :=
  models x64typctx r /\ wrapper_n r+170<2^63 /\ 8*wrapper_n r<=2^64 /\
  0x5b0<=r R_RSP /\
  array_separate (wrapper_sum r) (wrapper_diff r) (wrapper_n r) /\
  (forall d, d=wrapper_sum r \/ d=wrapper_diff r ->
    forall p, p=wrapper_u r \/ p=wrapper_v r ->
      exact_or_separate d p (wrapper_n r)) /\
  (forall p, p=wrapper_sum r \/ p=wrapper_diff r \/
             p=wrapper_u r \/ p=wrapper_v r ->
    p+8*wrapper_n r<=2^64 /\
    ~overlap 64 p (8*wrapper_n r) (wrapper_stack r) 0x5b0).

(* Reads outside both outputs and the complete stack footprint are unchanged.
   The footprint includes CALL's cell at F-8, and excludes the caller's RET. *)
Definition wrapper_memory_frame (r : store) m :=
  forall p len,
    ~overlap 64 p len (wrapper_sum r) (8*wrapper_n r) ->
    ~overlap 64 p len (wrapper_diff r) (8*wrapper_n r) ->
    ~overlap 64 p len (wrapper_stack r) 0x5b0 ->
    getmem 64 LittleE len m p=getmem 64 LittleE len (r V_MEM64) p.

Definition wrapper_saved (r : store) m :=
  m Ⓠ[wrapper_frame r+0x578]=r R_RBX /\
  m Ⓠ[wrapper_frame r+0x580]=r R_RBP /\
  m Ⓠ[wrapper_frame r+0x588]=r R_R12 /\
  m Ⓠ[wrapper_frame r+0x590]=r R_R13 /\
  m Ⓠ[wrapper_frame r+0x598]=r R_R14 /\
  m Ⓠ[wrapper_frame r+0x5a0]=r R_R15.
Definition wrapper_common (r s : store) :=
  s R_RSP=wrapper_frame r /\ s R_R12=wrapper_n r /\
  wrapper_saved r (s V_MEM64) /\ wrapper_memory_frame r (s V_MEM64).
Definition wrapper_results (r : store) m ks kd cy borrow :=
  cy<=1 /\ borrow<=1 /\
  nc_equation false (value m (wrapper_sum r) ks)
    (value (r V_MEM64) (wrapper_u r) ks)
    (value (r V_MEM64) (wrapper_v r) ks) 0 cy ks /\
  nc_equation true (value m (wrapper_diff r) kd)
    (value (r V_MEM64) (wrapper_u r) kd)
    (value (r V_MEM64) (wrapper_v r) kd) 0 borrow kd.
Definition wrapper_unread (r : store) m k :=
  unread (r V_MEM64) m (wrapper_u r) (wrapper_v r) (wrapper_n r) k.
Definition wrapper_scratch_sum (r : store) m k q cy :=
  cy<=1 /\
  nc_equation false
    (value m (wrapper_sum r) k+radix k*value m (wrapper_frame r+0x20) q)
    (value (r V_MEM64) (wrapper_u r) (k+q))
    (value (r V_MEM64) (wrapper_v r) (k+q)) 0 cy (k+q).

Inductive wrapper_route := AdditionFirst | SubtractionFirst | Scratch.
Definition wrapper_route_ok route (r : store) :=
  match route with
  | AdditionFirst => array_separate (wrapper_sum r) (wrapper_u r) (wrapper_n r) /\
                     array_separate (wrapper_sum r) (wrapper_v r) (wrapper_n r)
  | SubtractionFirst => (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r) /\
                        array_separate (wrapper_diff r) (wrapper_u r) (wrapper_n r) /\
                        array_separate (wrapper_diff r) (wrapper_v r) (wrapper_n r)
  | Scratch => (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r) /\
               (wrapper_diff r=wrapper_u r \/ wrapper_diff r=wrapper_v r)
  end.
Definition wrapper_loop_regs route (r s : store) k :=
  s R_RBX=limb_ptr (wrapper_u r) k /\ s R_RBP=limb_ptr (wrapper_v r) k /\
  match route with
  | AdditionFirst => s R_R14=k /\ s R_R13=limb_ptr (wrapper_sum r) k /\
                     s R_R15=limb_ptr (wrapper_diff r) k
  | SubtractionFirst => s R_R13=k /\ s R_R14=limb_ptr (wrapper_diff r) k /\
                        s R_R15=limb_ptr (wrapper_sum r) k
  | Scratch => s R_R13=k /\ s R_R14=limb_ptr (wrapper_diff r) k /\
      (s V_MEM64) Ⓠ[wrapper_frame r+0x10]=limb_ptr (wrapper_sum r) k /\
      (s V_MEM64) Ⓠ[wrapper_frame r+0x18]=wrapper_frame r+0x20
  end.
Definition wrapper_loop route (r s : store) :=
  exists k, k<wrapper_n r /\ k mod 170=0 /\
    wrapper_common r s /\ wrapper_route_ok route r /\ wrapper_loop_regs route r s k /\
    wrapper_unread r (s V_MEM64) k /\
    wrapper_results r (s V_MEM64) k k
      ((s V_MEM64) Ⓠ[wrapper_frame r+(if match route with SubtractionFirst => true | _ => false end then 8 else 0)])
      ((s V_MEM64) Ⓠ[wrapper_frame r+(if match route with SubtractionFirst => true | _ => false end then 0 else 8)]).

(* First result returned; the second operation still needs the current inputs.
   In the scratch route the sum remains buffered until the copy returns. *)
Definition wrapper_first_return route (r s : store) :=
  exists k, k<wrapper_n r /\ k mod 170=0 /\ wrapper_common r s /\
    wrapper_route_ok route r /\ wrapper_unread r (s V_MEM64) k /\
    s R_RBX=limb_ptr (wrapper_u r) k /\ s R_RBP=limb_ptr (wrapper_v r) k /\
    match route with
    | AdditionFirst => s R_R14=k+170 /\
        s R_R13=limb_ptr (wrapper_sum r) (k+170) /\ s R_R15=limb_ptr (wrapper_diff r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x10]=chunk_size (wrapper_n r) k /\
        wrapper_results r (s V_MEM64) (chunk_end (wrapper_n r) k) k
          (s R_RAX) ((s V_MEM64) Ⓠ[wrapper_frame r+8])
    | SubtractionFirst => s R_R13=k+170 /\
        s R_R14=limb_ptr (wrapper_diff r) (k+170) /\ s R_R15=limb_ptr (wrapper_sum r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x10]=chunk_size (wrapper_n r) k /\
        wrapper_results r (s V_MEM64) k (chunk_end (wrapper_n r) k)
          ((s V_MEM64) Ⓠ[wrapper_frame r+8]) (s R_RAX)
    | Scratch => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) k /\
        s R_R15=chunk_size (wrapper_n r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x10]=limb_ptr (wrapper_sum r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x18]=wrapper_frame r+0x20 /\
        wrapper_results r (s V_MEM64) k k
          ((s V_MEM64) Ⓠ[wrapper_frame r]) ((s V_MEM64) Ⓠ[wrapper_frame r+8]) /\
        wrapper_scratch_sum r (s V_MEM64) k (chunk_size (wrapper_n r) k) (s R_RAX)
    end.

Definition wrapper_second_return route (r s : store) :=
  exists k, k<wrapper_n r /\ k mod 170=0 /\ wrapper_common r s /\
    wrapper_route_ok route r /\ wrapper_unread r (s V_MEM64) (chunk_end (wrapper_n r) k) /\
    s R_RBX=limb_ptr (wrapper_u r) (k+170) /\ s R_RBP=limb_ptr (wrapper_v r) (k+170) /\
    match route with
    | AdditionFirst => s R_R14=k+170 /\
        s R_R13=limb_ptr (wrapper_sum r) (k+170) /\ s R_R15=limb_ptr (wrapper_diff r) (k+170) /\
        wrapper_results r (s V_MEM64) (chunk_end (wrapper_n r) k) (chunk_end (wrapper_n r) k)
          ((s V_MEM64) Ⓠ[wrapper_frame r]) (s R_RAX)
    | SubtractionFirst => s R_R13=k+170 /\
        s R_R14=limb_ptr (wrapper_diff r) (k+170) /\ s R_R15=limb_ptr (wrapper_sum r) (k+170) /\
        wrapper_results r (s V_MEM64) (chunk_end (wrapper_n r) k) (chunk_end (wrapper_n r) k)
          (s R_RAX) ((s V_MEM64) Ⓠ[wrapper_frame r])
    | Scratch => s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
        s R_R15=chunk_size (wrapper_n r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x10]=limb_ptr (wrapper_sum r) k /\
        (s V_MEM64) Ⓠ[wrapper_frame r+0x18]=wrapper_frame r+0x20 /\
        (s R_RAX<=1 /\ nc_equation true
          (value (s V_MEM64) (wrapper_diff r) (chunk_end (wrapper_n r) k))
          (value (r V_MEM64) (wrapper_u r) (chunk_end (wrapper_n r) k))
          (value (r V_MEM64) (wrapper_v r) (chunk_end (wrapper_n r) k)) 0 (s R_RAX)
          (chunk_end (wrapper_n r) k)) /\
        wrapper_scratch_sum r (s V_MEM64) k (chunk_size (wrapper_n r) k)
          ((s V_MEM64) Ⓠ[wrapper_frame r])
    end.

Definition wrapper_copy_return (r s : store) :=
  exists k, k<wrapper_n r /\ k mod 170=0 /\ wrapper_common r s /\ wrapper_route_ok Scratch r /\
    s R_R13=k+170 /\ s R_R14=limb_ptr (wrapper_diff r) (k+170) /\
    s R_RBX=limb_ptr (wrapper_u r) (k+170) /\ s R_RBP=limb_ptr (wrapper_v r) (k+170) /\
    s R_R15=limb_ptr (wrapper_sum r) k /\
    (s V_MEM64) Ⓠ[wrapper_frame r+0x18]=wrapper_frame r+0x20 /\
    wrapper_unread r (s V_MEM64) (chunk_end (wrapper_n r) k) /\
    wrapper_results r (s V_MEM64) (chunk_end (wrapper_n r) k) (chunk_end (wrapper_n r) k)
      ((s V_MEM64) Ⓠ[wrapper_frame r]) ((s V_MEM64) Ⓠ[wrapper_frame r+8]).

Definition wrapper_dispatch (r s : store) :=
  wrapper_common r s /\ wrapper_unread r (s V_MEM64) 0 /\
  s R_R13=wrapper_sum r /\ s R_R14=wrapper_diff r /\
  s R_RBX=wrapper_u r /\ s R_RBP=wrapper_v r.
Definition wrapper_epilogue (r s : store) :=
  s R_RSP=wrapper_frame r /\ wrapper_saved r (s V_MEM64) /\
  wrapper_memory_frame r (s V_MEM64) /\
  add_n_sub_n_post (r V_MEM64) (wrapper_sum r) (wrapper_diff r)
    (wrapper_u r) (wrapper_v r) (wrapper_n r) s.
(* __gmpn_add_n_sub_n postcondition *)
Definition wrapper_post (r s : store) :=
  add_n_sub_n_post (r V_MEM64) (wrapper_sum r) (wrapper_diff r)
    (wrapper_u r) (wrapper_v r) (wrapper_n r) s /\
  leaf_abi r s /\ wrapper_memory_frame r (s V_MEM64).

Definition wrapper_property (r s : store) (a : addr) : Prop :=
  wrapper_pre r /\
  match a with
  (* __gmpn_add_n_sub_n precondition *)
  | 0x15c360 => s=r
  | 0x15c448 => wrapper_dispatch r s /\ (wrapper_sum r=wrapper_u r \/ wrapper_sum r=wrapper_v r)
  | 0x15c508 => wrapper_dispatch r s /\ wrapper_route_ok Scratch r
  | 0x15c3b8 => wrapper_loop AdditionFirst r s
  | 0x15c480 => wrapper_loop SubtractionFirst r s
  | 0x15c538 => wrapper_loop Scratch r s
  | 0x15c3ef => wrapper_first_return AdditionFirst r s
  | 0x15c4b7 => wrapper_first_return SubtractionFirst r s
  | 0x15c568 => wrapper_first_return Scratch r s
  | 0x15c420 => wrapper_second_return AdditionFirst r s
  | 0x15c4e8 => wrapper_second_return SubtractionFirst r s
  | 0x15c597 => wrapper_second_return Scratch r s
  | 0x15c5b1 => wrapper_copy_return r s
  | 0x15c432 => wrapper_epilogue r s
  (* __gmpn_add_n_sub_n postcondition *)
  | 0x15c443 => wrapper_post r s
  | _ => False
  end.
