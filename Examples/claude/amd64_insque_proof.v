(* insque -- insert an element into a doubly linked list

   SEMANTICS
   ---------
   insque(elem, prev) splices elem into a doubly linked list right after prev.
   A list element starts with a forward pointer (offset 0) and a backward
   pointer (offset 8).  Let next be prev's old forward pointer.  insque sets
   prev->forward = elem, next->backward = elem (only if next is non-NULL),
   elem->forward = next and elem->backward = prev.  If prev is NULL, elem
   becomes a one-element linear list: both of its pointers are set to NULL.

   SPECIFICATION (man 3 insque, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <search.h>
            void insque(void *elem, void *prev);

     DESCRIPTION
            The  insque()  and  remque()  functions manipulate doubly linked lists.
            Each element in the list is a structure of which the first two elements
            are  a  forward  and a backward pointer.  The linked list may be linear
            (i.e., NULL forward pointer at the end of the list  and  NULL  backward
            pointer at the start of the list) or circular.

            The  insque()  function  inserts the element pointed to by elem immedi-
            ately after the element pointed to by prev.

            If the list is linear, then the call insque(elem, NULL) can be used  to
            insert  the  initial  list  element,  and the call sets the forward and
            backward pointers of elem to NULL.

            If the list is circular, the caller should ensure that the forward  and
            backward pointers of the first element are initialized to point to that
            element, and the prev argument of the insque() call should  also  point
            to the element.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol insque at 0x21d090 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see insque_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = elem, RSI = prev (pointers); m = memory on entry.
   Output:  insque returns void.  On return the memory is exactly
              if prev = NULL:  m[elem := 0][elem+8 := 0]
              otherwise, with next = m[prev] (8-byte little-endian loads/stores):
                m1 = m[prev := elem]
                m2 = if next = NULL then m1 else m1[next+8 := elem]
                m2[elem := next][elem+8 := prev].
            Nothing else in memory changes (insque_exact).  Corollary
            (insque_links): if elem's 16 bytes overlap neither prev's forward
            pointer nor next's backward pointer, the four links described above
            all hold after the call.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import insque_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem insque_nwc: forall s2 s1, insque_amd64 s1 = insque_amd64 s2.
Proof. reflexivity. Qed.

Theorem insque_welltyped: welltyped_prog x64typctx insque_amd64.
Proof. Picinae_typecheck. Qed.

Theorem insque_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates insque_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 33. *)
Definition insque_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 33 => true
  | _ => false
  end | _ => false end.

Definition insque_mem (m elem prev:N) :=
  if prev =? 0 then m [Ⓠ elem := 0] [Ⓠ elem ⊕ 8 := 0]
  else let next := m Ⓠ[prev] in
       let m1 := m [Ⓠ prev := elem] in
       let m2 := if next =? 0 then m1 else m1 [Ⓠ next ⊕ 8 := elem] in
       m2 [Ⓠ elem := next] [Ⓠ elem ⊕ 8 := prev].

Definition postcondition (m elem prev rsp:N) (s:store) :=
  s V_MEM64 = insque_mem m elem prev /\ s R_RSP = rsp.

Definition insque_invs (m elem prev rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = elem /\ s R_RSI = prev /\ s R_RSP = rsp)
  | 33 => Some (postcondition m elem prev rsp s)
  | _ => None
  end | _ => None end.

Theorem insque_exact:
  forall s t s' x' m elem prev rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (ELEM: s R_RDI = elem) (PREV: s R_RSI = prev)
         (RSP: s R_RSP = rsp),
  satisfies_all insque_amd64 (insque_invs m elem prev rsp) insque_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply insque_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [ELEM [PREV RSP]]].
  repeat x64_step.
  all: split; [|assumption]; unfold insque_mem; rewrite BC; try rewrite BC0;
       rewrite !setmem_mod_l, !(N.add_comm elem 8).
    apply N.eqb_eq in BC. rewrite BC. reflexivity.
    reflexivity.
    rewrite (N.add_comm (m Ⓠ[prev]) 8). reflexivity.
Qed.

(* With no aliasing between the updated fields, the four links of the
   man page hold. *)
Theorem insque_links:
  forall m elem prev, elem < 2^64 -> prev < 2^64 -> prev <> 0 ->
  let next := m Ⓠ[prev] in
  ~ overlap 64 elem 16 prev 8 ->
  (next <> 0 -> ~ overlap 64 elem 16 (next ⊕ 8) 8 /\ ~ overlap 64 prev 8 (next ⊕ 8) 8) ->
  let m' := insque_mem m elem prev in
  m' Ⓠ[elem] = next /\ m' Ⓠ[elem ⊕ 8] = prev /\ m' Ⓠ[prev] = elem /\
  (next <> 0 -> m' Ⓠ[next ⊕ 8] = elem).
Proof.
  intros m elem prev EL PL PNZ next NO1 NO2 m'.
  assert (NL: next < 2^64) by apply getmem_bound.
  assert (E8: ~ overlap 64 (elem ⊕ 8) 8 elem 8).
    intros [i [j [I [J EQ]]]]. rewrite mp2_add_l, <- N.add_assoc in EQ.
    change (2^64) with 18446744073709551616 in EQ. lia.
  subst m' next. unfold insque_mem. rewrite (proj2 (N.eqb_neq _ _) PNZ). cbv zeta.
  set (nx := m Ⓠ[prev]) in *.
  pose proof (noverlap16_lo _ _ _ NO1) as F1. pose proof (noverlap16_hi _ _ _ NO1) as F2.
  destruct (N.eqb_spec nx 0) as [NZ|NZ].
    getmem_simpl. rewrite !N.mod_small by assumption.
    repeat split; try reflexivity. intro. contradiction.
    destruct (NO2 NZ) as [NO3 F4].
    pose proof (noverlap16_lo _ _ _ NO3) as F5. pose proof (noverlap16_hi _ _ _ NO3) as F6.
    repeat split; [..|intros _]; getmem_simpl; apply N.mod_small; assumption.
Qed.
