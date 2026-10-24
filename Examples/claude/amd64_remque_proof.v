(* remque -- remove an element from a doubly linked list

   SEMANTICS
   ---------
   remque(elem) unlinks elem from its doubly linked list.  With next = elem's
   forward pointer (offset 0) and prev = elem's backward pointer (offset 8),
   remque sets next->backward = prev when next is non-NULL, then
   prev->forward = next when prev is non-NULL.  elem itself is not modified.

   SPECIFICATION (man 3 remque, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <search.h>
            void remque(void *elem);

     DESCRIPTION
            The  insque()  and  remque()  functions manipulate doubly linked lists.
            Each element in the list is a structure of which the first two elements
            are  a  forward  and a backward pointer.  The linked list may be linear
            (i.e., NULL forward pointer at the end of the list  and  NULL  backward
            pointer at the start of the list) or circular.

            The  remque()  function  removes the element pointed to by elem from the
            doubly linked list.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol remque at 0x21d0c0 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see remque_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = elem (pointer); m = memory on entry.
   Output:  remque returns void.  On return, with next = m[elem] and
            prev = m[elem+8] (8-byte little-endian loads/stores), the memory is
            exactly
              m1 = if next = NULL then m else m[next+8 := prev]
              if prev = NULL then m1 else m1[prev := next].
            Nothing else in memory changes (remque_exact).  Corollary
            (remque_links): if next's backward field and prev's forward field
            don't overlap each other or elem's 16 bytes, then afterwards
            next->backward = prev, prev->forward = next, and elem's own two
            fields are unchanged.
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import remque_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import amd64_common.
Open Scope N.

Theorem remque_nwc: forall s2 s1, remque_amd64 s1 = remque_amd64 s2.
Proof. reflexivity. Qed.

Theorem remque_welltyped: welltyped_prog x64typctx remque_amd64.
Proof. Picinae_typecheck. Qed.

Theorem remque_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates remque_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET is at offset 28. *)
Definition remque_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 28 => true
  | _ => false
  end | _ => false end.

Definition remque_mem (m elem:N) :=
  let next := m Ⓠ[elem] in
  let prev := m Ⓠ[elem ⊕ 8] in
  let m1 := if next =? 0 then m else m [Ⓠ next ⊕ 8 := prev] in
  if prev =? 0 then m1 else m1 [Ⓠ prev := next].

Definition postcondition (m elem rsp:N) (s:store) :=
  s V_MEM64 = remque_mem m elem /\ s R_RSP = rsp.

Definition remque_invs (m elem rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s V_MEM64 = m /\ s R_RDI = elem /\ s R_RSP = rsp)
  | 28 => Some (postcondition m elem rsp s)
  | _ => None
  end | _ => None end.

Theorem remque_exact:
  forall s t s' x' m elem rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (ELEM: s R_RDI = elem) (RSP: s R_RSP = rsp),
  satisfies_all remque_amd64 (remque_invs m elem rsp) remque_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply remque_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [ELEM RSP]].
  repeat x64_step.
  all: split; [|assumption]; unfold remque_mem; cbv zeta;
       rewrite getmem_mod_l, (N.add_comm elem 8), BC, BC0; try rewrite setmem_mod_l;
       try rewrite (N.add_comm (m Ⓠ[elem]) 8); reflexivity.
Qed.

(* With no aliasing between the updated fields and elem, the neighbors are
   linked to each other and elem is left untouched. *)
Theorem remque_links:
  forall m elem,
  let next := m Ⓠ[elem] in
  let prev := m Ⓠ[elem ⊕ 8] in
  (next <> 0 -> ~ overlap 64 elem 16 (next ⊕ 8) 8) ->
  (prev <> 0 -> ~ overlap 64 elem 16 prev 8) ->
  (next <> 0 -> prev <> 0 -> ~ overlap 64 prev 8 (next ⊕ 8) 8) ->
  let m' := remque_mem m elem in
  (next <> 0 -> m' Ⓠ[next ⊕ 8] = prev) /\
  (prev <> 0 -> m' Ⓠ[prev] = next) /\
  m' Ⓠ[elem] = next /\ m' Ⓠ[elem ⊕ 8] = prev.
Proof.
  intros m elem next prev NO1 NO2 NO3 m'.
  assert (NL: next < 2^64) by apply getmem_bound.
  assert (PL: prev < 2^64) by apply getmem_bound.
  subst m'. unfold remque_mem. fold next prev.
  destruct (N.eqb_spec next 0) as [NZ|NZ]; destruct (N.eqb_spec prev 0) as [PZ|PZ].
    repeat split; intros; try contradiction; reflexivity.
    pose proof (noverlap16_lo _ _ _ (NO2 PZ)) as F1. pose proof (noverlap16_hi _ _ _ (NO2 PZ)) as F2.
      repeat split; intros; try contradiction; getmem_simpl;
      try apply N.mod_small; fold next prev; try assumption; reflexivity.
    pose proof (noverlap16_lo _ _ _ (NO1 NZ)) as F1. pose proof (noverlap16_hi _ _ _ (NO1 NZ)) as F2.
      repeat split; intros; try contradiction; getmem_simpl;
      try apply N.mod_small; fold next prev; try assumption; reflexivity.
    pose proof (noverlap16_lo _ _ _ (NO1 NZ)) as F1. pose proof (noverlap16_hi _ _ _ (NO1 NZ)) as F2.
      pose proof (noverlap16_lo _ _ _ (NO2 PZ)) as F3. pose proof (noverlap16_hi _ _ _ (NO2 PZ)) as F4.
      pose proof (NO3 NZ PZ) as F5.
      repeat split; intros; try contradiction; getmem_simpl;
      try apply N.mod_small; fold next prev; try assumption; reflexivity.
Qed.
