(* inet_netof (AArch64 / ARMv8) -- network number part of an IPv4 address.

   SEMANTICS
   ---------
   inet_netof returns the classful network-number part of an IPv4 address: the
   argument is byte-swapped to host order, then split per the address class
   (A: top byte, B: top two bytes, C/other: top three bytes).  Same spec
   (inet_net . ntohl32) as amd64_inet_netof_proof.v.

     `rev w0,w0; tbz w0,#31,L; and w3,w0,#0xc0000000; lsr w1,w0,#16;
      mov w2,#0x80000000; lsr w0,w0,#8; cmp w3,w2; csel w0,w0,w1,ne; ret
      L: lsr w0,w0,#24; ret`

   SPECIFICATION (man 3 inet_netof)
   --------------------------------
     in_addr_t inet_netof(struct in_addr in);
     The inet_netof() function returns the network number part of the Internet
     address in.

   PROVENANCE
   ----------
   Binary:  aarch64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15
            (sha256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06),
            symbol inet_netof at 0x1f9d90.  Lifter: Ghidra 11.4.2 + pcode2coq.
   Model:   Specification and proof written by Claude Opus 4.8 (claude-opus-4-8),
            an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT (AAPCS64)
   ----------------------
   Input:   W0 holds the in_addr (network byte order).
   Output:  X0 = inet_net (ntohl32 (W0)).  Memory is unchanged (leaf, via X30).
 *)

Require Import Picinae_armv8.
Require Import inet_netof_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Open Scope N.

Theorem inet_netof_nwc: forall s2 s1, inet_netof_arm8 s1 = inet_netof_arm8 s2.
Proof. reflexivity. Qed.
Theorem inet_netof_welltyped: welltyped_prog arm8typctx inet_netof_arm8.
Proof. Picinae_typecheck. Qed.
Theorem inet_netof_preserves_memory:
  forall_endstates inet_netof_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* The AArch64 `rev` expansion equals the host-order address. *)
Lemma rev_ntohl: forall x,
  (((x .& 4278255360) >> 8 .| (x .& 16711935) << 8) >> 16
   .| ((x .& 65280) >> 8 .| x << 8) << 16) mod 2^32 = ntohl32 (x mod 2^32).
Proof. intro x. unfold ntohl32. bitblast_upto 32. Qed.

(* A mask below 2^32 ignores bits that `mod 2^32` would clear. *)
Lemma land_mod32: forall y m, m < 2^32 -> (y mod 2^32) .& m = y .& m.
Proof.
  intros y m H. destruct (N.eq_dec m 0) as [->|NZ].
  { rewrite !N.land_0_r. reflexivity. }
  apply N.bits_inj. intro i. rewrite !N.land_spec.
  destruct (N.ltb_spec i 32) as [L|L].
  - rewrite N.mod_pow2_bits_low by exact L. reflexivity.
  - replace (N.testbit m i) with false.
    + rewrite !Bool.andb_false_r. reflexivity.
    + symmetry. apply N.bits_above_log2.
      apply N.lt_le_trans with 32; [| exact L].
      apply (proj1 (N.log2_lt_pow2 m 32 (proj1 (N.neq_0_lt_0 m) NZ)) H).
Qed.

Definition inet_netof_exit (t:trace) :=
  match t with (Addr 32,_)::_ => true | (Addr 40,_)::_ => true | _ => false end.

Definition postcondition (x:N) (s:store) := s R_X0 = inet_net (ntohl32 (x mod 2^32)).

Definition inet_netof_invs (x:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_X0 = x)
  | 32 | 40 => Some (postcondition x s)
  | _ => None
  end | _ => None end.

Theorem inet_netof_correct:
  forall s t s' x' x
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models arm8typctx s)
         (X: s R_X0 = x),
  satisfies_all inet_netof_arm8 (inet_netof_invs x) inet_netof_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply inet_netof_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.

  rename PRE into X.
  repeat arm8_step.
  all: rewrite shr31_mod2 in BC.
  all: unfold postcondition; rewrite <- rev_ntohl.
  all: unfold inet_net, is_classA, is_classB.
  all: rewrite land_bit31, ifb31_eqb0.
  all: rewrite (N.mod_pow2_bits_low _ 32 31 ltac:(lia)).
  all: rewrite (land_mod32 _ 3221225472 ltac:(vm_compute; reflexivity)).
  (* class A: BC says bit 31 clear (tbz jumped) *)
  - destruct (N.testbit _ 31); [ discriminate BC | reflexivity ].
  (* class B/C paths: bit 31 set, classB cmp decides *)
  - destruct (N.testbit _ 31); [| discriminate BC ].
    change (2^31) with 2147483648 in BC0. rewrite BC0. reflexivity.
  - destruct (N.testbit _ 31); [| discriminate BC ].
    change (2^31) with 2147483648 in BC0. rewrite BC0. reflexivity.
Qed.
