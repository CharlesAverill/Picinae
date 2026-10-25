(* inet_makeaddr -- build an Internet address from network and host numbers

   SEMANTICS
   ---------
   inet_makeaddr(net, host) combines a classful network number with a local
   host number and returns the address in network byte order:
     net < 128:       class A, net.host24
     net < 65536:     class B, net.host16
     net < 2^24:      class C, net.host8
     otherwise:       net | host
   glibc shifts net into place, masks host to the class's host width, ORs,
   and byte-swaps the result (BSWAP).  It is the converse of inet_netof and
   inet_lnaof (amd64_inet_netof_proof.v, amd64_inet_lnaof_proof.v).

   SPECIFICATION (man 3 inet_makeaddr, Linux man-pages 5.10, Ubuntu 22.04)
   ------------------------------------------------------------------------

     struct in_addr inet_makeaddr(in_addr_t net, in_addr_t host);

     The inet_makeaddr() function is the converse of inet_netof() and
     inet_lnaof().  It returns an Internet host address in network byte
     order, created by combining the network number net with the local
     address host, both in host byte order.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol inet_makeaddr at 0x236660 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see inet_makeaddr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI = net, ESI = host (32-bit values).
   Output:  RAX = ntohl32 (makeaddr net host): the combined address,
            byte-swapped to network order, zero-extended.  RSP and memory are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import inet_makeaddr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem inet_makeaddr_nwc: forall s2 s1, inet_makeaddr_amd64 s1 = inet_makeaddr_amd64 s2.
Proof. reflexivity. Qed.

Theorem inet_makeaddr_welltyped: welltyped_prog x64typctx inet_makeaddr_amd64.
Proof. Picinae_typecheck. Qed.

Theorem inet_makeaddr_preserves_memory:
  forall_endstates inet_makeaddr_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem inet_makeaddr_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates inet_makeaddr_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The classful combination, in host byte order. *)
Definition makeaddr (net host:N) :=
  if net <? 128 then (net << 24 .| host mod 2^24) mod 2^32
  else if net <? 65536 then (net << 16 .| host mod 2^16) mod 2^32
  else if net <? 2^24 then (net << 8 .| host mod 2^8) mod 2^32
  else (net .| host) mod 2^32.

Definition inet_makeaddr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x236678 | 0x236692 | 0x2366af => true | _ => false end | _ => false end.

Definition inet_makeaddr_invs (net host rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x236660 => Some (s R_RDI mod 2^32 = net /\ s R_RSI mod 2^32 = host /\ s R_RSP = rsp)
  | 0x236678 | 0x236692 | 0x2366af => Some (s R_RAX = ntohl32 (makeaddr net host) /\ s R_RSP = rsp)
  | _ => None
  end | _ => None end.

(* The byte swap of the combined address, one byte lane at a time. *)
Lemma lor_mod32: forall a b, (a .| b) mod 2^32 = a mod 2^32 .| b mod 2^32.
Proof.
  intros. apply N.bits_inj. intro i. rewrite N.lor_spec.
  destruct (N.ltb_spec i 32).
  - rewrite !N.mod_pow2_bits_low by lia. apply N.lor_spec.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma shl24_mod: forall d r, d mod 2^8 = r mod 2^8 -> (d << 24) mod 2^32 = (r << 24) mod 2^32.
Proof.
  intros d r E. apply N.bits_inj. intro i.
  destruct (N.ltb_spec i 32).
  - rewrite !N.mod_pow2_bits_low by lia. destruct (N.ltb_spec i 24).
    + rewrite !N.shiftl_spec_low by lia. reflexivity.
    + rewrite !N.shiftl_spec_high by lia.
      rewrite <- (N.mod_pow2_bits_low d 8) by lia. rewrite <- (N.mod_pow2_bits_low r 8) by lia.
      rewrite E. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma bswap_bytes:
  forall a b c d r,
  a .& 4278190080 = r .& 4278190080 -> b .& 16711680 = r .& 16711680 ->
  c .& 65280 = r .& 65280 -> d mod 2^8 = r mod 2^8 ->
  ((a .& 4278190080) >> 24 .| (b .& 16711680) >> 8 .| (c .& 65280) << 8 .| d << 24) mod 2^32 =
  ntohl32 (r mod 2^32).
Proof.
  intros a b c d r A B C D. rewrite A, B, C.
  rewrite lor_mod32, (shl24_mod d r D), <- lor_mod32. apply bswap_ntohl.
Qed.

Lemma mbit: forall k i, N.testbit (N.ones 8 << k) i = (k <=? i) && (i <? k + 8).
Proof.
  intros k i. destruct (N.ltb_spec i k).
  - rewrite N.shiftl_spec_low by lia. destruct (N.leb_spec k i); [lia|reflexivity].
  - rewrite N.shiftl_spec_high by lia. destruct (N.leb_spec k i); [|lia].
    destruct (N.ltb_spec (i - k) 8).
    + rewrite N.ones_spec_low by lia. symmetry. apply N.ltb_lt. lia.
    + rewrite N.ones_spec_high by lia. symmetry. apply N.ltb_ge. lia.
Qed.

Ltac bytes_tac :=
  change 4278190080 with (N.ones 8 << 24) in *; change 16711680 with (N.ones 8 << 16) in *;
  change 65280 with (N.ones 8 << 8) in *;
  apply N.bits_inj; let i := fresh "i" in intro i;
  repeat first [ rewrite N.land_spec | rewrite N.lor_spec | rewrite mbit ];
  destruct (N.ltb_spec i 8); [|destruct (N.ltb_spec i 16); [|destruct (N.ltb_spec i 24); [|destruct (N.ltb_spec i 32)]]];
  repeat match goal with |- context [?a <=? ?b] => destruct (N.leb_spec a b); try lia
                       | |- context [?a <? ?b] => destruct (N.ltb_spec a b); try lia end;
  cbn [andb orb];
  repeat first [ rewrite N.shiftl_spec_low by lia | rewrite N.shiftl_spec_high by lia
               | rewrite N.mod_pow2_bits_low by lia | rewrite N.mod_pow2_bits_high by lia ];
  rewrite ?Bool.orb_false_l, ?Bool.orb_false_r; try reflexivity.

Ltac low8_tac :=
  apply N.bits_inj; let i := fresh "i" in intro i;
  destruct (N.ltb_spec i 8);
  [ rewrite !N.mod_pow2_bits_low by lia;
    repeat first [ rewrite N.lor_spec | rewrite N.shiftl_spec_low by lia | rewrite N.mod_pow2_bits_low by lia ];
    rewrite ?Bool.orb_false_l, ?Bool.orb_false_r; try reflexivity
  | rewrite !N.mod_pow2_bits_high by lia; reflexivity ].

Theorem inet_makeaddr_correct:
  forall s t s' x' net host rsp
         (ENTRY: startof t (x',s') = (Addr 0x236660, s))
         (MDL: models x64typctx s)
         (NET: s R_RDI mod 2^32 = net) (HOST: s R_RSI mod 2^32 = host) (RSP: s R_RSP = rsp),
  satisfies_all inet_makeaddr_amd64 (inet_makeaddr_invs net host rsp) inet_makeaddr_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply inet_makeaddr_welltyped. intro MDL1.
  clear - PRE MDL1. rename t1 into t.
  destruct_inv 64 PRE.
  destruct PRE as [NET [HOST RSP]].
  repeat x64_step.
  all: repeat match goal with
       | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
       | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
       | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
       end.
  all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                            | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end.
  all: repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                            | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.
  all: try discriminate.
  all: split; [|assumption].
  all: unfold makeaddr; subst net host.
  all: repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (N.ltb_spec a b) end.
  all: try (exfalso; lia).
  all: eapply bswap_bytes; [bytes_tac | bytes_tac | bytes_tac | low8_tac].
Qed.
