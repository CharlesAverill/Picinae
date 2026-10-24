(* inet_lnaof -- local (host) part of an IPv4 address

   SEMANTICS
   ---------
   inet_lnaof returns the network number part of an IPv4 address,
   using the classful rules quoted below.
   Let a = ntohl(in.s_addr), the address in host byte order.  glibc
   classifies a as class A (top bit 0), class B (top bits 10), or anything
   else; it treats everything else like class C, which includes the class D/E
   ranges that the man page does not discuss.  The definitions ntohl32,
   is_classA, is_classB, inet_net and inet_lna in amd64_common.v state this.

   SPECIFICATION (man 3 inet_netof, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <sys/socket.h>
            #include <netinet/in.h>
            #include <arpa/inet.h>
            in_addr_t inet_lnaof(struct in_addr in);
            in_addr_t inet_netof(struct in_addr in);

     DESCRIPTION
            The inet_lnaof() function returns the local network address part of the
            Internet address in.  The returned value is in host byte order.

            The inet_netof() function returns the network number part of the Inter-
            net address in.  The returned value is in host byte order.

     NOTES
            inet_lnaof(),  inet_netof(),  and  inet_makeaddr() are legacy functions
            that assume they are dealing with classful network addresses.  Classful
            networking  divides IPv4 network addresses into host and network compo-
            nents at byte boundaries, as follows:

            Class A   This address type is indicated by the value  0  in  the  most
                      significant  bit  of the (network byte ordered) address.  The
                      network address is contained in the  most  significant  byte,
                      and the host address occupies the remaining three bytes.

            Class B   This  address type is indicated by the binary value 10 in the
                      most significant two bits of the address.   The  network  ad-
                      dress is contained in the two most significant bytes, and the
                      host address occupies the remaining two bytes.

            Class C   This address type is indicated by the binary value 110 in the
                      most  significant three bits of the address.  The network ad-
                      dress is contained in the three most significant  bytes,  and
                      the host address occupies the remaining byte.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol inet_lnaof at 0x236630 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see inet_lnaof_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   EDI = in.s_addr (struct in_addr passed by value, network byte order).
   Output:  On return, RAX = inet_lna (ntohl32 (EDI)), the in_addr_t result in host
            byte order (zero-extended).
   Frame:   RSP is unchanged at the RET, so control returns to the caller's
            return address.  Memory is not modified.  No callee-saved register
            (RBX, RBP, R12-R15) is modified.
 *)

Require Import Picinae_amd64.
Require Import inet_lnaof_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Import ListNotations.
Open Scope N.

Theorem inet_lnaof_nwc: forall s2 s1, inet_lnaof_amd64 s1 = inet_lnaof_amd64 s2.
Proof. reflexivity. Qed.

Theorem inet_lnaof_welltyped: welltyped_prog x64typctx inet_lnaof_amd64.
Proof. Picinae_typecheck. Qed.

Theorem inet_lnaof_preserves_memory:
  forall_endstates inet_lnaof_amd64 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem inet_lnaof_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates inet_lnaof_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* The RET instructions are at offsets 34 and 47. *)
Definition inet_lnaof_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 34 | 47 => true
  | _ => false
  end | _ => false end.

Definition postcondition (h rsp:N) (s:store) :=
  s R_RAX = inet_lna h /\ s R_RSP = rsp.

Definition inet_lnaof_invs (x h rsp:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0 => Some (s R_RDI mod 2^32 = x /\ s R_RSP = rsp)
  | 6 => Some (s R_RDI = h /\ s R_RSP = rsp)
  | 10 => Some (s R_RDI = h /\ N.testbit h 31 = true /\ s R_RSP = rsp)
  | 40 => Some (s R_RDI = h /\ N.testbit h 31 = false /\ s R_RSP = rsp)
  | 25 => Some (N.testbit h 31 = true /\ s R_RDI = h .& 255 /\ s R_RAX = h .& 65535 /\
                s R_RDX = h .& 0xc0000000 /\ s R_RSP = rsp)
  | 31 => Some (N.testbit h 31 = true /\ s R_RDI = h .& 255 /\ s R_RAX = h .& 65535 /\
                s R_ZF = (if h .& 0xc0000000 =? 0x80000000 then 1 else 0) /\ s R_RSP = rsp)
  | 34 | 47 => Some (postcondition h rsp s)
  | _ => None
  end | _ => None end.

Theorem inet_lnaof_correct:
  forall s t s' x' x h rsp
         (ENTRY: startof t (x',s') = (Addr 0,s))
         (MDL: models x64typctx s)
         (X: s R_RDI mod 2^32 = x) (A: h = ntohl32 x) (RSP: s R_RSP = rsp),
  satisfies_all inet_lnaof_amd64 (inet_lnaof_invs x h rsp) inet_lnaof_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply inet_lnaof_welltyped. intro MDL1.
  assert (NL: h < 2^32) by (rewrite A; apply ntohl32_lt).
  clear - PRE MDL1 A NL. rename t1 into t.
  destruct_inv 64 PRE.

  - (* BSWAP *)
    destruct PRE as [X RSP]. x64_step. x64_step. split; [|assumption].
    rewrite bswap_ntohl, X, A. reflexivity.
  - (* sign test *)
    destruct PRE as [RA RSP].
    repeat x64_step.
    all: rewrite N.shiftr_0_r, N.mod_small, N.land_diag, slt32_0 in BC by exact NL.
    all: repeat split; assumption.
  - (* class B or C (or D/E): compute the candidates *)
    destruct PRE as [RA [B31 RSP]].
    repeat x64_step.
    all: repeat split; try assumption.
    all: rewrite ?N.shiftr_0_r, ?N.mod_small by exact NL.
    all: first [ sreflexivity | rewrite <- N.land_ones; f_equal; reflexivity |
                 rewrite <- (N.mod_small h (2^32)) by exact NL; bitblast_upto 32 ].
  - (* class B or C (or D/E): compare with 0x80000000 *)
    destruct PRE as [B31 [RDI [RAX [RDX RSP]]]].
    repeat x64_step.
    repeat split; try assumption.
    all: first [rewrite RDI | rewrite RAX]; rewrite <- N.land_ones; f_equal; reflexivity.
  - (* class B or C (or D/E): select *)
    destruct PRE as [B31 [RDI [RAX [ZF RSP]]]].
    repeat x64_step.
    all: split; [|assumption].
    all: unfold inet_lna, is_classA, is_classB; rewrite land_bit31, ifb31_eqb0, B31; cbn [negb].
    all: try (change (2^31) with 2147483648 in BC; rewrite BC).
    all: first [ sreflexivity | rewrite <- N.land_ones; f_equal; reflexivity ].
  - (* class A *)
    destruct PRE as [RA [B31 RSP]].
    repeat x64_step.
    split; [|assumption].
    unfold inet_lna, is_classA, is_classB; rewrite land_bit31, ifb31_eqb0, B31; cbn [negb].
    rewrite ?(N.mod_small h) by exact NL.
    rewrite <- N.land_ones; f_equal; reflexivity.
Qed.

(* The network and host parts recombine to the address. *)
Theorem inet_net_lna_recombine:
  forall a, a < 2^32 ->
  (if is_classA a then (inet_net a << 24) .| inet_lna a
   else if is_classB a then (inet_net a << 16) .| inet_lna a
   else (inet_net a << 8) .| inet_lna a) = a.
Proof.
  intros a LT. unfold inet_net, inet_lna.
  rewrite <- (N.mod_small a (2^32)) by exact LT.
  destruct (is_classA (a mod 2^32)), (is_classB (a mod 2^32)); bitblast_upto 32.
Qed.
