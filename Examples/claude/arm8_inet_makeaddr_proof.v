(* PARTIAL handoff: the single full target build failed at inet_bfm24_correct.
   Only the preceding nine facts reached Qed; no full proof .vo was produced.
   Every unchecked proof below is Aborted, with its statement unchanged. *)

(* inet_makeaddr (AAPCS64, little-endian AArch64).

   SYNOPSIS: struct in_addr inet_makeaddr(in_addr_t net, in_addr_t host).
   English specification: combine unsigned 32-bit network and host numbers.
   net < 128: net<<24 | low24(host); otherwise net < 65536:
   net<<16 | low16(host); otherwise net < 16777216: net<<8 | low8(host);
   otherwise net|host. Reverse the four bytes to return network-order s_addr.

   Provenance: official Ubuntu ARM64 glibc 2.35-0ubuntu3.15,
   /lib/aarch64-linux-gnu/libc.so.6, SHA256
   79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   ELF entry 0xf9d40, Ghidra image base 0x100000, IL entry 0x1f9d40.
   Ghidra 11.4.2 raw SLEIGH pcode, e11/e29 explicit scalar replacement;
   unchanged complete 19-instruction e29_inet_makeaddr_arm8 map, 76 bytes.
   See lifter/scalar_bitforms/e29_inet_makeaddr_arm8.manifest.json.
   The AMD64 proof is a specification/style reference only, never an import.
   Initial statement/proof author: OpenAI gpt-6-astra, xhigh/priority.
   Validation and final-producer status are recorded in notes/a-inet-makeaddr/.

   ABI: low32(X0)=net, low32(X1)=host. Upper halves are unrestricted within
   the modeled 64-bit register types. At each of the three RET sites X0 is
   the zero-extended 32-bit result. Memory, SP, X30, modeled X19-X29 and
   modeled Z8-Z15 are preserved. RET encodings name X30 as the target.
   The intended invariant theorem specifies entry-to-RET partial correctness of
   this exact IL map for every input pair, including boundaries and high bits.
   No buffer-size, overlap, memory-content/accessibility, callee, global,
   CPU-feature, tunable, or result-oracle premise is imposed. The only state
   premise is ordinary Picinae typing. No termination, verified binary/lifter
   refinement, hardware fault, cache, timing, or concurrency claim is made.
 *)

Require Import Picinae_armv8.
Require Import e29_inet_makeaddr_arm8.
Require Import arm8_common.
Import ARM8Notations.
From Stdlib Require Import NArith Lia List.
Import ListNotations.
Open Scope N.

Definition makeaddr (net host:N) :=
  if net <? 128 then (net << 24 .| host mod 2^24) mod 2^32
  else if net <? 65536 then (net << 16 .| host mod 2^16) mod 2^32
  else if net <? 16777216 then (net << 8 .| host mod 2^8) mod 2^32
  else (net .| host) mod 2^32.

Definition inet_makeaddr_result (net host:N) := ntohl32 (makeaddr net host).

Definition inet_makeaddr_postcondition (net host m sp lr:N) (s:store) :=
  s R_X0 = inet_makeaddr_result net host /\
  s V_MEM64 = m /\ s R_SP = sp /\ s R_X30 = lr.

Definition inet_makeaddr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1f9d50 | 0x1f9d68 | 0x1f9d88 => true
  | _ => false end | _ => false end.

Definition inet_makeaddr_invs (net host m sp lr:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x1f9d40 => Some (s R_X0 mod 2^32 = net /\ s R_X1 mod 2^32 = host /\
                      s V_MEM64 = m /\ s R_SP = sp /\ s R_X30 = lr)
  | 0x1f9d50 | 0x1f9d68 | 0x1f9d88 =>
      Some (inet_makeaddr_postcondition net host m sp lr s)
  | _ => None end | _ => None end.

Theorem inet_makeaddr_nwc:
  forall s2 s1, e29_inet_makeaddr_arm8 s1 = e29_inet_makeaddr_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions inet_makeaddr_nwc.

Theorem inet_makeaddr_welltyped:
  welltyped_prog arm8typctx e29_inet_makeaddr_arm8.
Proof. exact e29_inet_makeaddr_arm8.welltyped. Qed.
Print Assumptions inet_makeaddr_welltyped.

Theorem inet_makeaddr_preserves_memory:
  forall_endstates e29_inet_makeaddr_arm8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Print Assumptions inet_makeaddr_preserves_memory.

Definition inet_makeaddr_saved : list arm8var :=
  [R_SP; R_X30; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24;
   R_X25; R_X26; R_X27; R_X28; R_X29;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15].

Theorem inet_makeaddr_preserves_callee_saved:
  forall v, In v inet_makeaddr_saved ->
  forall_endstates e29_inet_makeaddr_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same. unfold inet_makeaddr_saved in IN.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Print Assumptions inet_makeaddr_preserves_callee_saved.

Theorem inet_makeaddr_preserves_sp:
  forall_endstates e29_inet_makeaddr_arm8 (fun _ s _ s' => s R_SP = s' R_SP).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Print Assumptions inet_makeaddr_preserves_sp.

Theorem inet_makeaddr_preserves_x30:
  forall_endstates e29_inet_makeaddr_arm8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Print Assumptions inet_makeaddr_preserves_x30.

Theorem inet_makeaddr_ret_map:
  forall s a, In a [0x1f9d50; 0x1f9d68; 0x1f9d88] ->
  e29_inet_makeaddr_arm8 s a = Some (4, Move R_PC (Var R_X30) $; Jmp (Var R_PC)).
Proof. intros s a H. repeat destruct H as [<-|H]; [reflexivity..|destruct H]. Qed.
Print Assumptions inet_makeaddr_ret_map.

Lemma inet_makeaddr_result_bound:
  forall net host, inet_makeaddr_result net host < 2^32.
Proof. intros. apply ntohl32_lt. Qed.
Print Assumptions inet_makeaddr_result_bound.

(* Pure bitvector facts; no use of finite tests as proof evidence. *)
Definition inet_rev32 (x:N) :=
  let y := ((x .& 0xff00ff00) >> 8 .| ((x .& 0x00ff00ff) << 8) mod 2^32) in
  (y >> 16 .| (y << 16) mod 2^32) mod 2^32.

Lemma inet_rev32_correct:
  forall x, inet_rev32 x = ntohl32 x.
Proof. intro x. unfold inet_rev32, ntohl32. bitblast_upto 32. Qed.
Print Assumptions inet_rev32_correct.

Definition inet_bfm32 (net host rotate mask:N) :=
  ((host .& (N.lxor mask (N.ones 32))) .|
   (((net mod 2^32) >> rotate .| ((net mod 2^32) << (32-rotate)) mod 2^32) .& mask))
  mod 2^32.

Lemma inet_bfm24_correct:
  forall net host, inet_bfm32 net host 8 0xff000000 =
    (net << 24 .| host mod 2^24) mod 2^32.
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Lemma inet_bfm16_correct:
  forall net host, inet_bfm32 net host 16 0xffff0000 =
    (net << 16 .| host mod 2^16) mod 2^32.
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Lemma inet_bfm8_correct:
  forall net host, inet_bfm32 net host 24 0xffffff00 =
    (net << 8 .| host mod 2^8) mod 2^32.
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Lemma inet_msub32_eqb:
  forall a b, a < 2^32 -> b < 2^32 ->
    (msub 32 a b =? 0) = (a =? b).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

(* An inhabited typed entry, including arbitrary 32-bit upper halves. *)
Definition inet_makeaddr_input (net host nhi hhi:N) : store :=
  update (update (fun _ => 0) R_X0 (net + 2^32*nhi)) R_X1 (host + 2^32*hhi).

Lemma inet_makeaddr_zero_typed:
  models arm8typctx (fun _ => 0).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Lemma inet_makeaddr_input_typed:
  forall net host nhi hhi,
  net < 2^32 -> host < 2^32 -> nhi < 2^32 -> hhi < 2^32 ->
  models arm8typctx (inet_makeaddr_input net host nhi hhi).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Theorem inet_makeaddr_inputs_inhabited:
  forall net host nhi hhi,
  net < 2^32 -> host < 2^32 -> nhi < 2^32 -> hhi < 2^32 ->
  exists s, models arm8typctx s /\
    trueif_inv (inet_makeaddr_invs net host 0 0 0 [(Addr 0x1f9d40,s)]).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Theorem inet_makeaddr_spec_inhabited:
  forall net host, net < 2^32 -> host < 2^32 ->
  exists s, models arm8typctx s /\ inet_makeaddr_postcondition net host 0 0 0 s.
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.

Theorem inet_makeaddr_correct:
  forall s t s' x' net host m sp lr
         (ENTRY: startof t (x',s') = (Addr 0x1f9d40,s))
         (MDL: models arm8typctx s)
         (NET: s R_X0 mod 2^32 = net) (HOST: s R_X1 mod 2^32 = host)
         (MEM: s V_MEM64 = m) (SP: s R_SP = sp) (LR: s R_X30 = lr),
  satisfies_all e29_inet_makeaddr_arm8 (inet_makeaddr_invs net host m sp lr)
    inet_makeaddr_exit ((x',s')::t).
Proof.
  (* PARTIAL: exact initial attempt and diagnostics are in
     notes/a-inet-makeaddr/initial-attempt.v.txt and initial-build.log.
     No Astra repair cycle was run. *)
Abort.
