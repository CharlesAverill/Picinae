(* inet_netof inet_lnaof inet_makeaddr -- classful IPv4 address arithmetic
   (musl x86_64, C)

   SEMANTICS
   ---------
   musl's src/network/inet_legacy.c (the address is taken in host order):

       in_addr_t inet_netof(struct in_addr in)
       { uint32_t h = in.s_addr;
         if (h>>24 < 128) return h >> 24;
         if (h>>24 < 192) return h >> 16;
         return h >> 8; }
       in_addr_t inet_lnaof(struct in_addr in)
       { uint32_t h = in.s_addr;
         if (h>>24 < 128) return h & 0xffffff;
         if (h>>24 < 192) return h & 0xffff;
         return h & 0xff; }
       struct in_addr inet_makeaddr(in_addr_t n, in_addr_t h)
       { if (n < 256) h |= n<<24;
         else if (n < 65536) h |= n<<16;
         else h |= n<<8;
         return (struct in_addr){ h }; }

   compiled with a sign test (h>>24 < 128 iff bit 31 clear) and CMOVA.

   SPECIFICATION (man 3 inet, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     in_addr_t inet_netof(struct in_addr in);  returns the network number
     part of the Internet address in;  in_addr_t inet_lnaof(struct in_addr in)
     returns the local network address part;  struct in_addr
     inet_makeaddr(in_addr_t net, in_addr_t host) is the converse.  These
     are obsolete classful (class A/B/C) functions.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            inet_makeaddr at 0x5a11b, inet_lnaof at 0x5a143, inet_netof at
            0x5a166 (Ghidra image base 0x100000)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see programs/inet_{netof,lnaof,makeaddr}_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = h (netof, lnaof) or n (makeaddr), RSI = h (makeaddr); only
            the low 32 bits are used.  No precondition.
   Output:  At the RET: RAX = netof_spec / lnaof_spec / makeaddr_spec of the
            32-bit arguments (below); memory, RSP and RBX, RBP, R12-R15
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.inet_netof_amd64 CoqEtTu.programs.inet_lnaof_amd64 CoqEtTu.programs.inet_makeaddr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia Bool.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_signed CoqEtTu.lib.x64_ctype.
Open Scope N.

Definition netof_spec (h:N) := if h >> 24 <? 128 then h >> 24 else if h >> 24 <? 192 then h >> 16 else h >> 8.
Definition lnaof_spec (h:N) := if h >> 24 <? 128 then h mod 2^24 else if h >> 24 <? 192 then h mod 2^16 else h mod 2^8.
Definition makeaddr_spec (n h:N) :=
  ((if n <? 256 then n << 24 else if n <? 65536 then n << 16 else n << 8) mod 2^32) .| h.

Definition in_exit (r1 r2:N) (t:trace) :=
  match t with (Addr a,_)::_ => (a =? r1) || (a =? r2) | _ => false end.

Definition in_invs (e r1 r2:N) (f:N -> N -> N) (s0:store) (x y:N) (t:trace) :=
  match t with (Addr a,s)::_ =>
    if a =? e then Some (s R_RDI = x /\ s R_RSI = y /\ s V_MEM64 = s0 V_MEM64 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else if (a =? r1) || (a =? r2) then
      Some (s R_RAX = f (x mod 2^32) (y mod 2^32) /\ s V_MEM64 = s0 V_MEM64 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
    else None
  | _ => None end.

Ltac num_bc :=
  repeat match goal with
  | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
  | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
  | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
  | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
  | H: negb _ = true |- _ => apply negb_true_iff in H
  | H: negb _ = false |- _ => apply negb_false_iff in H
  end.

Ltac in_tac wt :=
  intros prog s0 t s' x' x y P ENTRY MDL X Y;
  eapply satisfies_all_pmono; [exact P| |];
  [ intros a s1 t1 EXIT NOCODE; unfold in_invs, in_exit in *;
    repeat match goal with |- context [a =? ?e] => destruct (N.eqb_spec a e) as [->|_] end;
    first [discriminate NOCODE | discriminate EXIT | reflexivity]
  | ];
  intros [x1 s1] t1 START; rewrite ENTRY in START;
  apply prove_invs;
  [ simpl; rewrite START; x64_step; conj_tac; apply callee_saved_eq_refl
  | intros tt1 aa1 ss1 tt2 UT SPL PRE;
    erewrite startof_prefix in START; try eassumption;
    eapply models_at_invariant; try eassumption; [exact wt|]; intro MDL1;
    destruct_inv 64 PRE;
    destruct PRE as [X' [Y' [MEM [RSP CS]]]];
    repeat x64_step; bc_norm ].

Lemma mod32_k: forall x k, k <= 32 -> (x mod 2^32) mod 2^k = x mod 2^k.
Proof.
  intros x k K. apply N.bits_inj. intro i. destruct (N.lt_ge_cases i k).
  - rewrite !N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma mk_eq: forall x y k, ((x mod 2^32) << k) mod 2^32 .| y mod 2^32 = (x << k .| y) mod 2^32.
Proof.
  intros x y k. apply N.bits_inj. intro i. destruct (N.lt_ge_cases i 32).
  - rewrite N.lor_spec, !N.mod_pow2_bits_low, N.lor_spec by lia.
    destruct (N.lt_ge_cases i k).
    + rewrite !N.shiftl_spec_low by lia. reflexivity.
    + rewrite !N.shiftl_spec_high by lia. rewrite N.mod_pow2_bits_low by lia. reflexivity.
  - rewrite N.lor_spec, !N.mod_pow2_bits_high by lia. reflexivity.
Qed.

Ltac in_close x y :=
  pose proof (N.mod_lt x (2^32) ltac:(discriminate)) as XB;
  pose proof (N.mod_lt y (2^32) ltac:(discriminate)) as YB;
  rewrite ?N.shiftr_0_r, ?N.land_diag in *;
  repeat match goal with H: slt 32 (?y mod 2^32) 0 = _ |- _ =>
    rewrite (slt32_0' (y mod 2^32)) in H by (apply N.mod_lt; discriminate) end;
  repeat match goal with |- context [?a .& 18446744069414584320] =>
    rewrite (land_high32 a) by
      first [ (rewrite N.shiftr_div_pow2; apply (N.le_lt_trans _ (x mod 2^32)); [apply N.div_le_upper_bound; lia | exact XB])
            | (eapply N.lt_le_trans; [apply N.mod_lt; discriminate | discriminate]) ]
  end;
  rewrite ?N.lor_0_r;
  split; [|conj_tac];
  unfold netof_spec, lnaof_spec, makeaddr_spec;
  rewrite ?(mod32_k x 24), ?(mod32_k x 16), ?(mod32_k x 8) by discriminate;
  num_bc;
  repeat match goal with |- context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E end;
  num_bc;
  try reflexivity;
  try (rewrite mk_eq; reflexivity);
  exfalso; rewrite ?N.shiftr_div_pow2 in *;
  change (2^24) with 16777216 in *; change (2^31) with 2147483648 in *; change (2^32) with 4294967296 in *;
  lia.

Theorem inet_netof_correct:
  forall prog s t s' x' x y (P: inet_netof_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15a166, s)) (MDL: models x64typctx s)
         (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (in_invs 0x15a166 0x15a181 0x15a181 (fun h _ => netof_spec h) s x y) (in_exit 0x15a181 0x15a181) ((x',s')::t).
Proof. in_tac inet_netof_amd64.welltyped. all: in_close x y. Qed.

Theorem inet_lnaof_correct:
  forall prog s t s' x' x y (P: inet_lnaof_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15a143, s)) (MDL: models x64typctx s)
         (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (in_invs 0x15a143 0x15a15d 0x15a165 (fun h _ => lnaof_spec h) s x y) (in_exit 0x15a15d 0x15a165) ((x',s')::t).
Proof.
  in_tac inet_lnaof_amd64.welltyped.
  all: in_close x y.
Qed.

Theorem inet_makeaddr_correct:
  forall prog s t s' x' x y (P: inet_makeaddr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x15a11b, s)) (MDL: models x64typctx s)
         (X: s R_RDI = x) (Y: s R_RSI = y),
  satisfies_all prog (in_invs 0x15a11b 0x15a12a 0x15a142 makeaddr_spec s x y) (in_exit 0x15a12a 0x15a142) ((x',s')::t).
Proof.
  in_tac inet_makeaddr_amd64.welltyped.
  all: in_close x y.
Qed.
