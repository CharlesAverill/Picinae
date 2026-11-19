(* dn_skipname -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (leaf, one loop)

   SEMANTICS
   ---------
   musl's src/network/dn_skipname.c:
       int dn_skipname(const unsigned char *s, const unsigned char *end)
       {
           const unsigned char *p = s;
           while (p < end)
               if (!*p) return p-s+1;
               else if ( *p>=192)
                   if (p+1<end) return p-s+2;
                   else break;
               else
                   if (end-p<*p+1) break;
                   else p += *p+1;
           return -1;
       }
   compiled to a 26-instruction leaf loop (0x13ff00-0x13ff64); end-p < *p+1
   is a signed 64-bit compare (b.lt).

   SPECIFICATION (musl / BIND resolver API; no Linux man page)
   ------------------------------------------------------------
   dn_skipname() skips over a compressed domain name starting at s, not
   reading at or beyond end, and returns its length in bytes, or -1 if the
   name runs past end.  A name is a sequence of labels, each a length byte
   1..63 (here: any byte below 192) followed by that many bytes, ended by a
   zero byte or by a 2-byte compression pointer (first byte >= 192).

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            dn_skipname at 0x3ff00 (ELF vaddr); 0x13ff00 in Ghidra (image base 0x100000)
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck, project aarch64/ghidra2;
            see ../lifted/dn_skipname_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = s, X1 = e (end); X30 = raddr; memory m.
   Precondition: s <= e and e - s < 2^63 (the buffer does not wrap and is
            shorter than 2^63 bytes, so the signed end-p compare is the
            ordinary one; dn_lt_flag).
   Output:  If the RET (0x13ff64) is reached (dn_post): there is p with
            dn_walk m s e p (p is reached from s by skipping labels whose
            length byte b is 1..191 and b+1 <= e-p) and s <= p <= e, and
            X0 = dn_res m s e p:
              - p >= e:                       0xffffffff (-1);
              - byte at p = 0:                (p + 1 - s) mod 2^32;
              - byte at p >= 192:             (p + 2 - s) mod 2^32 if
                                              p + 1 < e, else 0xffffffff;
              - otherwise (label too long):   0xffffffff.
            Memory, SP, X30 and the AAPCS64 callee-saved registers are
            unchanged.
 *)

From Stdlib Require Import Utf8 NArith ZArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require Import dn_skipname_armv8.
From Grok.lib Require Import GrokCommon GrokStep.
Import ARM8Notations.
Open Scope N.

Lemma msub64_le: ∀ x y, y <= x -> x < 2^64 -> msub 64 x y = x - y.
Proof.
  intros x y H1 H2. unfold msub. rewrite (N.mod_small y) by lia.
  replace (x + (2^64 - y)) with ((x - y) + 1 * 2^64) by lia.
  rewrite N.mod_add by discriminate. apply N.mod_small. lia.
Qed.

Lemma msub64_gt: ∀ x y, x < y -> y < 2^64 -> msub 64 x y = x + 2^64 - y.
Proof.
  intros x y H1 H2. unfold msub. rewrite (N.mod_small y) by lia.
  rewrite N.mod_small by lia. lia.
Qed.

Lemma slt0_64: ∀ r, r < 2^64 -> slt 64 r 0 = (2^63 <=? r).
Proof.
  intros r R. unfold slt. change (toZ 64 0) with 0%Z.
  pose proof (toZ_sign r 64) as TS. rewrite N.mod_small in TS by exact R.
  change (2^N.pred 64) with (2^63) in TS.
  destruct (Z.ltb_spec (toZ 64 r) 0), (N.leb_spec (2^63) r); try reflexivity.
  - exfalso. apply Z.lt_nge in H. apply H, TS. exact H0.
  - exfalso. apply N.le_ngt in H0. apply H0, TS. exact H.
Qed.

Lemma scast32_small: ∀ n, n < 2^31 -> scast 32 64 n = n.
Proof.
  intros n H. unfold scast. rewrite (proj1 (toZ_nonneg 32 n)) by (rewrite N.mod_small; [exact H|lia]).
  rewrite N.mod_small by lia. unfold ofZ. rewrite Z.mod_small. apply N2Z.id.
  split. apply N2Z.is_nonneg. change (2 ^ Z.of_N 64)%Z with (Z.of_N (2^64)). apply N2Z.inj_lt. lia.
Qed.

(* b.lt after cmp x, y with both operands below 2^63 is the plain x < y. *)
Lemma dn_lt_flag: ∀ x y, x < 2^63 -> y < 2^63 ->
  negb ((if slt 64 (x ⊖ y) 0 then 1 else 0) =?
        (x >> 63 .^ x ⊖ y >> 63) .& (x ⊖ y >> 63 .^ (y >> 63) mod 2 .^ 1)) = (x <? y).
Proof.
  intros x y Hx Hy.
  assert (X63: x >> 63 = 0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact Hx).
  assert (Y63: y >> 63 = 0) by (rewrite N.shiftr_div_pow2; apply N.div_small; exact Hy).
  rewrite X63, Y63.
  destruct (N.leb_spec y x) as [LE|GT].
  - rewrite msub64_le by lia. rewrite slt0_64 by lia.
    assert (R: x - y >> 63 = 0) by (rewrite N.shiftr_div_pow2; apply N.div_small; lia).
    rewrite R. destruct (N.leb_spec (2^63) (x - y)); [lia|].
    destruct (N.ltb_spec x y); [lia|]. reflexivity.
  - rewrite msub64_gt by lia. rewrite slt0_64 by lia.
    assert (R: x + 2^64 - y >> 63 = 1).
    { rewrite N.shiftr_div_pow2. symmetry. apply (N.div_unique _ _ _ (x + 2^64 - y - 2^63)); lia. }
    rewrite R. destruct (N.leb_spec (2^63) (x + 2^64 - y)); [|lia].
    destruct (N.ltb_spec x y); [|lia]. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Frame theorems                                                          *)

Theorem dn_skipname_nwc: ∀ s2 s1, dn_skipname_armv8 s1 = dn_skipname_armv8 s2.
Proof. reflexivity. Qed.

Theorem dn_skipname_welltyped: welltyped_prog arm8typctx dn_skipname_armv8.
Proof. Picinae_typecheck. Qed.

Theorem dn_skipname_preserves_memory:
  forall_endstates dn_skipname_armv8 (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.

Theorem dn_skipname_preserves_callee_saved:
  ∀ r, In r aapcs64_callee_saved ->
  forall_endstates dn_skipname_armv8 (fun _ s _ s' => s r = s' r).
Proof. prove_regs_noassign. Qed.

Theorem dn_skipname_preserves_x30:
  forall_endstates dn_skipname_armv8 (fun _ s _ s' => s R_X30 = s' R_X30).
Proof. apply noassign_prog_same. prove_noassign. Qed.

(* ---------------------------------------------------------------------- *)
(* Specification                                                           *)

(* p is reached from s by skipping plain labels (length byte 1..191) that
   fit before e. *)
Inductive dn_walk (m:memory) (s e:N) : N -> Prop :=
| DW0 : dn_walk m s e s
| DWS p : dn_walk m s e p -> p < e -> m Ⓑ[p] <> 0 -> m Ⓑ[p] < 192 ->
          m Ⓑ[p] + 1 <= e - p -> dn_walk m s e (p + m Ⓑ[p] + 1).

(* 32-bit return value when the scan stops at p. *)
Definition dn_res (m:memory) (s e p:N) : N :=
  if e <=? p then 2^32 - 1
  else if m Ⓑ[p] =? 0 then msub 32 (1 + p) s
  else if 192 <=? m Ⓑ[p] then (if p + 1 <? e then msub 32 (2 + p) s else 2^32 - 1)
  else 2^32 - 1.

Section Invariants.
  Variables (mem s e raddr : N).
  Definition dn_post (st:store) :=
    ∃ p, dn_walk mem s e p /\ s <= p <= e /\ st R_X0 = dn_res mem s e p /\
         st V_MEM64 = mem /\ st R_X30 = raddr.
  Definition invs T (Inv Post: inv_type T) (NoInv:T) (st:store) (a:addr) : T :=
    match a with
    | 0x13ff00 => Inv 0 (st R_X0 = s /\ st R_X1 = e /\ st V_MEM64 = mem /\ st R_X30 = raddr)
    | 0x13ff04 => Inv 0 (∃ p, st R_X3 = p /\ dn_walk mem s e p /\ s <= p <= e /\
                         st R_X0 = s /\ st R_X1 = e /\ st V_MEM64 = mem /\ st R_X30 = raddr)
    | 0x13ff64 => Post 0 (dn_post st)
    | _ => NoInv
    end.
  Definition dn_skipname_exits := make_exits 0 dn_skipname_armv8 invs.
  Definition dn_skipname_invs := make_invs 0 dn_skipname_armv8 invs.
End Invariants.

Theorem dn_skipname_partial_correctness:
  ∀ prog s0 mem s e raddr t xs'
    (PROG: dn_skipname_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x13ff00, s0))
    (MDL: models arm8typctx s0)
    (MEM: s0 V_MEM64 = mem) (X30: s0 R_X30 = raddr) (X0: s0 R_X0 = s) (X1: s0 R_X1 = e)
    (SE: s <= e) (SPAN: e - s < 2^63),
  satisfies_all prog (dn_skipname_invs mem s e raddr) (dn_skipname_exits mem s e raddr) (xs'::t).
Proof.
  intros.
  eapply satisfies_all_pmono with (p1:=dn_skipname_armv8). exact PROG.
    intros x s1 t1 EXIT NOCODE. unfold dn_skipname_invs, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL MEM X30 X0 X1 SE SPAN START. rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  pose proof (MDL R_X1 64 eq_refl) as E64. rewrite X1 in E64. simpl in E64.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply dn_skipname_welltyped. intro MDL1.
  clear - PRE MDL1 SE SPAN E64. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as (X0 & X1 & MEM & X30).
    arm8_step. exists s. splits; try assumption; try reflexivity; try apply DW0; lia.
  - destruct PRE as (p & X3 & WK & SP & X0 & X1 & MEM & X30).
    pose proof (getmem_bound 64 LittleE 1 mem p) as BB. change (2^(1*8)) with 256 in BB.
    repeat arm8_step.
    all: try first [ apply N.leb_le in BC | apply N.leb_gt in BC ].
    all: try first [ apply N.eqb_eq in BC0 | apply N.eqb_neq in BC0 ].
    (* stopped at e <= p *)
    + exists p. splits; try assumption; try reflexivity; try lia.
      unfold dn_res. destruct (N.leb_spec e p); [reflexivity | lia].
    (* terminating zero byte *)
    + exists p. splits; try assumption; try reflexivity; try lia.
      unfold dn_res. destruct (N.leb_spec e p); [lia|]. rewrite BC0. reflexivity.
    (* plain label that does not fit *)
    + assert (LO: mem Ⓑ[p] <= 191) by (revert BC1; destruct (N.eqb_spec (mem Ⓑ[p]) 191), (N.leb_spec 191 (mem Ⓑ[p])); intros; try discriminate; lia).
      rewrite N.shiftr_0_r, (N.mod_small (1 + mem Ⓑ[p])), scast32_small, (msub64_le e p), dn_lt_flag in BC2 by lia.
      apply N.ltb_lt in BC2.
      exists p. splits; try assumption; try reflexivity; try lia.
      unfold dn_res. destruct (N.leb_spec e p); [lia|].
      destruct (N.eqb_spec (mem Ⓑ[p]) 0); [contradiction|].
      destruct (N.leb_spec 192 (mem Ⓑ[p])); [lia|]. reflexivity.
    (* plain label: skip it *)
    + assert (LO: mem Ⓑ[p] <= 191) by (revert BC1; destruct (N.eqb_spec (mem Ⓑ[p]) 191), (N.leb_spec 191 (mem Ⓑ[p])); intros; try discriminate; lia).
      rewrite N.shiftr_0_r, (N.mod_small (1 + mem Ⓑ[p])), scast32_small, (msub64_le e p), dn_lt_flag in BC2 by lia.
      apply N.ltb_ge in BC2.
      eexists. split. reflexivity.
      rewrite N.mod_small by lia. replace (1 + p + mem Ⓑ[p]) with (p + mem Ⓑ[p] + 1) by lia.
      splits; try assumption; try reflexivity; try lia.
      apply DWS; try assumption; lia.
    (* compression pointer, p + 1 >= e *)
    + assert (HI: 192 <= mem Ⓑ[p]) by (revert BC1; destruct (N.eqb_spec (mem Ⓑ[p]) 191), (N.leb_spec 191 (mem Ⓑ[p])); intros; try discriminate; lia).
      rewrite (msub64_le e 1), (N.mod_small (1 + p)) in BC2 by lia.
      assert (NL: e <= p + 1) by (revert BC2; destruct (N.eqb_spec (e - 1) p), (N.leb_spec (1 + p) e); intros; try discriminate; lia).
      exists p. splits; try assumption; try reflexivity; try lia.
      unfold dn_res. destruct (N.leb_spec e p); [lia|].
      destruct (N.eqb_spec (mem Ⓑ[p]) 0); [contradiction|].
      destruct (N.leb_spec 192 (mem Ⓑ[p])); [|lia]. destruct (N.ltb_spec (p + 1) e); [lia|]. reflexivity.
    (* compression pointer, p + 1 < e *)
    + assert (HI: 192 <= mem Ⓑ[p]) by (revert BC1; destruct (N.eqb_spec (mem Ⓑ[p]) 191), (N.leb_spec 191 (mem Ⓑ[p])); intros; try discriminate; lia).
      rewrite (msub64_le e 1), (N.mod_small (1 + p)) in BC2 by lia.
      assert (LT: p + 1 < e) by (revert BC2; destruct (N.eqb_spec (e - 1) p), (N.leb_spec (1 + p) e); intros; try discriminate; lia).
      exists p. splits; try assumption; try reflexivity; try lia.
      unfold dn_res. destruct (N.leb_spec e p); [lia|].
      destruct (N.eqb_spec (mem Ⓑ[p]) 0); [contradiction|].
      destruct (N.leb_spec 192 (mem Ⓑ[p])); [|lia]. destruct (N.ltb_spec (p + 1) e); [|lia]. reflexivity.
Qed.
