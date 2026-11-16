(* swab -- swap adjacent bytes (musl x86_64, C)

   SEMANTICS
   ---------
   musl's swab (src/string/swab.c) is

       const char *src = _src;  char *dest = _dest;
       for (; n>1; n-=2) {
           dest[0] = src[1];
           dest[1] = src[0];
           dest += 2;
           src += 2;
       }

   GCC turns the counter into an end pointer (end = src + n) and tests the
   signed difference end - src > 1 (CMP RAX,1; JG).

   SPECIFICATION (man 3 swab, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     void swab(const void from[restrict .n], void to[restrict .n], ssize_t n);
     swab copies n bytes from `from' to `to', exchanging adjacent even and
     odd bytes.  When n is odd the last byte is left alone (musl copies only
     the 2*floor(n/2) bytes of whole pairs); a negative n copies nothing.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            swab at 0x24900 (Ghidra image base 0x100000: 0x124900)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/swab_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = src, RSI = dest, RDX = n (a 64-bit word read as ssize_t);
            m = memory.  Let P = 2*floor(n/2) if n < 2^63 (n >= 0 as ssize_t)
            and P = 0 otherwise.  Precondition: the P bytes at dest and the
            P bytes at src do not overlap (nov dest src P; restrict).
   Output:  At the RET (0x124962): for i < P, dest[i] = src[i xor 1]
            (swb: byte i of dest holds byte sw i of src, sw 2j = 2j+1 and
            sw (2j+1) = 2j); every byte whose offset from dest (mod 2^64) is
            >= P is unchanged.  RSP and RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.swab_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_memcpy_sets CoqEtTu.lib.x64_signed.
Open Scope N.

Theorem swab_welltyped: welltyped_prog x64typctx swab_amd64.
Proof. exact welltyped. Qed.

(* the partner of byte i within its pair *)
Definition sw (i:N) := if N.even i then i + 1 else i - 1.

(* number of pairs swapped *)
Definition npairs (n:N) := if n <? 2^63 then n / 2 else 0.

(* the first k bytes at d hold the pair-swapped bytes of s; bytes at offsets
   >= k from d are as in m *)
Definition swb (m m':memory) (d s k:N) :=
  (forall i, i < k -> m' Ⓑ[d ⊕ i] = m Ⓑ[s ⊕ sw i]) /\
  (forall b, k <= msub 64 b d -> m' Ⓑ[b] = m Ⓑ[b]).

Lemma swb_empty: forall m d s, swb m m d s 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma swb_store:
  forall m m' d s k a v, swb m m' d s k -> k < 2^64 ->
  a mod 2^64 = (d + k) mod 2^64 -> v mod 2^8 = m Ⓑ[s ⊕ sw k] ->
  swb m (setmem 64 LittleE 1 m' a v) d s (k + 1).
Proof.
  intros m m' d s k a v [W F] K A V. split.
  - intros i I. destruct (N.lt_ge_cases i k) as [IK|IK].
    + rewrite getmem_noverlap. apply W, IK.
      intros [x [y [X [Y E]]]]. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
    + replace i with k by lia.
      rewrite <- A, getmem_mod_l, getmem_setmem by discriminate. exact V.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [x [y [X [Y E]]]]. unfold msub in *. change (2^64) with 18446744073709551616 in *. lia.
Qed.

(* source bytes are not yet overwritten *)
Lemma swb_src:
  forall m m' d s k P i, swb m m' d s k -> nov d s P -> k <= P -> i < P ->
  m' Ⓑ[s ⊕ i] = m Ⓑ[s ⊕ i].
Proof.
  intros m m' d s k P i [W F] NOV KP I. apply F.
  destruct (N.le_gt_cases k (msub 64 (s ⊕ i) d)) as [H|H]. exact H. exfalso.
  apply (NOV (msub 64 (s ⊕ i) d) i). lia. exact I.
  rewrite add_msub, N.mod_mod by discriminate. reflexivity.
Qed.

Lemma sw_even: forall j, sw (2*j) = 2*j + 1.
Proof. intro j. unfold sw. rewrite N.even_mul. reflexivity. Qed.

Lemma sw_odd: forall j, sw (2*j + 1) = 2*j.
Proof.
  intro j. unfold sw. rewrite N.even_add, N.even_mul. simpl. lia.
Qed.

(* one loop iteration, in the shape x64_step leaves the two byte stores *)
Lemma swb_pair:
  forall m mem d s j P, swb m mem d s (2*j) -> nov d s P -> 2*j + 2 <= P -> P < 2^64 ->
  swb m (mem [Ⓑd + 2*j := mem Ⓑ[1 + s + 2*j]]
             [Ⓑ1 + d + 2*j := (mem [Ⓑd + 2*j := mem Ⓑ[1 + s + 2*j]]) Ⓑ[s + 2*j]]) d s (2*(j+1)).
Proof.
  intros m mem d s j P SW NOV JP PB.
  assert (SW1: swb m (mem [Ⓑd + 2*j := mem Ⓑ[1 + s + 2*j]]) d s (2*j + 1)).
  { apply swb_store. exact SW. lia. reflexivity.
    rewrite N.mod_small by apply (getmem_bound 64 LittleE 1). rewrite sw_even.
    replace (1 + s + 2*j) with (s + (2*j + 1)) by lia. rewrite <- getmem_mod_l.
    apply (swb_src m mem d s (2*j) P). exact SW. exact NOV. lia. lia. }
  replace (2*(j+1)) with (2*j + 1 + 1) by lia. apply swb_store. exact SW1. lia.
  f_equal. lia.
  rewrite N.mod_small by apply (getmem_bound 64 LittleE 1). rewrite sw_odd.
  rewrite <- getmem_mod_l.
  apply (swb_src m _ d s (2*j + 1) P). exact SW1. exact NOV. lia. lia.
Qed.

Lemma npairs_cases: forall n, (n < 2^63 /\ npairs n = n / 2) \/ (2^63 <= n /\ npairs n = 0).
Proof.
  intro n. unfold npairs. destruct (N.ltb_spec n (2^63)). left; split; [assumption|reflexivity].
  right; split; [assumption|reflexivity].
Qed.

Definition swab_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x124962 => true
  | _ => false end | _ => false end.

Definition swab_post (s0:store) (m src dest n:N) (s:store) :=
  swb m (s V_MEM64) dest src (2 * npairs n) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition swab_invs (s0:store) (m src dest n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x124900 => Some (s V_MEM64 = m /\ s R_RDI = src /\ s R_RSI = dest /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x124956 => Some (exists j, j <= npairs n /\ s R_RDI = src ⊕ 2*j /\ s R_RSI = dest ⊕ 2*j /\
                      s R_RDX = src ⊕ n /\ swb m (s V_MEM64) dest src (2*j) /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x124962 => Some (swab_post s0 m src dest n s)
  | _ => None
  end | _ => None end.

Theorem swab_correct:
  forall prog s t s' x' m src dest n
         (SWAB: swab_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x124900, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (S: s R_RDI = src) (D: s R_RSI = dest) (Nn: s R_RDX = n)
         (NOV: nov dest src (2 * npairs n)),
  satisfies_all prog (swab_invs s m src dest n) swab_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m src dest n SWAB ENTRY MDL MEM S D Nn NOV.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RDI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=swab_amd64); [exact SWAB| |].
    intros a s1 t1 EXIT NOCODE. unfold swab_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m src dest n MDL MEM S D Nn NOV NB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply swab_welltyped. intro MDL1.
  clear - PRE MDL1 NOV NB SB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [S [D [Nn [RSP CS]]]]].
    repeat x64_step.
    exists 0. conj_tac.
    + lia.
    + rewrite N.add_0_r. symmetry. apply N.mod_small. assumption.
    + rewrite N.add_0_r, N.mod_small. exact D. rewrite <- D. apply (MDL1 R_RSI 64). reflexivity.
    + rewrite N.add_comm. reflexivity.
    + rewrite MEM. apply swb_empty.
  - destruct PRE as [j [JN [RDI [RSI [RDX [SW [RSP CS]]]]]]].
    repeat x64_step.
    all: match goal with BC: context [slt 64 _ 0] |- _ =>
           rewrite jg1_64 in BC by apply msub_lt end.
    all: assert (P2: 2 * npairs n <= n) by
           (destruct (npairs_cases n) as [[_ E]|[_ E]]; rewrite E;
            [apply N.Div0.mul_div_le | lia]).
    all: assert (XM: msub 64 n (2*j) = n - 2*j) by mlia64.
    all: rewrite XM in *.
    + (* exit: j is the number of pairs *)
      assert (JE: j = npairs n).
      { destruct (npairs_cases n) as [[NL E]|[NL E]]; rewrite E in *.
        - destruct (N.ltb_spec 1 (n - 2*j)), (N.ltb_spec (n - 2*j) (2^63)); try discriminate.
          + change (2^63) with 9223372036854775808 in *. lia.
          + pose proof (N.Div0.div_mod n 2). pose proof (N.mod_lt n 2 ltac:(discriminate)). lia.
          + pose proof (N.Div0.div_mod n 2). pose proof (N.mod_lt n 2 ltac:(discriminate)). lia.
        - lia. }
      rewrite <- JE. split. exact SW. conj_tac.
    + (* loop *)
      assert (J1: j + 1 <= npairs n).
      { destruct (npairs_cases n) as [[NL E]|[NL E]]; rewrite E in *.
        - destruct (N.ltb_spec 1 (n - 2*j)), (N.ltb_spec (n - 2*j) (2^63)); try discriminate.
          pose proof (N.Div0.div_mod n 2). pose proof (N.mod_lt n 2 ltac:(discriminate)). lia.
        - assert (j = 0) by lia. subst j.
          destruct (N.ltb_spec 1 (n - 2*0)), (N.ltb_spec (n - 2*0) (2^63)); try discriminate. lia. }
      exists (j + 1). conj_tac.
      all: first
        [ exact J1 | (f_equal; lia)
        | (apply (swb_pair m _ dest src j (2 * npairs n)); [exact SW | exact NOV | lia | lia]) ].
Qed.
