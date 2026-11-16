(* l64a -- convert a long to a radix-64 ASCII string (musl x86_64, C)

   SEMANTICS
   ---------
   musl's l64a (src/misc/a64l.c) is

       static const char digits[] =
           "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
       char *l64a(long x0)
       {
           static char s[7];
           char *p;
           uint32_t x = x0;
           for (p=s; x; p++, x>>=6)
               *p = digits[x&63];
           *p = 0;
           return s;
       }

   In the binary the static buffer s is at 0x1a7066 and digits at 0x19d720
   (Ghidra addresses, image base 0x100000).

   SPECIFICATION (man 3 l64a, Linux man-pages 6.9.1, paraphrased)
   -------------------------------------------------------------
     char *l64a(long value);
     l64a converts the low 32 bits of value to a string of at most six
     radix-64 digits, least significant digit first, using the digit set
     "./0-9A-Za-z"; the result lives in a static buffer that later calls
     overwrite.  l64a(0) returns the empty string.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            l64a at 0x2c780 (Ghidra image base 0x100000: 0x12c780)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/l64a_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = x0; m = memory.  No precondition.  Let x = x0 mod 2^32.
   Output:  At the RET (0x12c7ba): RAX = 0x1a7066 (= buf) and there is a
            k <= 6 with x >> 6k = 0 and x >> 6j <> 0 for j < k (k is the
            number of radix-64 digits of x); buf[i] = m[0x19d720 +
            ((x >> 6i) & 63)] for i < k, buf[k] = 0, and every byte outside
            buf[0..k] is unchanged.  RSP and RBX, RBP, R12-R15 are unchanged.
            (l64a_digits: with musl's digit table in memory, buf[i] is the
            i-th digit character.)
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.l64a_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi.
Open Scope N.

Theorem l64a_welltyped: welltyped_prog x64typctx l64a_amd64.
Proof. exact welltyped. Qed.

Definition l64a_buf := 0x1a7066.
Definition l64a_tab := 0x19d720.

(* the first k bytes of the buffer hold the digits of x; nothing else moved *)
Definition lw (m m':memory) (x k:N) :=
  (forall i, i < k -> m' Ⓑ[l64a_buf + i] = m Ⓑ[l64a_tab + ((x >> (6*i)) .& 63)]) /\
  (forall b, k <= msub 64 b l64a_buf -> m' Ⓑ[b] = m Ⓑ[b]).

Lemma lw_empty: forall m x, lw m m x 0.
Proof. intros. split. intros i I. lia. reflexivity. Qed.

Lemma lw_set:
  forall m mem x k v, lw m mem x k -> k < 7 ->
  (forall i, i < k -> (mem [Ⓑl64a_buf + k := v]) Ⓑ[l64a_buf + i] = m Ⓑ[l64a_tab + ((x >> (6*i)) .& 63)]) /\
  (mem [Ⓑl64a_buf + k := v]) Ⓑ[l64a_buf + k] = v mod 2^8 /\
  (forall b, k + 1 <= msub 64 b l64a_buf -> (mem [Ⓑl64a_buf + k := v]) Ⓑ[b] = m Ⓑ[b]).
Proof.
  intros m mem x k v [W F] K. split; [|split].
  - intros i I. rewrite getmem_noverlap. apply W, I.
    intros [a [y [A [Y E]]]]. unfold l64a_buf in E.
    change (2^64) with 18446744073709551616 in *. lia.
  - rewrite getmem_setmem by discriminate. reflexivity.
  - intros b B. rewrite getmem_noverlap. apply F. lia.
    intros [a [y [A [Y E]]]]. unfold l64a_buf, msub in *.
    change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma digit_lt: forall y, y .& 63 < 64.
Proof. intro y. change 63 with (N.ones 6). rewrite N.land_ones. apply N.mod_lt. discriminate. Qed.

Lemma lw_step:
  forall m mem x k c, lw m mem x k -> k < 7 -> (x >> (6*k)) .& 63 = c ->
  lw m (mem [Ⓑl64a_buf + k := mem Ⓑ[l64a_tab + c]]) x (k + 1).
Proof.
  intros m mem x k c LW K C.
  destruct (lw_set m mem x k (mem Ⓑ[l64a_tab + c]) LW K) as [A [B D]]. split.
  - intros i I. destruct (N.lt_ge_cases i k). apply A; assumption.
    replace i with k by lia. rewrite B, N.mod_small by apply (getmem_bound 64 LittleE 1).
    rewrite C. destruct LW as [_ F]. apply F.
    pose proof (digit_lt (x >> (6*k))). rewrite C in *. unfold l64a_buf, l64a_tab, msub.
    change (2^64) with 18446744073709551616 in *. lia.
  - intros b Bb. apply D. lia.
Qed.

(* at most six digits: a 32-bit value shifted by 36 is 0 *)
Lemma digits_le6: forall x k, x < 2^32 -> x >> (6*k) <> 0 -> k < 6.
Proof.
  intros x k X NZ. destruct (N.lt_ge_cases k 6) as [H|H]. exact H. exfalso. apply NZ.
  rewrite N.shiftr_div_pow2. apply N.div_small. eapply N.lt_le_trans. exact X.
  apply N.pow_le_mono_r. discriminate. lia.
Qed.

Definition l64a_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x12c7ba => true
  | _ => false end | _ => false end.

Definition l64a_post (s0:store) (m x:N) (s:store) :=
  s R_RAX = l64a_buf /\
  (exists k, k <= 6 /\ x >> (6*k) = 0 /\ (forall j, j < k -> x >> (6*j) <> 0) /\
     (forall i, i < k -> s V_MEM64 Ⓑ[l64a_buf + i] = m Ⓑ[l64a_tab + ((x >> (6*i)) .& 63)]) /\
     s V_MEM64 Ⓑ[l64a_buf + k] = 0 /\
     (forall b, k + 1 <= msub 64 b l64a_buf -> s V_MEM64 Ⓑ[b] = m Ⓑ[b])) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition l64a_invs (s0:store) (m x:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x12c780 => Some (s V_MEM64 = m /\ s R_RDI mod 2^32 = x /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x12c7b3 => Some (exists k, k <= 6 /\ (forall j, j < k -> x >> (6*j) <> 0) /\
                      s R_RDI mod 2^32 = x >> (6*k) /\ s R_RDX = l64a_buf + k /\
                      s R_RAX = l64a_buf /\ s R_RSI = l64a_tab /\ lw m (s V_MEM64) x k /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x12c7ba => Some (l64a_post s0 m x s)
  | _ => None
  end | _ => None end.

Theorem l64a_correct:
  forall prog s t s' x' m x
         (L64A: l64a_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x12c780, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (X: s R_RDI mod 2^32 = x),
  satisfies_all prog (l64a_invs s m x) l64a_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m x L64A ENTRY MDL MEM X.
  assert (XB: x < 2^32) by (rewrite <- X; apply N.mod_lt; discriminate).
  eapply satisfies_all_pmono with (p1:=l64a_amd64); [exact L64A| |].
    intros a s1 t1 EXIT NOCODE. unfold l64a_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m x MDL MEM X XB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply l64a_welltyped. intro MDL1.
  clear - PRE MDL1 XB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [X [RSP CS]]].
    repeat x64_step.
    exists 0. conj_tac.
    all: first
      [ lia | (intros j J; lia) | (rewrite N.mul_0_r, N.shiftr_0_r; exact X)
      | (rewrite MEM; apply lw_empty) | reflexivity ].
  - destruct PRE as [k [K6 [NZ [RDI [RDX [RAX [RSI [LW [RSP CS]]]]]]]]].
    repeat x64_step.
    all: match goal with BC: (_ mod 2^32 =? 0) = _ |- _ => rewrite RDI in BC end.
    + (* exit *)
      apply N.eqb_eq in BC. split. exact RAX.
      split.
      * exists k. destruct (lw_set m (s1 V_MEM64) x k 0 LW ltac:(lia)) as [A [B D]].
        split. exact K6. split. exact BC. split. exact NZ. split. exact A.
        split. exact B. exact D.
      * conj_tac.
    + (* loop *)
      apply N.eqb_neq in BC. pose proof (digits_le6 x k XB BC) as K5.
      exists (k + 1). conj_tac.
      * lia.
      * intros j J. destruct (N.lt_ge_cases j k). apply NZ. assumption. replace j with k by lia. exact BC.
      * rewrite RDI, N.shiftr_shiftr. f_equal. lia.
      * unfold l64a_buf. rewrite N.mod_small. lia. change (2^64) with 18446744073709551616. lia.
      * apply lw_step. exact LW. lia.
        rewrite <- RDI. change 63 with (N.ones 6). rewrite N.land_ones.
        change 64 with (2^6). rewrite mp2_mod_mod_min. reflexivity.
Qed.

(* musl's digit table: "./0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz" *)
Definition l64a_char (d:N) := if d <? 12 then 46 + d else if d <? 38 then 53 + d else 59 + d.

Corollary l64a_digits:
  forall m mem x k,
  (forall d, d < 64 -> m Ⓑ[l64a_tab + d] = l64a_char d) ->
  (forall i, i < k -> mem Ⓑ[l64a_buf + i] = m Ⓑ[l64a_tab + ((x >> (6*i)) .& 63)]) ->
  forall i, i < k -> mem Ⓑ[l64a_buf + i] = l64a_char ((x >> (6*i)) .& 63).
Proof. intros m mem x k TAB W i I. rewrite W by exact I. apply TAB, digit_lt. Qed.

(* sanity check of l64a_char against the table bytes (objdump of 0x9d720) *)
Example l64a_char_check:
  map l64a_char [0;1;2;11;12;37;38;63] = [46;47;48;57;65;90;97;122].
Proof. reflexivity. Qed.
