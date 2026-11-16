(* wmemcmp -- compare two arrays of wide characters (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wmemcmp (src/string/wmemcmp.c) is

       for (; n && *l==*r; n--, l++, r++);
       return n ? ( *l<*r ? -1 : *l>*r) : 0;

   wchar_t is a signed 32-bit int on x86_64, so the final comparison is
   signed (GCC: CMP, SETG, CMOVL); the result is exactly -1, 0 or 1.  Unlike
   wcsncmp, a zero word does not stop the scan.  Ghidra took the leading
   JMP to the loop head 0x134f2c for a tail call and split the function
   there; programs/wmemcmp_amd64.v is the merge of both lifted pieces
   (tools/merge_lift.py), checked complete against objdump by
   tools/check_lift.py.

   SPECIFICATION (man 3 wmemcmp, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>

            int wmemcmp(const wchar_t s1[.n], const wchar_t s2[.n], size_t n);

     DESCRIPTION
            The wmemcmp() function is the wide-character equivalent of the memcmp(3)
            function.   It  compares	 the n wide-characters starting at s1 and the n
            wide-characters starting at s2.

     RETURN VALUE
            The wmemcmp() function returns zero if the wide-character arrays of size
            n at s1 and s2 are equal.  It returns an integer greater than zero if at
            the first differing position i (i < n), the corresponding wide-character
            s1[i] is greater than s2[i].  It returns an integer less than zero if at
            the first differing position i (i < n), the corresponding wide-character
            s1[i] is less than s2[i].

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wmemcmp at 0x34f00 (Ghidra image base 0x100000: 0x134f00)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wmemcmp_amd64.v
            (merged with the FUN_00134f2c fragment).
   Model:   This specification and proof were written by Claude Fable 5.1
            (claude-fable-5-1), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = l, RSI = r, RDX = n; m = memory on entry.  No precondition.
   Output:  At either RET (0x134f47, 0x134f4a) there is K <= n such that the
            words l[i] = r[i] for i < K (weq_prefix), and either K = n and
            RAX = 0, or K < n, l[K] <> r[K] and RAX = wcmp l[K] r[K]:
            0xffffffff (-1) if l[K] < r[K] as signed 32-bit ints, 1 if
            greater (wmemcmp_result).  Memory, RSP and RBX, RBP, R12-R15 are
            unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wmemcmp_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_signed.
Open Scope N.

Ltac amlia := arith_only; unfold msub in *; change (2^64) with 18446744073709551616 in *;
  change (2^63) with 9223372036854775808 in *; lia.

Theorem wmemcmp_nwc: forall s2 s1, wmemcmp_amd64 s1 = wmemcmp_amd64 s2.
Proof. reflexivity. Qed.

Theorem wmemcmp_welltyped: welltyped_prog x64typctx wmemcmp_amd64.
Proof. exact welltyped. Qed.

(* the words l[0..k) and r[0..k) are equal *)
Definition weq_prefix (m:memory) (l r k:N) :=
  forall i, i < k -> m Ⓓ[l ⊕ 4*i] = m Ⓓ[r ⊕ 4*i].

(* signed three-way comparison of two 32-bit words, as an int (as in wcscmp_proof.v) *)
Definition wcmp (a b:N) : N :=
  if Z.ltb (toZ 32 a) (toZ 32 b) then 0xffffffff else if Z.ltb (toZ 32 b) (toZ 32 a) then 1 else 0.


(* MOV EDX,-1; SETG AL; MOVZX EAX,AL; CMOVL EAX,EDX with the CMOVL taken:
   the OR with the (zero) upper half of the SETG result is just -1 *)
Lemma cmovl_wrap: forall (c d:bool),
  N.lor 4294967295 (N.land (if c then (if d then 0 else 1) else 0) 18446744069414584320) = 4294967295.
Proof. intros c d. destruct c, d; reflexivity. Qed.

Lemma dword_load_off: forall (m:memory) p k, m Ⓓ[p ⊕ k] = m Ⓓ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

(* K words compared equal; then either all n words were compared (result 0)
   or word K differs (result wcmp l[K] r[K]) *)
Definition wmemcmp_result (m l r n rax:N) :=
  exists K, weq_prefix m l r K /\
    ((K = n /\ rax = 0) \/
     (K < n /\ m Ⓓ[l ⊕ 4*K] <> m Ⓓ[r ⊕ 4*K] /\
      rax = wcmp (m Ⓓ[l ⊕ 4*K]) (m Ⓓ[r ⊕ 4*K]))).

Definition wmemcmp_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x134f47 | 0x134f4a => true
  | _ => false end | _ => false end.

Definition wmemcmp_post (s0:store) (m l r n:N) (s:store) :=
  wmemcmp_result m l r n (s R_RAX) /\
  s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wmemcmp_invs (s0:store) (m l r n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x134f00 => Some (s V_MEM64 = m /\ s R_RDI = l /\ s R_RSI = r /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134f2c => Some (exists k, k <= n /\ weq_prefix m l r k /\
                      s R_RDX = n - k /\ s R_RDI = l ⊕ 4*k /\ s R_RSI = r ⊕ 4*k /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x134f47 | 0x134f4a => Some (wmemcmp_post s0 m l r n s)
  | _ => None
  end | _ => None end.

Theorem wmemcmp_correct:
  forall prog s t s' x' m l r n
         (WMEMCMP: wmemcmp_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x134f00, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (L: s R_RDI = l) (R: s R_RSI = r) (Nn: s R_RDX = n),
  satisfies_all prog (wmemcmp_invs s m l r n) wmemcmp_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m l r n WMEMCMP ENTRY MDL MEM L R Nn.
  assert (LB: l < 2^64) by (rewrite <- L; apply (MDL R_RDI 64); reflexivity).
  assert (RB: r < 2^64) by (rewrite <- R; apply (MDL R_RSI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wmemcmp_amd64); [exact WMEMCMP| |].
    intros a s1 t1 EXIT NOCODE. unfold wmemcmp_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m l r n MDL MEM L R Nn LB RB NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemcmp_welltyped. intro MDL1.
  clear - PRE MDL1 LB RB NB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [L [R [Nn [RSP CS]]]]].
    repeat x64_step.
    exists 0. split. lia. split. intros i I. lia.
    split. rewrite N.sub_0_r. assumption.
    split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption. assumption.
    split. rewrite N.mul_0_r, N.add_0_r, N.mod_small by assumption. assumption.
    conj_tac.
  - destruct PRE as [k [KN [SP [RDX [RDI [RSI [MEM [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?dword_load_off in *.
    all: lazymatch goal with
    | |- exists _, _ =>
      (* equal words: advance *)
      exists (k + 1); split; [amlia|];
      split; [intros i I; destruct (N.lt_ge_cases i k); [apply SP; assumption|];
              replace i with k by lia; first [sassumption | symmetry; sassumption]|];
      split; [amlia|]; split; [amlia|]; split; [amlia|]; conj_tac
    | |- wmemcmp_result _ _ _ _ 0 /\ _ =>
      (* n words compared: 0 *)
      split; [exists k; split; [exact SP|]; left; split; [lia|reflexivity]|]; conj_tac
    | _ =>
      (* first difference *)
      split; [|conj_tac];
      exists k; split; [exact SP|]; right; split; [amlia|];
      split; [intro E; lazymatch type of E with ?x = ?y =>
                match goal with H: x <> y |- _ => exact (H E) | H: y <> x |- _ => exact (H (eq_sym E)) end end|];
      unfold wcmp;
      set (a := m Ⓓ[l ⊕ 4*k]) in *; set (b := m Ⓓ[r ⊕ 4*k]) in *;
      assert (A: a < 2^32) by apply getmem_bound;
      assert (B: b < 2^32) by apply getmem_bound;
      clearbody a b; arith_only;
      s32_norm a; s32_norm b; s32_msub_norm; try rewrite cmovl_wrap; flags_finish
    end.
Qed.
