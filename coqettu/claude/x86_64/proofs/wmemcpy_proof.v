(* wmemcpy -- copy an array of wide characters (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wmemcpy (src/string/wmemcpy.c) is

       wchar_t *a = d;
       while (n--) *d++ = *s++;
       return a;

   The binary keeps the word index in RAX and copies one 32-bit word per
   iteration while RAX != RDX.

   SPECIFICATION (man 3 wmemcpy, Linux man-pages 6.9.1)
   ----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>

            wchar_t *wmemcpy(wchar_t dest[restrict .n],
     			const wchar_t src[restrict .n],
     			size_t n);

     DESCRIPTION
            The wmemcpy() function is the wide-character equivalent of the memcpy(3)
            function.  It copies n wide characters from the array starting at src to
            the array starting at dest.

            The  arrays may not overlap; use wmemmove(3) to copy between overlapping
            arrays.

            The programmer must ensure that there is room for at least n wide  char‐
            acters at dest.

     RETURN VALUE
            wmemcpy() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wmemcpy at 0x3c3f0 (Ghidra image base 0x100000: 0x13c3f0)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wmemcpy_amd64.v.
   Model:   This specification and proof were written by Claude Fable 5.1
            (claude-fable-5-1), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; m = memory on entry.
            Precondition (wmemcpy_ok): the 4n bytes at d and the 4n bytes at
            src do not overlap, and 4n < 2^63.  (The proof only uses that d
            is at least 4n bytes past src modulo 2^64, which non-overlap
            implies; see lib/x64_wcopy.v.)
   Output:  At the RET (0x13c412): RAX = d; the n 32-bit words at d equal the
            n words at src as they were on entry, and every byte outside the
            4n bytes at d is unchanged (wmoved); RSP and RBX, RBP, R12-R15
            are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wmemcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_wcopy.
Open Scope N.

Theorem wmemcpy_nwc: forall s2 s1, wmemcpy_amd64 s1 = wmemcpy_amd64 s2.
Proof. reflexivity. Qed.

Theorem wmemcpy_welltyped: welltyped_prog x64typctx wmemcpy_amd64.
Proof. exact welltyped. Qed.

(* the 4n bytes at d and at src are disjoint, and 4n < 2^63 *)
Definition wmemcpy_ok (d src n:N) := ~ overlap 64 d (4*n) src (4*n) /\ 4*n < 2^63.

Definition wmemcpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c412 => true
  | _ => false end | _ => false end.

Definition wmemcpy_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\ wmoved m (s V_MEM64) d src n /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wmemcpy_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c3f0 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c40a => Some (exists k, k <= n /\ s R_RAX = k /\ wcpf m (s V_MEM64) d src k /\
                      s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c412 => Some (wmemcpy_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Theorem wmemcpy_correct:
  forall prog s t s' x' m d src n
         (WMEMCPY: wmemcpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c3f0, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (OK: wmemcpy_ok d src n),
  satisfies_all prog (wmemcpy_invs s m d src n) wmemcpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WMEMCPY ENTRY MDL MEM D S Nn OK.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wmemcpy_amd64); [exact WMEMCPY| |].
    intros a s1 t1 EXIT NOCODE. unfold wmemcpy_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn OK NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemcpy_welltyped. intro MDL1.
  clear - PRE MDL1 OK NB. rename t1 into t.
  destruct OK as [NOV N63].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step.
    exists 0. conj_tac. lia. rewrite MEM. apply wcpf_empty.
  - destruct PRE as [k [KN [RAX [WC [D [S [Nn [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: lazymatch goal with
    | |- exists _, _ =>
      assert (KL: k < n) by (arith_only; mlia);
      assert (DS: 4*n <= msub 64 d src) by (apply noverlap_msub; [exact NOV | lia]);
      exists (k + 1); split; [lia|]; split; [rewrite N.add_comm; apply N.mod_small; lia|];
      split;
      [ apply (wcpf_store m (s1 V_MEM64) d src k (d + k*4) _ WC); [lia | f_equal; lia |];
        rewrite N.mod_small by apply (getmem_bound 64 LittleE 4);
        replace (src + k*4) with (src + 4*k) by lia;
        rewrite <- (getmem_mod_l 64 LittleE 4 (s1 V_MEM64) (src + 4*k));
        exact (wcpf_src m (s1 V_MEM64) d src k n WC KL DS N63)
      | conj_tac ]
    | _ =>
      assert (KE: k = n) by (arith_only; mlia);
      split; [sreflexivity|]; split; [rewrite <- KE; exact (wcpf_moved m (s1 V_MEM64) d src k WC)|];
      conj_tac
    end.
Qed.
