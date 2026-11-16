(* wcscpy -- copy a wide-character string (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wcscpy (src/string/wcscpy.c) is

       wchar_t *a = d;
       while (( *d++ = *s++));
       return a;

   The binary copies one 32-bit word per iteration (byte offset in RAX) and
   stops after copying a zero word.

   SPECIFICATION (man 3 wcscpy, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <wchar.h>

            wchar_t *wcscpy(wchar_t *restrict dest, const wchar_t *restrict src);

     DESCRIPTION
            The  wcscpy() function is the wide-character equivalent of the strcpy(3)
            function.  It copies the wide-character string pointed to  by  src,  in‐
            cluding	the  terminating  null	wide  character	 (L'\0'),  to the array
            pointed to by dest.

            The strings may not overlap.

            The programmer must ensure that there is room for at least wcslen(src)+1
            wide characters at dest.

     RETURN VALUE
            wcscpy() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wcscpy at 0x3c350 (Ghidra image base 0x100000: 0x13c350)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wcscpy_amd64.v.
   Model:   This specification and proof were written by Claude Fable 5.1
            (claude-fable-5-1), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src; m = memory on entry.
            Precondition (wcscpy_ok m d src L): src holds L nonzero 32-bit
            words followed by a zero word (L = wcslen(src)); the 4(L+1) bytes
            at d and the 4(L+1) bytes at src do not overlap; 4(L+1) < 2^63.
   Output:  At the RET (0x13c371): RAX = d; the L+1 words at d (including
            the terminator) equal the L+1 words at src, and every byte
            outside the 4(L+1) bytes at d is unchanged (wmoved); RSP and RBX,
            RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wcscpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_wcopy.
Open Scope N.

Theorem wcscpy_nwc: forall s2 s1, wcscpy_amd64 s1 = wcscpy_amd64 s2.
Proof. reflexivity. Qed.

Theorem wcscpy_welltyped: welltyped_prog x64typctx wcscpy_amd64.
Proof. exact welltyped. Qed.

(* src is a wide string of length L (L nonzero words, then a zero word); the
   4(L+1) bytes at d and at src are disjoint; 4(L+1) < 2^63 *)
Definition wcscpy_ok (m d src L:N) :=
  nzw m src L /\ m Ⓓ[src ⊕ 4*L] = 0 /\
  ~ overlap 64 d (4*(L+1)) src (4*(L+1)) /\ 4*(L+1) < 2^63.

Lemma word_nz_lt: forall (m:memory) s k L, k <= L -> m Ⓓ[s ⊕ 4*L] = 0 -> m Ⓓ[s ⊕ 4*k] <> 0 -> k < L.
Proof.
  intros m s k L KL Z NZ. destruct (N.lt_ge_cases k L) as [H|H]. exact H.
  exfalso. replace k with L in NZ by lia. exact (NZ Z).
Qed.

Lemma word_z_eq: forall (m:memory) s k L, k <= L -> nzw m s L -> m Ⓓ[s ⊕ 4*k] = 0 -> k = L.
Proof.
  intros m s k L KL NZ Z. destruct (N.lt_ge_cases k L) as [H|H].
  exfalso. exact (NZ k H Z). lia.
Qed.

Definition wcscpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c371 => true
  | _ => false end | _ => false end.

Definition wcscpy_post (s0:store) (m d src L:N) (s:store) :=
  s R_RAX = d /\ wmoved m (s V_MEM64) d src (L+1) /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wcscpy_invs (s0:store) (m d src L:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c350 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c360 => Some (exists k, k <= L /\ s R_RAX = 4*k /\ wcpf m (s V_MEM64) d src k /\
                      s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c371 => Some (wcscpy_post s0 m d src L s)
  | _ => None
  end | _ => None end.

Theorem wcscpy_correct:
  forall prog s t s' x' m d src L
         (WCSCPY: wcscpy_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c350, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src)
         (OK: wcscpy_ok m d src L),
  satisfies_all prog (wcscpy_invs s m d src L) wcscpy_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src L WCSCPY ENTRY MDL MEM D S OK.
  eapply satisfies_all_pmono with (p1:=wcscpy_amd64); [exact WCSCPY| |].
    intros a s1 t1 EXIT NOCODE. unfold wcscpy_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src L MDL MEM D S OK START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wcscpy_welltyped. intro MDL1.
  clear - PRE MDL1 OK. rename t1 into t.
  destruct OK as [NZ [ZL [NOV N63]]].
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [RSP CS]]]].
    repeat x64_step.
    exists 0. split. lia. split. reflexivity. split. rewrite MEM. apply wcpf_empty. conj_tac.
  - destruct PRE as [k [KL [RAX [WC [D [S [RSP CS]]]]]]].
    assert (DS: 4*(L+1) <= msub 64 d src) by (apply noverlap_msub; [exact NOV | lia]).
    repeat x64_step. all: bc_norm.
    all: assert (SW: s1 V_MEM64 Ⓓ[src + 4*k] = m Ⓓ[src ⊕ 4*k])
      by (rewrite <- (getmem_mod_l 64 LittleE 4 (s1 V_MEM64) (src + 4*k));
          exact (wcpf_src m (s1 V_MEM64) d src k (L+1) WC ltac:(lia) DS N63)).
    all: rewrite SW in *.
    all: lazymatch goal with
    | |- exists _, _ =>
      (* src[k] <> 0: k < L, copy on *)
      assert (KL': k < L) by (apply (word_nz_lt m src k L KL ZL); sassumption);
      exists (k + 1); split; [lia|]; split; [rewrite N.mod_small by lia; lia|];
      split;
      [ apply (wcpf_store m (s1 V_MEM64) d src k (d + 4*k) _ WC); [lia | reflexivity |];
        apply N.mod_small, (getmem_bound 64 LittleE 4)
      | conj_tac ]
    | _ =>
      (* src[k] = 0: k = L, done *)
      assert (KE: k = L) by (apply (word_z_eq m src k L KL NZ); sassumption);
      split; [sreflexivity|];
      split;
      [ replace (1 + L) with (k + 1) by lia; apply wcpf_moved;
        apply (wcpf_store m (s1 V_MEM64) d src k (d + 4*k) _ WC); [lia | reflexivity |];
        apply N.mod_small, (getmem_bound 64 LittleE 4)
      | conj_tac ]
    end.
Qed.
