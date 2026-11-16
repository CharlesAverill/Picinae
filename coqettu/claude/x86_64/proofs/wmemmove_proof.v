(* wmemmove -- copy an array of wide characters, areas may overlap (musl x86_64, C)

   SEMANTICS
   ---------
   musl's wmemmove (src/string/wmemmove.c) is

       wchar_t *d0 = d;
       if (d == s) return d;
       if ((uintptr_t)d-(uintptr_t)s < n * sizeof *d)
           while (n--) d[n] = s[n];
       else
           while (n--) *d++ = *s++;
       return d0;

   d == s returns at once.  Otherwise d - s (unsigned, modulo 2^64) < 4n
   selects the backward loop (index RDX counting down), and any larger
   distance the forward loop (index RAX counting up).  The theorem covers
   all three paths, with overlapping or disjoint areas: lib/x64_wcopy.v
   shows that each loop never reads a word it has already overwritten.

   SPECIFICATION (man 3 wmemmove, Linux man-pages 6.9.1)
   -----------------------------------------------------

     SYNOPSIS
            #include <wchar.h>

            wchar_t *wmemmove(wchar_t dest[.n], const wchar_t src[.n], size_t n);

     DESCRIPTION
            The  wmemmove()	function  is  the wide-character equivalent of the mem‐
            move(3) function.  It copies n wide characters from the	array  starting
            at src to the array starting at dest.  The arrays may overlap.

            The  programmer must ensure that there is room for at least n wide char‐
            acters at dest.

     RETURN VALUE
            wmemmove() returns dest.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            wmemmove at 0x3c420 (Ghidra image base 0x100000: 0x13c420)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/wmemmove_amd64.v.
   Model:   This specification and proof were written by Claude Fable 5.1
            (claude-fable-5-1), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = d, RSI = src, RDX = n; m = memory on entry.
            Precondition: 4n < 2^63.  The areas may overlap arbitrarily.
   Output:  At the RET (0x13c452): RAX = d; the n 32-bit words at d equal the
            n words at src as they were on entry, and every byte outside the
            4n bytes at d is unchanged (wmoved); RSP and RBX, RBP, R12-R15
            are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.wmemmove_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_wcopy.
Open Scope N.

Ltac amlia := arith_only; unfold msub in *; change (2^64) with 18446744073709551616 in *;
  change (2^63) with 9223372036854775808 in *; lia.

Theorem wmemmove_nwc: forall s2 s1, wmemmove_amd64 s1 = wmemmove_amd64 s2.
Proof. reflexivity. Qed.

Theorem wmemmove_welltyped: welltyped_prog x64typctx wmemmove_amd64.
Proof. exact welltyped. Qed.

Definition wmemmove_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x13c452 => true
  | _ => false end | _ => false end.

Definition wmemmove_post (s0:store) (m d src n:N) (s:store) :=
  s R_RAX = d /\ wmoved m (s V_MEM64) d src n /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

Definition wmemmove_invs (s0:store) (m d src n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x13c420 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* backward loop: d is less than 4n bytes past src *)
  | 0x13c44a => Some (exists k, k <= n /\ s R_RDX = k /\ wcpb m (s V_MEM64) d src k n /\
                      msub 64 d src < 4*n /\
                      s R_RDI = d /\ s R_RSI = src /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* forward loop: d is at least 4n bytes past src *)
  | 0x13c46a => Some (exists k, k <= n /\ s R_RAX = k /\ wcpf m (s V_MEM64) d src k /\
                      4*n <= msub 64 d src /\
                      s R_RDI = d /\ s R_RSI = src /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x13c452 => Some (wmemmove_post s0 m d src n s)
  | _ => None
  end | _ => None end.

Theorem wmemmove_correct:
  forall prog s t s' x' m d src n
         (WMEMMOVE: wmemmove_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x13c420, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (S: s R_RSI = src) (Nn: s R_RDX = n)
         (N63: 4*n < 2^63),
  satisfies_all prog (wmemmove_invs s m d src n) wmemmove_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d src n WMEMMOVE ENTRY MDL MEM D S Nn N63.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  assert (DB: d < 2^64) by (rewrite <- D; apply (MDL R_RDI 64); reflexivity).
  assert (SB: src < 2^64) by (rewrite <- S; apply (MDL R_RSI 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=wmemmove_amd64); [exact WMEMMOVE| |].
    intros a s1 t1 EXIT NOCODE. unfold wmemmove_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d src n MDL MEM D S Nn N63 NB DB SB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply wmemmove_welltyped. intro MDL1.
  clear - PRE MDL1 N63 NB DB SB. rename t1 into t.
  destruct_inv 64 PRE.
  - destruct PRE as [MEM [D [S [Nn [RSP CS]]]]].
    repeat x64_step. all: bc_norm.
    all: lazymatch goal with
    | |- context [wcpb] =>
      (* d <> src and d - src < 4n: copy backward from word n *)
      assert (DS: msub 64 d src < 4*n) by amlia;
      exists n; split; [lia|]; split; [reflexivity|];
      split; [rewrite MEM; apply wcpb_empty|]; split; [exact DS|]; conj_tac
    | |- context [wcpf] =>
      (* d - src >= 4n: copy forward from word 0 *)
      assert (DS: 4*n <= msub 64 d src) by amlia;
      exists 0; split; [lia|]; split; [reflexivity|];
      split; [rewrite MEM; apply wcpf_empty|]; split; [exact DS|]; conj_tac
    | _ =>
      (* d = src: nothing to do *)
      split; [sreflexivity|]; split; [rewrite MEM, BC; apply wmoved_refl|]; conj_tac
    end.
  - destruct PRE as [k [KN [RDX [WC [DS [D [S [RSP CS]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: lazymatch goal with
    | |- exists _, _ =>
      assert (K0: 0 < k) by lia;
      exists (k - 1); split; [lia|]; split; [amlia|];
      split;
      [ apply (wcpb_store m (s1 V_MEM64) d src k n (d + (k ⊖ 1)*4) _ WC); [exact K0 | exact KN | exact N63 | amlia |];
        rewrite N.mod_small by apply (getmem_bound 64 LittleE 4);
        replace (src + (k ⊖ 1)*4) with (src + 4*(k-1)) by amlia;
        rewrite <- (getmem_mod_l 64 LittleE 4 (s1 V_MEM64) (src + 4*(k-1)));
        exact (wcpb_src m (s1 V_MEM64) d src k n WC K0 KN DS N63)
      | split; [exact DS|]; conj_tac ]
    | _ =>
      replace k with 0 in WC by lia;
      split; [sreflexivity|]; split; [exact (wcpb_moved m (s1 V_MEM64) d src n WC)|]; conj_tac
    end.
  - destruct PRE as [k [KN [RAX [WC [DS [D [S [Nn [RSP CS]]]]]]]]].
    repeat x64_step. all: bc_norm.
    all: lazymatch goal with
    | |- exists _, _ =>
      assert (KL: k < n) by lia;
      exists (k + 1); split; [lia|]; split; [rewrite N.add_comm; apply N.mod_small; lia|];
      split;
      [ apply (wcpf_store m (s1 V_MEM64) d src k (d + k*4) _ WC); [lia | f_equal; lia |];
        rewrite N.mod_small by apply (getmem_bound 64 LittleE 4);
        replace (src + k*4) with (src + 4*k) by lia;
        rewrite <- (getmem_mod_l 64 LittleE 4 (s1 V_MEM64) (src + 4*k));
        exact (wcpf_src m (s1 V_MEM64) d src k n WC KL DS N63)
      | split; [exact DS|]; conj_tac ]
    | _ =>
      replace k with n in WC by lia;
      split; [sreflexivity|]; split; [exact (wcpf_moved m (s1 V_MEM64) d src n WC)|]; conj_tac
    end.
Qed.
