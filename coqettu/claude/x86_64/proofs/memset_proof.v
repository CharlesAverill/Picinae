(* memset -- fill memory with a constant byte (musl x86_64 assembly)

   SEMANTICS
   ---------
   musl implements memset for x86_64 in hand-written assembly
   (src/string/x86_64/memset.s).  It first forms the 8-byte broadcast of
   c8 = c mod 256 with MOVZX + IMUL by 0x0101010101010101.  Then:
   * n <= 126: it stores c8 at s and s+n-1, and, as long as n exceeds 2, 6,
     14, 30 and 62 respectively, a pair of 2-, 4-, 8-, 2x8- and 4x8-byte
     stores growing from both ends (head stores at s+1, s+3, s+7, ...; tail
     stores ending at s+n-1, s+n-3, ...).  The pieces overlap, and for each n
     they cover exactly [s, s+n).
   * n > 126: it stores 8 bytes at s+n-8.  If s is 16-byte aligned it then
     runs REP STOSQ for n/8 quadwords from s; otherwise it stores 16 bytes at
     s, advances to the next 16-byte boundary s+a (a = -s mod 16) and runs
     REP STOSQ for (n-a)/8 quadwords from there.
   It returns s.  The proof tracks the exact set of offsets written so far
   (fil, lib/x64_fill_sets.v) through every overlapping store and through the
   REP STOSQ iterations (the lifter models REP as a self-loop).

   SPECIFICATION (man 3 memset, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            void *memset(void s[.n], int c, size_t n);

     DESCRIPTION
            The memset() function fills the first n bytes of the memory area
            pointed to by s with the constant byte c.

     RETURN VALUE
            The memset() function returns a pointer to the memory area s.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            memset at 0x66095 (Ghidra image base 0x100000: 0x166095)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/memset_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, RSI = c (only c mod 256 matters), RDX = n; m = memory on
            entry; the direction flag DF is clear (an ABI requirement at
            every call).  No other precondition: in particular s+n may wrap
            around the address space.
   Output:  At either RET (0x166124, 0x166142):  RAX = s; RSP is unchanged;
            RBX, RBP, R12-R15 are unchanged; and the memory is `filled`:
            the byte at s+i (mod 2^64) is c mod 256 for every i < n, and every
            other byte equals its value in m.
   Scope:   The theorem holds for any program containing memset's lifted
            instructions (memset_amd64 ⊆2 prog), so it composes with callers.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.memset_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_memcpy_sets CoqEtTu.lib.x64_fill_sets CoqEtTu.lib.x64_abi.
Open Scope N.

Definition memset_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x166124 | 0x166142 => true
  | _ => false end | _ => false end.

Definition memset_post (s0:store) (m:memory) (d c n:N) (s:store) :=
  s R_RAX = d /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\
  filled m (s V_MEM64) d (c mod 2^8) n.

Definition memset_invs (s0:store) (m:memory) (d c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x166095 => Some (s V_MEM64 = m /\ s R_RDI = d /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ s R_DF = 0 /\ callee_saved_eq s0 s)
  | 0x16613c => Some (exists a h q i,
                      s R_RCX = q - i /\ i <= q /\ s R_RDI = d ⊕ (a + 8*i) /\
                      s R_R8 = d /\ bytes_are (s R_RAX) 8 (c mod 2^8) /\
                      s R_DF = 0 /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s /\
                      a <= h /\ h <= 16 /\ 16 <= n /\ a + 8*q <= n /\ n <= a + 8*q + 8 /\
                      fil m (s V_MEM64) d (c mod 2^8)
                        (fun j => j < h \/ n - 8 <= j < n \/ a <= j < a + 8*i))
  | 0x166124 | 0x166142 => Some (memset_post s0 m d c n s)
  | _ => None
  end | _ => None end.

Theorem memset_nwc: forall s2 s1, memset_amd64 s1 = memset_amd64 s2.
Proof. reflexivity. Qed.

Theorem memset_welltyped: welltyped_prog x64typctx memset_amd64.
Proof. exact welltyped. Qed.

Theorem memset_correct:
  forall prog s t s' x' m d c n
         (MEMSET: memset_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x166095, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (D: s R_RDI = d) (C: s R_RSI = c) (Nn: s R_RDX = n)
         (DF: s R_DF = 0),
  satisfies_all prog (memset_invs s m d c n) memset_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m d c n MEMSET ENTRY MDL MEM D C Nn DF.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=memset_amd64); [exact MEMSET| |].
    intros a s1 t1 EXIT NOCODE. unfold memset_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m d c n MDL MEM D C Nn DF NB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; try assumption; apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memset_welltyped. intro MDL1.
  clear - PRE MDL1 NB. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [D [C [Nn [RSP [DF CS]]]]]].
    Time repeat x64_step.
    all: assert (DB: d < 2^64) by (rewrite <- D; apply (MDL1 R_RDI 64); reflexivity).
    Time all: bc_norm.
    all: try (rewrite (N.mod_small n (2^32)) in * by (change (2^32) with 4294967296; lia)).
    all: try (exfalso; lia).
    Time all: try (split; [reflexivity|]; split; [assumption|]; split; [callee_saved_tac|];
      first [ rewrite MEM; split; [intros; lia | reflexivity]
            | eapply fil_filled; [|fil_chain d];
              let i := fresh "i" in let Hi := fresh "Hi" in
              intro i; cbv beta; split;
              [intro Hi; repeat destruct Hi as [Hi|Hi]; lia | intro Hi; lia] ]; fail).
    all: change (2^64) with 18446744073709551616 in *.
    + (* aligned: REP STOSQ from d, after the tail store *)
      exists 0, 0, (n >> 3), 0.
      rewrite N.shiftr_div_pow2. change (2^3) with 8.
      pose proof (N.div_mod n 8 ltac:(discriminate)) as DM.
      pose proof (N.mod_lt n 8 ltac:(discriminate)) as ML.
      split. lia. split. lia.
      split. rewrite N.mul_0_r, !N.add_0_r, N.mod_small by lia. reflexivity.
      split. reflexivity. split. fil_side. split. assumption. split. assumption.
      split. callee_saved_tac.
      split. lia. split. lia. split. lia. split. lia. split. lia.
      eapply fil_equiv; [|fil_chain d].
      intro j. cbv beta. split; intro Hj; repeat destruct Hj as [Hj|Hj]; lia.
    + (* unaligned: two head stores, then REP STOSQ from the 16-aligned d + a *)
      set (a := msub 4 0 d) in *.
      assert (A: a < 16) by apply (msub_lt 4).
      assert (NA: n ⊖ a = n - a).
        rewrite msub_nowrap; rewrite !N.mod_small; lia.
      rewrite NA, N.shiftr_div_pow2. change (2^3) with 8.
      exists a, 16, ((n - a) / 8), 0.
      pose proof (N.div_mod (n - a) 8 ltac:(discriminate)) as DM.
      pose proof (N.mod_lt (n - a) 8 ltac:(discriminate)) as ML.
      split. lia. split. lia.
      split. rewrite N.mul_0_r, N.add_0_r. reflexivity.
      split. reflexivity. split. fil_side. split. assumption. split. assumption.
      split. callee_saved_tac.
      split. lia. split. lia. split. lia. split. lia. split. lia.
      eapply fil_equiv; [|fil_chain d].
      intro j. cbv beta. split; intro Hj; repeat destruct Hj as [Hj|Hj]; lia.
  - (* REP STOSQ *)
    destruct PRE as [a [h [q [i [RCX [IQ [RDI [R8 [RAX [DF [RSP [CS [AH [H16 [N16 [AQ [QN FIL]]]]]]]]]]]]]]]]].
    assert (RCXB: q - i < 2^64) by (rewrite <- RCX; apply (MDL1 R_RCX 64); reflexivity).
    x64_step'. all: repeat x64_step.
    all: bc_norm.
    all: change (2^64) with 18446744073709551616 in *.
    + (* RCX = 0: every offset below n is filled *)
      split. reflexivity. split. assumption. split. callee_saved_tac.
      eapply fil_filled; [|exact FIL].
      intro j. cbv beta. split; intro Hj; [repeat destruct Hj as [Hj|Hj]; lia | lia].
    + (* one more quadword at offset a + 8i *)
      exists a, h, q, (i + 1).
      split. rewrite msub_nowrap; rewrite !N.mod_small; lia.
      split. lia.
      split. f_equal. lia.
      split. assumption. split. assumption. split. reflexivity. split. assumption.
      split. callee_saved_tac.
      split. lia. split. lia. split. lia. split. lia. split. lia.
      eapply fil_equiv; [|eapply (fil_store m (s1 V_MEM64) d _ _ (a + 8*i) 8 _ (s1 R_RAX));
        [exact FIL | | reflexivity | lia | f_equal; lia | assumption]].
        intro j. cbv beta. split; intro Hj; repeat destruct Hj as [Hj|Hj]; lia.
        intros j Hj. cbv beta in Hj. repeat destruct Hj as [Hj|Hj]; lia.
Qed.
