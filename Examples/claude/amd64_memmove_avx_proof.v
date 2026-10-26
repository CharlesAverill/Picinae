(* memmove / memcpy -- AVX implementation, sizes up to 256 bytes

   SEMANTICS
   ---------
   __memmove_avx_unaligned_erms(dest, src, n) copies n bytes from src to
   dest and returns dest.  On machines with AVX (and without AVX-512 or
   FSRM preferences), glibc's IFUNC resolvers select it for both memmove
   and memcpy (and mempcpy enters it a few bytes earlier).  It is the second
   most-used libc function in our Firefox profile.

   Up to 256 bytes it copies without loops: it loads the head and the tail
   of the source into registers, then stores them, so every load happens
   before any store and the copy is correct even when the areas overlap:
     n = 0: nothing;  n = 1: byte;  n = 2..3: word tail + byte head;
     n = 4..7: two dwords;  n = 8..15: two qwords;  n = 16..31: two XMM;
     n = 32..64: two YMM;  n = 65..128: four YMM;  n = 129..256: eight YMM.
   Above 64 bytes it first compares n with __x86_rep_movsb_threshold (the
   quadword at 0x31a3f8 in the Ghidra image) and takes the REP MOVSB path
   when n is larger.  Above 256 bytes it uses 128-byte loops (forward or
   backward, by overlap), REP MOVSB, or non-temporal stores; those paths
   are not covered here.

   SPECIFICATION (man 3 memmove, Linux man-pages, Ubuntu 22.04)
   --------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            void *memmove(void *dest, const void *src, size_t n);

     DESCRIPTION
            The memmove() function copies n bytes from memory area src to memory
            area dest.  The memory areas may overlap: copying takes place as
            though the bytes in src are first copied into a temporary array that
            does not overlap src or dest, and the bytes are then copied from the
            temporary array to dest.

     RETURN VALUE
            The memmove() function returns a pointer to dest.

   memcpy(3) has the same contract except that the areas must not overlap,
   so this theorem also covers memcpy.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            __memmove_avx_unaligned_erms at 0x2a0840 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            canonical temporaries, entry rebased to 0; see memmove_avx_amd64.v.
            The RIP-relative load of the threshold keeps its Ghidra address.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src, RDX = n with n <= 256; m = memory on entry,
            and n <= m[0x31a3f8] (8 bytes).  glibc never sets the REP MOVSB
            threshold below 8 vector lengths (256 bytes for AVX), so this holds
            for every n <= 256 in a running process.
   Output:  On return, RAX = dest, and the final memory m' satisfies
              m'[dest + i] = m[src + i]   for every i < n, and
              m'[b] = m[b]                for every byte b outside dest[0, n)
            (1-byte reads, addresses mod 2^64).  No non-overlap precondition.
   Frame:   RSP is unchanged at every RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Import ListNotations.
Open Scope N.

Theorem memmove_avx_nwc: forall s2 s1, memmove_avx_amd64 s1 = memmove_avx_amd64 s2.
Proof. reflexivity. Qed.

Theorem memmove_avx_welltyped: welltyped_prog x64typctx memmove_avx_amd64.
Proof. Picinae_typecheck. Qed.

Theorem memmove_avx_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates memmove_avx_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* RET instructions of the n <= 256 paths. *)
Definition mm_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 46 | 84 | 97 | 118 | 144 | 181 | 308 => true
  | _ => false
  end | _ => false end.

Definition postcondition (m d s n rsp:N) (s':store) :=
  s' R_RAX = d /\ s' R_RSP = rsp /\ copied m (s' V_MEM64) d s n.

Definition mm_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
               st R_RSP = rsp)
  | 46 | 84 | 97 | 118 | 144 | 181 | 308 => Some (postcondition m d s n rsp st)
  (* entries of the n > 256 paths and of REP MOVSB: unreachable *)
  | 309 | 704 => Some False
  | _ => None
  end | _ => None end.

(* The store address d - L + n is offset n - L from d (L up to 256). *)
Lemma addr_tail_w:
  forall x L n, L <= n -> L <= 256 -> (msub 64 x L + n) mod 2^64 = (x + (n - L)) mod 2^64.
Proof.
  intros x L n LN L256. unfold msub. rewrite N.add_mod_idemp_l by discriminate.
  rewrite (N.mod_small L) by (eapply N.le_lt_trans; [exact L256 | reflexivity]).
  assert (L < 2^64) by (eapply N.le_lt_trans; [exact L256 | reflexivity]).
  replace (x + (2^64 - L) + n) with (x + (n - L) + 1 * 2^64) by lia.
  apply N.mod_add. discriminate.
Qed.

(* As chain in amd64_memcpy_lemmas.v, for the wider tail offsets. *)
Ltac chain_w :=
  eapply cpy_copied; cycle 1;
  [ repeat (eapply cpy_store;
              [ | | | | first [ apply addr_0 | apply addr_head | apply addr_tail_w; lia ]
                      | first [ apply addr_0 | apply addr_head | apply addr_tail_w; lia ] ]);
    try apply cpy_empty;
    try (intros ? ?; change (2^64) with 18446744073709551616; lia);
    change (2^64) with 18446744073709551616; lia
  | intro i; split; intro Hi; lia ].

(* Head move then tail move of L bytes covers n bytes when L <= n <= 2L. *)
Lemma copy_ht_w:
  forall (m:memory) d s n L, 0 < L <= 32 -> L <= n <= 2*L ->
  copied m (setmem 64 LittleE L (setmem 64 LittleE L m d (getmem 64 LittleE L m s))
                   (msub 64 d L + n) (getmem 64 LittleE L m (msub 64 s L + n))) d s n.
Proof. intros. chain_w. Qed.

(* n = 65..128: two YMM head moves, two YMM tail moves. *)
Lemma copy_4x32:
  forall (m:memory) d s n, 64 < n <= 128 ->
  copied m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 m
              d (getmem 64 LittleE 32 m s))
              (32 + d) (getmem 64 LittleE 32 m (32 + s)))
              (msub 64 d 32 + n) (getmem 64 LittleE 32 m (msub 64 s 32 + n)))
              (msub 64 d 64 + n) (getmem 64 LittleE 32 m (msub 64 s 64 + n))) d s n.
Proof. intros. chain_w. Qed.

(* n = 129..256: four YMM head moves, four YMM tail moves. *)
Lemma copy_8x32:
  forall (m:memory) d s n, 128 < n <= 256 ->
  copied m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32
           (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 m
              d (getmem 64 LittleE 32 m s))
              (32 + d) (getmem 64 LittleE 32 m (32 + s)))
              (64 + d) (getmem 64 LittleE 32 m (64 + s)))
              (96 + d) (getmem 64 LittleE 32 m (96 + s)))
              (msub 64 d 32 + n) (getmem 64 LittleE 32 m (msub 64 s 32 + n)))
              (msub 64 d 64 + n) (getmem 64 LittleE 32 m (msub 64 s 64 + n)))
              (msub 64 d 96 + n) (getmem 64 LittleE 32 m (msub 64 s 96 + n)))
              (msub 64 d 128 + n) (getmem 64 LittleE 32 m (msub 64 s 128 + n))) d s n.
Proof. intros. chain_w. Qed.

(* Drop everything but arithmetic facts before calling lia. *)
Ltac arith_only :=
  repeat match goal with H: ?T |- _ =>
    lazymatch T with
    | context [setmem] => clear H
    | context [MemAcc] => clear H
    | models _ _ => clear H
    | _ = _ :> store => clear H
    | context [V_MEM64] => clear H
    end
  end.

Theorem memmove_avx_correct_small:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (SMALL: n <= 256) (THR: n <= m Ⓠ[0x31a3f8]),
  satisfies_all memmove_avx_amd64 (mm_invs m d s n rsp) mm_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memmove_avx_welltyped. intro MDL1.
  clear - PRE MDL1 SMALL THR. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [D [S [Nn RSP]]]].
  repeat x64_step.
  all: repeat match goal with H: MemAcc _ _ _ _ _ |- _ => clear H end.
  all: repeat match goal with
       | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
       | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
       | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
       | H: (_ <=? _) = true |- _ => apply N.leb_le in H
       | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
       end.
  all: repeat match goal with H: context [?x mod 2^32], SM: ?x <= 256 |- _ =>
         rewrite (N.mod_small x (2^32)) in H by (change (2^32) with 4294967296; clear - SM; lia) end.
  all: try (exfalso; arith_only; lia).
  (* n < 4: the signed size test is decided by evaluating it at n = 0..3 *)
  all: try (match goal with H: context [slt 32], N4: ?x < 4 |- _ =>
         assert (NS: x = 0 \/ x = 1 \/ x = 2 \/ x = 3) by (clear - N4; lia);
         destruct NS as [ -> | [ -> | [ -> | -> ]]]; vm_compute in H; try discriminate H; clear H end).
  all: repeat match goal with H: context [if _ then _ else _] |- _ =>
         change (2^7) with 128 in H; change (2^8) with 256 in H;
         repeat match type of H with
         | context [if ?a <? ?b then _ else _] => destruct (N.ltb_spec a b)
         | context [if ?a =? ?b then _ else _] => destruct (N.eqb_spec a b)
         end;
         vm_compute in H; first [discriminate H | clear H]
       end.
  all: try (exfalso; arith_only; lia).
  all: split; [reflexivity|]; split; [assumption|].
  all: try (match goal with |- copied _ (_ V_MEM64) _ _ _ => rewrite MEM; apply copy_0 end).
  all: arith_only.
  all: lazymatch goal with
       | |- copied _ (_ V_MEM64) _ _ _ => rewrite MEM; apply copy_0
       | |- copied _ (setmem _ _ 1 (setmem _ _ 2 _ _ _) _ _) _ _ _ => apply copy_w_b; lia
       | |- copied _ (setmem _ _ 1 _ _ _) _ _ _ => apply copy_b
       | |- copied _ (setmem _ _ 4 (setmem _ _ 4 _ (msub _ _ _ + _) _) _ _) _ _ _ => apply copy_th; lia
       | |- copied _ (setmem _ _ 32 (setmem _ _ 32 (setmem _ _ 32 (setmem _ _ 32
                       (setmem _ _ 32 _ _ _) _ _) _ _) _ _) _ _) _ _ _ =>
           change (2^7) with 128; apply copy_8x32; lia
       | |- copied _ (setmem _ _ 32 (setmem _ _ 32 (setmem _ _ 32 (setmem _ _ 32 _ _ _) _ _) _ _) _ _) _ _ _ =>
           apply copy_4x32; lia
       | |- _ => apply copy_ht_w; lia
       end.
Time Qed.
