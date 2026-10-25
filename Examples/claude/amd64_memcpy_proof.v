(* memcpy -- copy memory area

   SEMANTICS
   ---------
   memcpy(dest, src, n) copies n bytes from src to dest and returns dest.  This
   is glibc's SSE2 implementation.  The plain symbol memcpy@GLIBC_2.2.5 enters
   it at 0x1c4870; binaries linked against glibc >= 2.14 use
   memcpy@@GLIBC_2.14, an IFUNC that selects among implementations like this
   one at load time.  Small sizes are copied without loops, using pairs of
   possibly overlapping head and tail moves:
     n = 0: nothing;  n = 1: byte;  n = 2..3: byte + word;
     n = 4..7: two dwords;  n = 8..15: two qwords;
     n = 16..32: two 16-byte SSE moves;  n = 33..64: four 16-byte moves.
   Larger sizes take loops, rep movsb, or non-temporal stores; this proof
   covers n <= 64.  On these paths every load happens before any store, so the
   copy is correct even when src and dest overlap (memmove semantics), which is
   stronger than the man page requires.

   The lifted program (memcpy_amd64.v) contains the memcpy entry plus the
   shared body at 0x1c4980, lifted together with global addresses.

   SPECIFICATION (man 3 memcpy, Linux man-pages, Ubuntu 22.04)
   -------------------------------------------------------------

     SYNOPSIS
            #include <string.h>
            void *memcpy(void *restrict dest, const void *restrict src, size_t n);

     DESCRIPTION
            The memcpy() function copies n bytes from memory area src to memory area
            dest.  The memory areas must not overlap.  Use memmove(3) if the memory
            areas do overlap.

     RETURN VALUE
            The memcpy() function returns a pointer to dest.

   PROVENANCE
   ----------
   Binary:  /lib/x86_64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.12
            sha256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9
            symbol memcpy@GLIBC_2.2.5 (= __memmove_sse2_unaligned_erms code paths) at 0x1c4870 (Ghidra image base 0x100000)
   Lifter:  Ghidra 11.4.2 (headless) + pcode2coq (branch claude/amd64-fixes),
            driven by lifter/lift.sh; see memcpy_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = dest, RSI = src, RDX = n with n <= 64; m = memory on entry.
   Output:  On return, RAX = dest, and the final memory m' satisfies
              m'[dest + i] = m[src + i]   for every i < n, and
              m'[b] = m[b]                for every byte b outside dest[0, n)
            (1-byte reads, addresses mod 2^64).  No non-overlap precondition
            is needed for these sizes.
   Frame:   RSP is unchanged at every RET, so control returns to the caller's
            return address.  No callee-saved register (RBX, RBP, R12-R15) is
            modified.
 *)

Require Import Picinae_amd64.
Require Import memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Import ListNotations.
Open Scope N.

Theorem memcpy_nwc: forall s2 s1, memcpy_amd64 s1 = memcpy_amd64 s2.
Proof. reflexivity. Qed.

Theorem memcpy_welltyped: welltyped_prog x64typctx memcpy_amd64.
Proof. Picinae_typecheck. Qed.

Theorem memcpy_preserves_callee_saved:
  forall v, In v [R_RBX; R_RBP; R_R12; R_R13; R_R14; R_R15] ->
  forall_endstates memcpy_amd64 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.

(* RET instructions of the n <= 64 paths. *)
Definition memcpy_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 => true
  | _ => false
  end | _ => false end.

Definition postcondition (m d s n rsp:N) (s':store) :=
  s' R_RAX = d /\ s' R_RSP = rsp /\ copied m (s' V_MEM64) d s n.

Definition memcpy_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1853552 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                     st R_RSP = rsp)
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 => Some (postcondition m d s n rsp st)
  (* entries of the n > 64 paths: unreachable under the precondition n <= 64 *)
  | 1854000 | 1854064 => Some False
  | _ => None
  end | _ => None end.

(* Ghidra lifts a 16-byte MOVUPS load as four dword loads. *)
Lemma xmm_dwords:
  forall (m:memory) a a4 a8 a12,
  a4 mod 2^64 = (a + 4) mod 2^64 -> a8 mod 2^64 = (a + 8) mod 2^64 ->
  a12 mod 2^64 = (a + 12) mod 2^64 ->
  m Ⓓ[a12] << 96 .| (m Ⓓ[a8] << 64 .| (m Ⓓ[a4] << 32 .| m Ⓓ[a])) = m Ⓧ[a].
Proof.
  intros m a a4 a8 a12 H4 H8 H12.
  rewrite <- (getmem_mod_l _ _ _ _ a4), <- (getmem_mod_l _ _ _ _ a8), <- (getmem_mod_l _ _ _ _ a12), H4, H8, H12, !getmem_mod_l.
  change (getmem 64 LittleE 16 m a) with (getmem 64 LittleE (4+12) m a).
  rewrite getmem_split.
  change (getmem 64 LittleE 12 m (a+4)) with (getmem 64 LittleE (4+8) m (a+4)).
  rewrite getmem_split.
  change (getmem 64 LittleE 8 m (a+4+4)) with (getmem 64 LittleE (4+4) m (a+4+4)).
  rewrite getmem_split. unfold cbits.
  rewrite <- !N.add_assoc. simpl (4 + 4). simpl (4 + (4 + 4)).
  rewrite !N.shiftl_lor, !N.shiftl_shiftl, <- !N.lor_assoc. reflexivity.
Qed.

(* Rewrite the four-dword form of a 16-byte value into a 16-byte load. *)
Ltac pack_xmm :=
  repeat match goal with
  |- context [getmem 64 LittleE 4 ?m ?a12 << 96 .| (getmem 64 LittleE 4 ?m ?a8 << 64 .|
              (getmem 64 LittleE 4 ?m ?a4 << 32 .| getmem 64 LittleE 4 ?m ?a))] =>
    rewrite (xmm_dwords m a a4 a8 a12) by mod64
  end.

(* Peel byte reads through a chain of stores, case-splitting on coverage. *)
Theorem memcpy_correct_small:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 1853552, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (SMALL: n <= 64),
  satisfies_all memcpy_amd64 (memcpy_invs m d s n rsp) memcpy_exit ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1 SMALL. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [D [S [Nn RSP]]]].
  repeat x64_step.
  (* turn the size tests into arithmetic facts *)
  all: repeat match goal with
       | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
       | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
       | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
       | H: (_ <=? _) = true |- _ => apply N.leb_le in H
       | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
       end.
  all: rewrite ?(N.mod_small n (2^32)) in * by (change (2^32) with 4294967296; lia).
  all: try (exfalso; lia).
  all: try (match goal with |- False =>
         repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                              | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
         cbn in *; first [discriminate | lia] end).
  all: split; [reflexivity|]; split; [assumption|].
  all: try rewrite MEM.
  all: pack_xmm.
  (* n < 4: the signed size tests are decided by evaluating them *)
  all: try (assert (N4: n < 4) by lia;
            assert (NS: n = 0 \/ n = 1 \/ n = 2 \/ n = 3) by lia;
            destruct NS as [ -> | [ -> | [ -> | -> ]]];
            repeat match goal with H: context [msub 32 _ _] |- _ => vm_compute in H end;
            try discriminate).
  all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                            | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end.
  all: repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                            | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.
  all: try discriminate.
  all: first
    [ apply copy_0 | apply copy_b
    | apply copy_w_b; lia
    | apply copy_th; lia | apply copy_ht; lia | apply copy_4x16; lia ].
Time Qed.

(* n = 65..128: eight 16-byte loads, then eight stores (RET at 0x1c4a6f).
   Every load precedes every store, so overlap is again allowed. *)
Definition memcpy_exit_mid (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 | 1854063 => true
  | _ => false
  end | _ => false end.

Definition memcpy_invs_mid (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1853552 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                     st R_RSP = rsp)
  | 1853595 | 1853903 | 1853916 | 1853936 | 1853964 | 1854063 => Some (postcondition m d s n rsp st)
  (* entry of the n > 128 paths: unreachable under n <= 128 *)
  | 1854064 => Some False
  | _ => None
  end | _ => None end.

Theorem memcpy_correct_mid:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 1853552, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp) (MID: 64 < n <= 128),
  satisfies_all memcpy_amd64 (memcpy_invs_mid m d s n rsp) memcpy_exit_mid ((x',s')::t).
Proof.
  intros. apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.

  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1 MID. rename t1 into t.
  destruct_inv 64 PRE.

  destruct PRE as [MEM [D [S [Nn RSP]]]].
  repeat x64_step.
  all: repeat match goal with
       | H: (_ <? _) = true |- _ => apply N.ltb_lt in H
       | H: (_ <? _) = false |- _ => apply N.ltb_ge in H
       | H: (_ =? _) = true |- _ => apply N.eqb_eq in H
       | H: (_ =? _) = false |- _ => apply N.eqb_neq in H
       | H: (_ <=? _) = true |- _ => apply N.leb_le in H
       | H: (_ <=? _) = false |- _ => apply N.leb_gt in H
       end.
  all: rewrite ?(N.mod_small n (2^32)) in * by (change (2^32) with 4294967296; lia).
  all: try (exfalso; lia).
  all: try (match goal with |- False =>
         repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                              | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end;
         cbn in *; first [discriminate | lia] end).
  all: repeat match goal with H: context [if ?a <? ?b then _ else _] |- _ => destruct (N.ltb_spec a b)
                            | H: context [if ?a =? ?b then _ else _] |- _ => destruct (N.eqb_spec a b) end.
  all: repeat match goal with H: context [N.lor] |- _ => progress cbn [N.lor N.lxor] in H
                            | H: context [N.lxor] |- _ => progress cbn [N.lor N.lxor] in H end.
  all: try discriminate; try (exfalso; lia).
  all: split; [reflexivity|]; split; [assumption|].
  all: try rewrite MEM.
  all: pack_xmm.
  all: apply copy_8x16; lia.
Time Qed.
