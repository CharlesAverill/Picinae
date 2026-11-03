(* Finite representation tests, not instruction/function correctness proofs.
   Synthetic program addresses/lengths below have no binary provenance.
   Only the operand requirements in the e15 metadata come from the exact ELF. *)
Require Import Picinae_amd64_avx512.
Require Import Picinae_amd64.
From Stdlib Require Import NArith List.
Import AMD64_AVX512 ListNotations.
Open Scope N.

Definition all_vectors :=
  [Z0; Z1; Z2; Z3; Z4; Z5; Z6; Z7; Z8; Z9; Z10; Z11; Z12; Z13; Z14; Z15;
   Z16; Z17; Z18; Z19; Z20; Z21; Z22; Z23; Z24; Z25; Z26; Z27; Z28; Z29; Z30; Z31].
Definition all_masks := [K0; K1; K2; K3; K4; K5; K6; K7].

Example physical_widths :
  map (fun r => avx512typctx (R_ZMM r)) all_vectors = repeat (Some 512) 32 /\
  map (fun r => avx512typctx (R_K r)) all_masks = repeat (Some 64) 8.
Proof. vm_compute. split; reflexivity. Qed.

Example old_context_unchanged :
  Picinae_amd64.x64typctx Picinae_amd64.R_YMM0 = Some 256 /\
  Picinae_amd64.x64typctx Picinae_amd64.R_YMM15 = Some 256 /\
  Picinae_amd64.x64typctx Picinae_amd64.R_RAX = avx512typctx R_RAX.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example finite_write_widths :
  forallb (fun r => forallb (fun w =>
    match typchk_stmt (vector_write_zero_upper w r (Word 0 (vector_bits w)))
                       avx512typctx avx512typctx with
    | Some _ => true | None => false end) [W128; W256; W512]) all_vectors = true /\
  forallb (fun r => forallb (fun w =>
    match typchk_stmt (mask_write_zero_upper w r (Word 0 (mask_bits w)))
                       avx512typctx avx512typctx with
    | Some _ => true | None => false end) [M8; M16; M32; M64]) all_masks = true.
Proof. vm_compute. split; reflexivity. Qed.

(* One byte at lane 63, with other bytes passed through. This deliberately
   tests mask bit 63 and the merge/zero choice in ordinary typed IL, without
   implementing any whole masked instruction or masked memory access. *)
Definition masked_lane63 (zeroing:bool) : exp :=
  Concat (Ite (Extract 63 63 (Var (R_K K1))) (Word 0xaa 8)
              (if zeroing then Word 0 8 else Extract 511 504 (Var (R_ZMM Z31))))
         (Extract 503 0 (Var (R_ZMM Z31))).

Definition state_fixture : program := fun _ a =>
  match a with
  | 0 => Some (1, xmm_write_preserve Z0 (vector_read W128 Z1))
  | 1 => Some (1, vector_write_zero_upper W128 Z1 (vector_read W128 Z0))
  | 2 => Some (1, vector_write_zero_upper W256 Z16 (vector_read W256 Z31))
  | 3 => Some (1, vector_write_zero_upper W512 Z31 (vector_read W512 Z16))
  | 4 => Some (1, Move (R_ZMM Z31) (masked_lane63 false))
  | 5 => Some (1, Move (R_ZMM Z31) (masked_lane63 true))
  | 6 => Some (1, mask_write_zero_upper M16 K0 (mask_read M16 K7))
  | 7 => Some (1, mask_write_zero_upper M64 K7 (mask_read M64 K0))
  | 8 => Some (1, Move (R_ZMM Z16) (Load (Var V_MEM64) (Var R_RSI) LittleE 64))
  | 9 => Some (1, Move V_MEM64
      (Store (Var V_MEM64) (Var R_RDI) (vector_read W512 Z16) LittleE 64))
  | _ => None
  end.

Theorem state_fixture_welltyped : welltyped_prog avx512typctx state_fixture.
Proof.
  unfold state_fixture, xmm_write_preserve, vector_write_zero_upper,
    vector_zero_upper, vector_read, vector_bits, masked_lane63,
    mask_write_zero_upper, mask_read, mask_bits.
  Picinae_typecheck.
Qed.

(* These queries check the same typing algorithm used on the fixtures,
   including rejection of a 256-bit replacement of a physical ZMM. *)
Example reject_short_physical_write :
  typchk_stmt (Move (R_ZMM Z16) (Word 0 256)) avx512typctx avx512typctx = None.
Proof. vm_compute. reflexivity. Qed.
Example reject_bad_view_write :
  typchk_stmt (vector_write_zero_upper W128 Z16 (Word 0 256))
    avx512typctx avx512typctx = None.
Proof. vm_compute. reflexivity. Qed.
Example reject_out_of_bounds_read :
  typchk_exp (Extract 512 0 (Var (R_ZMM Z31))) avx512typctx = None.
Proof. vm_compute. reflexivity. Qed.

Definition seed : store := fun v =>
  match v with
  | R_ZMM Z0 | R_ZMM Z16 => 2^511 + 2^200 + 5
  | R_ZMM Z31 => 2^511 + 7
  | R_K K0 => 0
  | R_K K1 => 2^63 + 1
  | R_K K7 => 2^63 + 0x12345
  | _ => 0
  end.
Definition value s e := fst
  (feval_exp noe_setop noe_typop avx512typctx s e (fun _ => 0) []).
Definition after q s r : option N :=
  match fexec_stmt noe_setop noe_typop avx512typctx q s (fun _ => 0) [] with
  | FIS l (FIExit None) [] => Some (updstr s l vupdate r)
  | _ => None
  end.

Example aliased_reads :
  (value seed (vector_read W128 Z16), value seed (vector_read W256 Z16),
   value seed (vector_read W512 Z16)) = (5, 2^200 + 5, 2^511 + 2^200 + 5).
Proof. vm_compute. reflexivity. Qed.
Example legacy_preserves_upper :
  after (xmm_write_preserve Z0 (Word 9 128)) seed (R_ZMM Z0) =
    Some (2^511 + 2^200 + 9).
Proof. vm_compute. reflexivity. Qed.
Example narrow_writes_clear_upper :
  (after (vector_write_zero_upper W128 Z16 (Word 9 128)) seed (R_ZMM Z16),
   after (vector_write_zero_upper W256 Z16 (Word (2^255+9) 256)) seed (R_ZMM Z16))
  = (Some 9, Some (2^255+9)).
Proof. vm_compute. reflexivity. Qed.
Example full_write_keeps_top_bit :
  after (vector_write_zero_upper W512 Z31 (vector_read W512 Z16)) seed (R_ZMM Z31)
    = Some (2^511 + 2^200 + 5).
Proof. vm_compute. reflexivity. Qed.
Example mask_top_bit_is_data :
  value seed (mask_read M64 K1) = 2^63+1 /\
  after (mask_write_zero_upper M16 K7 (Word 0x2345 16)) seed (R_K K7) = Some 0x2345.
Proof. vm_compute. split; reflexivity. Qed.
Example unmasked_is_not_k0 :
  (evex_writemask K0, evex_writemask K1, value seed (mask_read M64 K0)) =
  (None, Some K1, 0).
Proof. vm_compute. reflexivity. Qed.
Example mask_merge_and_zero :
  let disabled := vupdate seed (R_K K1) 1 in
  (value seed (masked_lane63 false), value disabled (masked_lane63 false),
   value disabled (masked_lane63 true)) = (0xaa * 2^504 + 7, 2^511 + 7, 7).
Proof. vm_compute. reflexivity. Qed.
Example other_slot_is_unchanged :
  after (vector_write_zero_upper W128 Z16 (Word 9 128)) seed (R_ZMM Z31) =
    Some (2^511+7).
Proof. vm_compute. reflexivity. Qed.
