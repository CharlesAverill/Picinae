(* decoder/lifter for ARMv7 *)

Require Export Picinae_armv7.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import List.
Require Import Lia.
Open Scope Z.

Definition Z1 := 1.
Definition Z2 := 2.
Definition Z3 := 3.
Definition Z4 := 4.
Definition Z5 := 5.
Definition Z6 := 6.
Definition Z7 := 7.
Definition Z8 := 8.
Definition Z9 := 9.
Definition Z10 := 10.
Definition Z11 := 11.
Definition Z12 := 12.
Definition Z13 := 13.
Definition Z14 := 14.
Definition Z15 := 15.
Definition Z16 := 16.
Definition Z17 := 17.
Definition Z18 := 18.
Definition Z19 := 19.
Definition Z20 := 20.
Definition Z21 := 21.
Definition Z22 := 22.
Definition Z23 := 23.
Definition Z24 := 24.
Definition Z25 := 25.
Definition Z26 := 26.
Definition Z27 := 27.
Definition Z28 := 28.
Definition Z29 := 29.
Definition Z30 := 30.
Definition Z31 := 31.
Definition Z32 := 32.
Definition Z4095 := 0xfff.

Variant arm_data_op :=
  | ARM_AND
  | ARM_EOR
  | ARM_SUB
  | ARM_RSB
  | ARM_ADD
  | ARM_ADC
  | ARM_SBC
  | ARM_RSC
  | ARM_TST
  | ARM_TEQ
  | ARM_CMP
  | ARM_CMN
  | ARM_ORR
  | ARM_MOV (* also called LSL, LSR, ASR, RRX, ROR depending on shift, but functionally the same *)
  | ARM_BIC
  | ARM_MVN.
Variant arm_mul_op :=
  | ARM_MUL
  | ARM_MLA
  | ARM_UMAAL
  | ARM_MLS
  | ARM_UMULL
  | ARM_UMLAL
  | ARM_SMULL
  | ARM_SMLAL.
Variant arm_hmul_op :=
  | ARM_SMLABB
  | ARM_SMLAWB
  | ARM_SMULWB
  | ARM_SMLALBB
  | ARM_SMULBB.
Variant arm_sat_op :=
  | ARM_QADD
  | ARM_QSUB
  | ARM_QDADD
  | ARM_QDSUB.
Variant arm_mem_op :=
  (* unpriviledged load/stores have a different mnemonic but can be determined by P and W fields *)
  | ARM_LDR
  | ARM_STR
  | ARM_LDRB
  | ARM_STRB.
Variant arm_xmem_op :=
  | ARM_STRH
  | ARM_LDRH
  | ARM_LDRD
  | ARM_LDRSB
  | ARM_STRD
  | ARM_LDRSH.
Variant arm_memm_op :=
  | ARM_STMDA
  | ARM_LDMDA
  | ARM_STMDB (* called PUSH when wback and rn=sp *)
  | ARM_LDMDB
  | ARM_STMIA
  | ARM_LDMIA (* called POP when wback rn=sp *)
  | ARM_STMIB
  | ARM_LDMIB.
Variant arm_sync_size :=
  | ARM_sync_word
  | ARM_sync_doubleword
  | ARM_sync_byte
  | ARM_sync_halfword.
Variant arm_pas_op :=
  | ARM_ADD16
  | ARM_ASX
  | ARM_SAX
  | ARM_SUB16
  | ARM_ADD8
  | ARM_SUB8.
Variant arm_pas_type :=
  | ARM_pas_normal
  | ARM_pas_saturating
  | ARM_pas_halving.
Variant arm_rev_op :=
  | ARM_REV
  | ARM_REV16
  | ARM_RBIT
  | ARM_REVSH.
Variant arm_extend_op := (* non-A variants have Rn=15 *)
  | ARM_XTAB16
  | ARM_XTAB
  | ARM_XTAH.
Variant arm_vfp_op :=
  | ARM_VMLA
  | ARM_VNMLA
  | ARM_VMUL
  | ARM_VADD
  | ARM_VSUB
  | ARM_VDIV
  | ARM_VFNMA
  | ARM_VFMA.
Variant arm_vfp_other_op :=
  | ARM_VMOV
  | ARM_VABS
  | ARM_VNEG
  | ARM_VSQRT.

Variant arm_inst :=
  (* causes undefined instruction exception *)
  | ARM_UNDEFINED
  (* no behaviour guaranteed *)
  | ARM_UNPREDICTABLE
  (* decoding not implemented yet, treat as unpredictable *)
  | idk

  (* data processing register: A5.2.1, pg A5-195 *)
  | ARM_data_r (op: arm_data_op) (cond S Rn Rd imm5 type Rm: Z)
  (* data processing register-shifted-register: A5.2.2, pg A5-196 *)
  | ARM_data_rsr (op: arm_data_op) (cond S Rn Rd Rs type Rm: Z)
  (* data processing immediate: A5.2.3, pg A5-197 *)
  | ARM_data_i (op: arm_data_op) (cond S Rn Rd imm12: Z)
  (* 16bit mov (movw/movt): A5.2, pg A5-194 *)
  | ARM_MOV_WT (is_w: bool) (cond imm4 Rd imm12: Z)
  (* multiply/multiply accumulate: A5.2.5, pg A5-200 *)
  | ARM_mul (op: arm_mul_op) (cond S Rd_RdHi Ra_RdLo Rm Rn: Z)
  | ARM_hmul (op: arm_hmul_op) (cond Rd Ra Rm M N Rn: Z)
  (* synchronization load: A5.2.10, pg A5-203 *)
  | ARM_sync_l (size: arm_sync_size) (cond Rn Rt: Z)
  (* synchronization store: A5.2.10, pg A5-203 *)
  | ARM_sync_s (size: arm_sync_size) (cond Rn Rd Rt: Z)
  (* miscellaneous instructions: A5.2.12, pg A5-205 *)
  | ARM_BX (cond Rm: Z)
  | ARM_BLX_r (cond Rm: Z)
  | ARM_BXJ (cond Rm: Z)
  | ARM_CLZ (cond Rd Rm: Z)
  | ARM_BKPT (cond imm12 imm4: Z)
  (* saturating add/sub: A5.2.6, pg A5-200 *)
  | ARM_sat (op: arm_sat_op) (cond Rn Rd Rm: Z)
  (* hints: A5.2.11, pg A5-204 *)
  | ARM_hint (cond op2: Z)
  (* extra load/store: A5.2.8, pg A5-201 *)
  | ARM_extra_ls_i (op: arm_xmem_op) (cond P U W Rn Rt imm4H imm4L: Z)
  | ARM_extra_ls_r (op: arm_xmem_op) (cond P U W Rn Rt Rm: Z)
  (* load/store immediate: A5.3, pg A5-206 *)
  | ARM_ls_i (op: arm_mem_op) (cond P U W Rn Rt imm12: Z)
  (* load/store register: A5.3, pg A5-206 *)
  | ARM_ls_r (op: arm_mem_op) (cond P U W Rn Rt imm5 type Rm: Z)

  (* parallel add/sub: A5.4.1/5.4.2, pg A5-208/209 *)
  | ARM_pas (is_signed: bool) (type: arm_pas_type) (op: arm_pas_op) (cond Rn Rd Rm: Z)
  (* reversal *)
  | ARM_rev (op: arm_rev_op) (cond Rd Rm: Z)
  | ARM_extend (is_signed: bool) (op: arm_extend_op) (cond Rn Rd rotate Rm: Z)

  (* load/store multiple: A5.5, pg A5-212 *)
  | ARM_lsm (op: arm_memm_op) (cond W Rn register_list: Z)
  (* branch: A5.5, pg A5-212 *)
  | ARM_B (cond imm24: Z)
  | ARM_BL (cond imm24: Z)
  | ARM_BLX_i (H imm24: Z)

  | ARM_SVC (cond imm24: Z)

  (* mcr, mcr2, mrc, mrc2 (cond=15 for ___2 insts) *)
  | ARM_coproc_m (is_cr: bool) (cond opc1 CRn Rt coproc opc2 CRm: Z)
  | ARM_vls (is_load is_single: bool) (cond U D Rn Vd imm8: Z)
  | ARM_vlsm (is_load is_single: bool) (cond P U D W Rn Rd imm8: Z)

  | ARM_VMOV_i (cond D imm4H Vd sz imm4L: Z)
  | ARM_VMOV_r2 (is_single: bool) (cond op Rt2 Rt M Vm: Z)
  | ARM_VMOV_r1 (cond op Vn Rt N: Z)
  | ARM_vfp (op: arm_vfp_op) (cond D Vn Vd sz N Op M Vm: Z)
  | ARM_VCMP (cond D Vd sz E M Vm: Z)
  | ARM_VMRS (cond Rt: Z)
  | ARM_VCVT_fpi (cond D opc2 Vd sz op M Vm: Z)
  | ARM_VCVT_fpf (cond D op U Vd sf sx i imm4: Z)
  | ARM_VCVT_ds (cond D Vd sz M Vm: Z)
  | ARM_vfp_other (op: arm_vfp_other_op) (cond D Vd sz M Vm: Z)

  | ARM_PLD_i (U R Rn imm12: Z)
  | ARM_PLD_r (U R Rn imm5 type Rm: Z)
      .
Definition zxbits z i j := Z.shiftr z i mod Z.shiftl Z1 (Z.max Z0 (j - i)).
Lemma zxbits_eq:
  forall z i j, zxbits z i j = Z_xbits z i j.
Proof.
  intros. unfold zxbits, Z_xbits. rewrite Z.shiftl_1_l. reflexivity.
Qed.
Definition bitb z b := zxbits z b (b + Z1).
Notation "x !=? y" := (negb (Z.eqb x y)) (at level 25, left associativity).
Notation "x .| y" := (Z.lor x y) (at level 25, left associativity).
Notation "x << y" := (Z.shiftl x y) (at level 40, left associativity).
Notation "x >> y" := (Z.shiftr x y) (at level 40, left associativity).
Notation "x & y" := (Z.land x y) (at level 40, left associativity).


(********** decoding **********)

Notation armcond z := (zxbits z Z28 Z32) (only parsing).

Definition arm_decode_data_r op z :=
  let cond := armcond z in
  let S := bitb z Z20 in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let imm5 := zxbits z Z7 Z12 in
  let type := zxbits z Z5 Z7 in
  let Rm := zxbits z Z0 Z4 in
  ARM_data_r op cond S Rn Rd imm5 type Rm.
Definition arm_decode_data_rsr op z :=
  let cond := armcond z in
  let S := bitb z Z20 in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let Rs := zxbits z Z8 Z12 in
  let type := zxbits z Z5 Z7 in
  let Rm := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rn =? Z15) || (Rm =? Z15) || (Rs =? Z15) then ARM_UNPREDICTABLE
  else ARM_data_rsr op cond S Rn Rd Rs type Rm.
Definition arm_decode_data_i op z :=
  let cond := armcond z in
  let S := bitb z Z20 in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let imm12 := zxbits z Z0 Z12 in
  ARM_data_i op cond S Rn Rd imm12.
Definition arm_decode_data_rd0 (kind: arm_data_op -> Z -> arm_inst) op z :=
  let Rd := zxbits z Z12 Z16 in
  if (Rd !=? Z0) then ARM_UNPREDICTABLE
  else kind op z.
Definition arm_decode_data_rn0 (kind: arm_data_op -> Z -> arm_inst) op z :=
  let Rn := zxbits z Z16 Z20 in
  if (Rn !=? Z0) then ARM_UNPREDICTABLE
  else kind op z.
Definition arm_decode_data_processing kind z :=
  let op := zxbits z Z21 Z25 in
  (       if (op =?  Z0) then                        kind ARM_AND
  else    if (op =?  Z1) then                        kind ARM_EOR
  else    if (op =?  Z2) then                        kind ARM_SUB
  else    if (op =?  Z3) then                        kind ARM_RSB
  else    if (op =?  Z4) then                        kind ARM_ADD
  else    if (op =?  Z5) then                        kind ARM_ADC
  else    if (op =?  Z6) then                        kind ARM_SBC
  else    if (op =?  Z7) then                        kind ARM_RSC
  else    if (op =?  Z8) then    arm_decode_data_rd0 kind ARM_TST
  else    if (op =?  Z9) then    arm_decode_data_rd0 kind ARM_TEQ
  else    if (op =? Z10) then    arm_decode_data_rd0 kind ARM_CMP
  else    if (op =? Z11) then    arm_decode_data_rd0 kind ARM_CMN
  else    if (op =? Z12) then                        kind ARM_ORR
  else    if (op =? Z13) then    arm_decode_data_rn0 kind ARM_MOV
  else    if (op =? Z14) then                        kind ARM_BIC
  else (* if (op =? Z15) then *) arm_decode_data_rn0 kind ARM_MVN) z.

Definition arm_decode_sat op z :=
  let cond := armcond z in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let Rm := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rn =? Z15) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z12 !=? Z0) then ARM_UNPREDICTABLE
  else ARM_sat op cond Rn Rd Rm.
Definition arm_decode_saturating_add_sub z := (* A5.2.6, pg A5-200 *)
  let op := zxbits z Z21 Z23 in
  if (op =? Z0) then arm_decode_sat ARM_QADD z
  else if (op =? Z1) then arm_decode_sat ARM_QSUB z
  else if (op =? Z2) then arm_decode_sat ARM_QDADD z
  else arm_decode_sat ARM_QDSUB z.

Definition arm_decode_mov_wt is_w z := (* A8.8.103, pg A8-485 (encoding A2) *) (* A8.8.107, pg A8-492 *)
  let cond := armcond z in
  let imm4 := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let imm12 := zxbits z Z0 Z12 in
  if (Rd =? Z15) then ARM_UNPREDICTABLE
  else ARM_MOV_WT is_w cond imm4 Rd imm12.
Definition arm_decode_bx z := (* A8.8.27, pg A8-350 *)
  let cond := armcond z in
  let Rm := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z20 !=? Z4095) then ARM_UNPREDICTABLE
  else ARM_BX cond Rm.
Definition arm_decode_clz z := (* A8.8.33, pg A8-360 *)
  let cond := armcond z in
  let Rd := zxbits z Z12 Z16 in
  let Rm := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z12 !=? Z15) || (zxbits z Z16 Z20 !=? Z15) || (Rd =? Z15) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else ARM_CLZ cond Rd Rm.
Definition arm_decode_bxj z := (* A8.8.28, pg A8-352 *)
  let cond := armcond z in
  let Rm := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z20 !=? Z4095) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else ARM_BXJ cond Rm.
Definition arm_decode_blx_r z := (* A8.8.26, pg A8-348 *)
  let cond := armcond z in
  let Rm := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z20 !=? Z4095) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else ARM_BLX_r cond Rm.
Definition arm_decode_bkpt z := (* A8.8.24, pg A8-344 *)
  let cond := armcond z in
  let imm12 := zxbits z Z8 Z20 in
  let imm4 := zxbits z Z0 Z4 in
  if (cond !=? Z14) then ARM_UNPREDICTABLE
  else ARM_BKPT cond imm12 imm4.
Definition arm_decode_b z := (* A8.8.18, pg A8-332 *)
  let cond := armcond z in
  let imm24 := zxbits z Z0 Z24 in
  ARM_B cond imm24.
Definition arm_decode_bl z := (* A8.8.25, pg A8-346 *)
  let cond := armcond z in
  let imm24 := zxbits z Z0 Z24 in
  ARM_BL cond imm24.
Definition arm_decode_blx_i z := (* A8.8.25, pg A8-346 *)
  let H := bitb z Z24 in
  let imm24 := zxbits z Z0 Z24 in
  ARM_BLX_i H imm24.
Definition arm_decode_misc z := (* A5.2.12, pg A5-205 *)
  let op := zxbits z Z21 Z23 in
  let op1 := zxbits z Z16 Z20 in
  let op2 := zxbits z Z4 Z7 in
  let B := bitb z Z9 in
  if (op2 =? Z0) then
    if (B =? Z1) then
    if (bitb z Z21 =? Z0) then ARM_UNPREDICTABLE (*mrs banked, unpredictable in user mode*)
      else ARM_UNPREDICTABLE (*msr banked, unpredictable in user mode*)
    else
      if (op =? Z0) || (op =? Z2) then idk (*mrs*)
      else if (op =? Z1) then idk (*msr reg*)
      else if (op =? Z3) then idk (*msr reg*)
      else ARM_UNDEFINED
  else if (op2 =? Z1) then
    if (op =? Z1) then arm_decode_bx z
    else if (op =? Z3) then arm_decode_clz z
    else ARM_UNDEFINED
  else if (op2 =? Z2) && (op =? Z1) then arm_decode_bxj z
  else if (op2 =? Z3) && (op =? Z1) then arm_decode_blx_r z
  else if (op2 =? Z5) then arm_decode_saturating_add_sub z
  else if (op2 =? Z6) && (op =? Z3) then ARM_UNPREDICTABLE (*eret, unpredictable in user mode*)
  else if (op2 =? Z7) then
    if (op =? Z1) then arm_decode_bkpt z
    else if (op =? Z2) then ARM_UNDEFINED (*hvc, undefined in user mode*)
    else if (op =? Z3) then ARM_UNDEFINED (*smc, undefined in user mode*)
    else ARM_UNDEFINED
  else ARM_UNDEFINED.

Definition arm_decode_hmul op z :=
  let cond := armcond z in
  let Rd := zxbits z Z16 Z20 in
  let Ra := zxbits z Z12 Z16 in
  let Rm := zxbits z Z8 Z12 in
  let M := bitb z Z6 in
  let N := bitb z Z5 in
  let Rn := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rn =? Z15) || (Rm =? Z15) || (Ra =? Z15) then ARM_UNPREDICTABLE
  else if (match op with | ARM_SMLALBB => Rd =? Ra | ARM_SMULWB | ARM_SMULBB => Ra !=? Z0 | _ => false end) then ARM_UNPREDICTABLE
  else ARM_hmul op cond Rd Ra Rm M N Rn.

Definition arm_decode_halfword_multiply z := (* A5.2.7, pg A5-200,201 *)
  let op1 := zxbits z Z21 Z23 in
  let op := bitb z Z5 in
  if (op1 =? Z0) then arm_decode_hmul ARM_SMLABB z
  else if (op1 =? Z1) then
    if (op =? Z0) then arm_decode_hmul ARM_SMLAWB z
    else arm_decode_hmul ARM_SMULWB z
  else if (op1 =? Z2) then arm_decode_hmul ARM_SMLALBB z
  else arm_decode_hmul ARM_SMULBB z.

Definition arm_decode_mul op z :=
  let cond := armcond z in
  let S := bitb z Z20 in
  let Rd_RdHi := zxbits z Z16 Z20 in
  let Ra_RdLo := zxbits z Z12 Z16 in
  let Rm := zxbits z Z8 Z12 in
  let Rn := zxbits z Z0 Z4 in
  if (Rd_RdHi =? Z15) || (Rn =? Z15) || (Rm =? Z15) || (Ra_RdLo =? Z15) then ARM_UNPREDICTABLE
  else if (match op with | ARM_MUL => Ra_RdLo !=? Z0 | ARM_MLA | ARM_MLS => false | _ => Rd_RdHi =? Ra_RdLo end) then ARM_UNPREDICTABLE
  (* another unpredictable case for version < 6 *)
  else ARM_mul op cond S Rd_RdHi Ra_RdLo Rm Rn.
Definition arm_decode_multiply z := (* A5.2.5, pg A5-200 *)
  let op := zxbits z Z20 Z24 in
  if (op =? Z0) || (op =? Z1) then arm_decode_mul ARM_MUL z
  else if (op =? Z2) || (op =? Z3) then arm_decode_mul ARM_MLA z
  else if (op =? Z4) then arm_decode_mul ARM_UMAAL z
  else if (op =? Z5) then ARM_UNDEFINED
  else if (op =? Z6) then arm_decode_mul ARM_MLS z
  else if (op =? Z7) then ARM_UNDEFINED
  else if (op =? Z8) || (op =? Z9) then arm_decode_mul ARM_UMULL z
  else if (op =? Z10) || (op =? Z11) then arm_decode_mul ARM_UMLAL z
  else if (op =? Z12) || (op =? Z13) then arm_decode_mul ARM_SMULL z
  else (*if (op =? Z14) || (op =? Z15) then*) arm_decode_mul ARM_SMLAL z.

Definition arm_decode_sync_s size z :=
  let cond := armcond z in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let Rt := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rt =? Z15) || (Rn =? Z15) then ARM_UNPREDICTABLE
  else if (Rd =? Rn) || (Rd =? Rt) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z12 !=? Z15) then ARM_UNPREDICTABLE
  else if (match size with ARM_sync_doubleword => true | _ => false end) && ((bitb Rt Z0 =? Z1) || (Rt =? Z14) || (Rd =? Rt + Z1)) then ARM_UNPREDICTABLE
  else ARM_sync_s size cond Rn Rd Rt.
Definition arm_decode_sync_l size z :=
  let cond := armcond z in
  let Rn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  if (Rt =? Z15) || (Rn =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z12 !=? Z15) || (zxbits z Z0 Z4 !=? Z15) then ARM_UNPREDICTABLE
  else if (match size with ARM_sync_doubleword => true | _ => false end) && ((bitb Rt Z0 =? Z1) || (Rt =? Z14)) then ARM_UNPREDICTABLE
  else ARM_sync_l size cond Rn Rt.
Definition arm_decode_sync_primitives z := (* A5.2.10, pg A5-203 *)
  let op := zxbits z Z20 Z24 in (* 3210:
     3=0 - swp/swpb, 3=1 - load/store exclusive
     2:1 - size
     0=0 - store, 0=1 - load *)
  if (bitb op Z3 =? Z0) then idk (* swp/swpb *)
  else
    let size := if (bitb op Z2 =? Z0) then
                  if (bitb op Z1 =? Z0) then ARM_sync_word else ARM_sync_doubleword
                else
                  if (bitb op Z1 =? Z0) then ARM_sync_byte else ARM_sync_halfword in
    if (bitb op Z0 =? Z0) then arm_decode_sync_s size z
    else arm_decode_sync_l size z.

Definition arm_decode_extra_ls_i op z :=
  let cond := armcond z in
  let P := bitb z Z24 in
  let U := bitb z Z23 in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let imm4H := zxbits z Z8 Z12 in
  let imm4L := zxbits z Z0 Z4 in
  let wback := (P =? Z0) || (W =? Z1) in
  if (Rt =? Z15) || (wback && ((Rn =? Z15) || (Rn =? Rt))) then ARM_UNPREDICTABLE
  else if (match op with | ARM_STRD | ARM_LDRD => (wback && (Rn =? Rt + Z1)) || (bitb Rt Z0 =? Z1) || ((P =? Z0) && (W =? Z1)) || (Rt =? Z14) | _ => false end) then ARM_UNPREDICTABLE
  else ARM_extra_ls_i op cond P U W Rn Rt imm4H imm4L.
Definition arm_decode_extra_ls_r op z :=
  let cond := armcond z in
  let P := bitb z Z24 in
  let U := bitb z Z23 in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let Rm := zxbits z Z0 Z4 in
  let wback := (P =? Z0) || (W =? Z1) in
  (* the way the manual expresses this is so unnecessarily confusing and spread out *)
  if (Rt =? Z15) || (Rm =? Z15) || (wback && ((Rn =? Z15) || (Rn =? Rt))) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z12 !=? Z0) then ARM_UNPREDICTABLE
  else if (match op with | ARM_STRD | ARM_LDRD => (wback && (Rn =? Rt + Z1)) || (bitb Rt Z0 =? Z1) || ((P =? Z0) && (W =? Z1)) || (Rt =? Z14) | _ => false end) then ARM_UNPREDICTABLE
  else if (match op with | ARM_LDRD => (Rm =? Rt) || (Rm =? Rt + Z1) | _ => false end) then ARM_UNPREDICTABLE
  else ARM_extra_ls_r op cond P U W Rn Rt Rm.
Definition arm_decode_extra_load_store z :=
  let op2 := zxbits z Z5 Z7 in
  let op1_0 := bitb z Z20 in
  (* op2 - 3 possibilities, 00 is a different category
     op1<0> - 2 possibilities => 3*2 = 6 ops
     4 ops (store half, load half, load signed byte, load signed half) have T variant
     2 ops (store/load dual) have T variant as unpredictable *)
  let kind := if (bitb z Z22 =? Z0) then arm_decode_extra_ls_r else arm_decode_extra_ls_i in
  if (op2 =? Z1) then
    if (op1_0 =? Z0) then kind ARM_STRH z
    else kind ARM_LDRH z
  else if (op2 =? Z2) then
    if (op1_0 =? Z0) then kind ARM_LDRD z
    else kind ARM_LDRSB z
  else if (op2 =? Z3) then
    if (op1_0 =? Z0) then kind ARM_STRD z
    else kind ARM_LDRSH z
  else ARM_UNDEFINED (* unreachable *).

Definition arm_decode_hint z :=
  let cond := armcond z in
  let op2 := zxbits z Z0 Z8 in
  if (op2 =? Z20) && (cond !=? Z14) then ARM_UNPREDICTABLE
  else if (zxbits z Z12 Z16 !=? Z15) || (zxbits z Z8 Z12 !=? Z0) then ARM_UNPREDICTABLE
  else ARM_hint cond op2.
Definition arm_decode_msr_hints z := (* A5.2.11, pg A5-204 *)
  let op := bitb z Z22 in
  let op1 := zxbits z Z16 Z20 in
  let op2 := zxbits z Z0 Z8 in
  if (op =? Z0) then
    if (op1 =? Z0) then arm_decode_hint z
    else idk (*msr imm*)
  else idk (*msr imm*).

Definition arm_decode_data_misc z :=
  let op := bitb z Z25 in
  let op1 := zxbits z Z20 Z25 in
  let op2 := zxbits z Z4 Z8 in
  if (op =? Z0) then
    if (op2 =? Z9) then
      if (bitb z Z24 =? Z0) then arm_decode_multiply z
      else arm_decode_sync_primitives z
    else if (bitb z Z4 =? Z0) || (bitb z Z7 =? Z0) then
      if (op1 =? Z16) || (op1 =? Z18) || (op1 =? Z20) || (op1 =? Z22) then (* op1 = 10xx0 *)
        if (bitb z Z7 =? 0) then arm_decode_misc z
        else arm_decode_halfword_multiply z
      else (* op1 = not 10xx0 *)
        if (bitb op2 Z0 =? Z0) then arm_decode_data_processing arm_decode_data_r z
        else if (bitb op2 Z3 =? Z0) then arm_decode_data_processing arm_decode_data_rsr z
        else ARM_UNDEFINED
    else arm_decode_extra_load_store z
  else (* op = 1 *)
    if (op1 =? Z16) then arm_decode_mov_wt true z
    else if (op1 =? Z20) then arm_decode_mov_wt false z
    else if (op1 =? Z18) || (op1 =? Z22) then arm_decode_msr_hints z (* op1 = 10x10 *)
    else arm_decode_data_processing arm_decode_data_i z. (* op1 = not 10xx0 *)

Definition arm_decode_ls_r op z :=
  let cond := armcond z in
  let P := bitb z Z24 in
  let U := bitb z Z23 in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let imm5 := zxbits z Z7 Z12 in
  let type := zxbits z Z5 Z7 in
  let Rm := zxbits z Z0 Z4 in
  let wback := (P =? Z0) || (W =? Z1) in
  if (Rm =? Z15) || (wback && ((Rn =? Z15) || (Rn =? Rt))) then ARM_UNPREDICTABLE (* also "wback && m == n" if archversion < 6 but we are armv7 *)
  else if (match op with | ARM_STR => false | ARM_LDR => (P =? Z0) && (W =? Z1) | _ => true end) && (Rt =? Z15) then ARM_UNPREDICTABLE
  else ARM_ls_r op cond P U W Rn Rt imm5 type Rm.
Definition arm_decode_ls_i op z :=
  let cond := armcond z in
  let P := bitb z Z24 in
  let U := bitb z Z23 in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let imm12 := zxbits z Z0 Z12 in
  let wback := (P =? Z0) || (W =? Z1) in
  let is_byte := bitb z Z22 =? Z1 in
  if (wback && ((Rn =? Z15) || (Rn =? Rt))) then ARM_UNPREDICTABLE
  else if (match op with | ARM_STR => false | ARM_LDR => (P =? Z0) && (W =? Z1) | _ => true end) && (Rt =? Z15) then ARM_UNPREDICTABLE
  else ARM_ls_i op cond P U W Rn Rt imm12.
Definition arm_decode_load_store z := (* A5.3, pg A5-206 *)
  let A := bitb z Z25 in (* 0 - immediate, 1 - register *)
  let B := bitb z Z4 in (* A=1, B=1 - media inst *)
  let op1 := zxbits z Z20 Z25 in (* 43210: 0=0 - store, 0=1 - load, 2=0 - word, 2=1 - byte *)
  let is_load := bitb op1 Z0 =? Z1 in
  let is_byte := bitb op1 Z2 =? Z1 in
  if (A =? Z1) && (B =? Z1) then ARM_UNDEFINED (* media instructions *)
  else
    let kind := if (A =? Z0) then arm_decode_ls_i else arm_decode_ls_r in
    let op := if (is_load) then
                if (is_byte) then ARM_LDRB else ARM_LDR
              else
                if (is_byte) then ARM_STRB else ARM_STR in
    kind op z.

Definition arm_decode_pas is_signed type op z :=
  let cond := armcond z in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let Rm := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z12 !=? Z15) then ARM_UNPREDICTABLE
  else if (Rd =? Z15) || (Rn =? Z15) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else ARM_pas is_signed type op cond Rn Rd Rm.
Definition arm_decode_parallel_add_sub z :=
  let is_signed := bitb z Z22 =? Z0 in
  let op1 := zxbits z Z20 Z22 in
  let op2 := zxbits z Z5 Z8 in
  let type := if (op1 =? Z1) then Some ARM_pas_normal
              else if (op1 =? Z2) then Some ARM_pas_saturating
              else if (op1 =? Z3) then Some ARM_pas_halving
              else None in
  let op := if (op2 =? Z0) then Some ARM_ADD16
            else if (op2 =? Z1) then Some ARM_ASX
            else if (op2 =? Z2) then Some ARM_SAX
            else if (op2 =? Z3) then Some ARM_SUB16
            else if (op2 =? Z4) then Some ARM_ADD8
            else if (op2 =? Z7) then Some ARM_SUB8
            else None in
  match type, op with
  | Some type, Some op => arm_decode_pas is_signed type op z
  | _, _ => ARM_UNDEFINED
  end.
Definition arm_decode_rev op z :=
  let cond := armcond z in
  let Rd := zxbits z Z12 Z16 in
  let Rm := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z16 Z20 !=? Z15) || (zxbits z Z8 Z12 !=? Z15) then ARM_UNPREDICTABLE
  else ARM_rev op cond Rd Rm.
Definition arm_decode_extend is_signed op z :=
  let cond := armcond z in
  let Rn := zxbits z Z16 Z20 in
  let Rd := zxbits z Z12 Z16 in
  let rotate := zxbits z Z10 Z12 in
  let Rm := zxbits z Z0 Z4 in
  if (Rd =? Z15) || (Rm =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z10 !=? Z0) then ARM_UNPREDICTABLE
  else ARM_extend is_signed op cond Rn Rd rotate Rm.
Definition arm_decode_packing z :=
  let op1 := zxbits z Z20 Z23 in
  let op1'2 := zxbits op1 Z1 Z3 in
  let op1_1 := bitb op1 Z0 in
  let op2 := zxbits z Z5 Z8 in
  let op2_1 := bitb op2 Z0 in
  if (op1'2 =? Z0) then
    if (op2_1 =? Z0) then idk (*pkh*)
    else if (op2 =? Z3) then arm_decode_extend true ARM_XTAB16 z
    else if (op2 =? Z5) then idk (*sel*)
    else ARM_UNDEFINED
  else if (op1'2 =? Z1) then
    if (op2_1 =? Z0) then idk (*ssat*)
    else if (op1_1 =? Z0) then (* op1=010 *)
      if (op2 =? Z1) then idk (*ssat16*)
      else if (op2 =? Z3) then arm_decode_extend true ARM_XTAB z
      else ARM_UNDEFINED
    else (* op1=011 *)
      if (op2 =? Z1) then arm_decode_rev ARM_REV z
      else if (op2 =? Z3) then arm_decode_extend true ARM_XTAH z
      else if (op2 =? Z5) then arm_decode_rev ARM_REV16 z
      else ARM_UNDEFINED
  else if (op1'2 =? Z2) then
    if (op1_1 =? Z0) && (op2 =? Z3) then arm_decode_extend false ARM_XTAB16 z
    else ARM_UNDEFINED
  else (*if (op1'2 =? Z3) then*)
    if (op2_1 =? Z0) then idk (*usat*)
    else if (op1_1 =? Z0) then (* op1=110 *)
      if (op2 =? Z1) then idk (*usat16*)
      else if (op2 =? Z3) then arm_decode_extend false ARM_XTAB z
      else ARM_UNDEFINED
    else (* op1=111 *)
      if (op2 =? Z1) then arm_decode_rev ARM_RBIT z
      else if (op2 =? Z3) then arm_decode_extend false ARM_XTAH z
      else if (op2 =? Z5) then arm_decode_rev ARM_REVSH z
      else ARM_UNDEFINED.

Definition arm_decode_signed_multiply z :=
  let op1 := zxbits z Z20 Z25 in
  idk.
Definition arm_decode_media z :=
  let op1 := zxbits z Z20 Z25 in
  let op1'2 := zxbits op1 Z3 Z5 in
  let op1_3 := zxbits op1 Z0 Z3 in
  let op2 := zxbits z Z5 Z8 in
  if (op1'2 =? Z0) then arm_decode_parallel_add_sub z
  else if (op1'2 =? Z1) then arm_decode_packing z
  else if (op1'2 =? Z2) then arm_decode_signed_multiply z
  else (* if (op1'2 =? Z3) then *)
    if (op1_3 =? Z0) then
      if (op2 =? Z0) then idk (*usad8/usada8*)
      else ARM_UNDEFINED
    else if (op1_3 =? Z2) || (op1_3 =? Z3) then
      if (op2 =? Z2) || (op2 =? Z6) then idk (*sbfx*)
      else ARM_UNDEFINED
    else if (op1_3 =? Z4) || (op1_3 =? Z5) then
      if (op2 =? Z0) || (op2 =? Z4) then idk (*bfc/bfi*)
      else ARM_UNDEFINED
    else if (op1_3 =? Z6) || (op1_3 =? Z7) then
      if (op2 =? Z2) || (op2 =? Z6) then idk (*ubfx*)
      else ARM_UNDEFINED
    else ARM_UNDEFINED.

Definition arm_decode_lsm op z :=
  let cond := armcond z in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let register_list := zxbits z Z0 Z16 in
  if (Rn =? Z15) || (register_list =? Z0 (* bitcount(reglist) < 1 *)) then ARM_UNPREDICTABLE
  else if (W =? Z1) && (bitb z Z20 =? Z1) && (bitb z Rn =? Z1) then ARM_UNPREDICTABLE (* load with wback cannot have Rn set in reg list (allowed before armv7 though) *)
  else ARM_lsm op cond W Rn register_list.
Definition arm_decode_branch_block_transfer z := (* A5.5, pg A5-212 *)
  let op := zxbits z Z20 Z26 in (* 543210:
     5=0 - load store, 5=1 - branch
     4=0 - after, 4=1 - before
     3=0 - decrement, 3=1 - increment
     2=0 - ???, 2=1 - unpredictable in user mode
     1=0 - no write back, 1=1 - write back
     0=0 - store, 0=1 - load *)
  if (bitb op Z5 =? Z0) then
    if (bitb op Z2 =? Z1) then ARM_UNPREDICTABLE (* stm (user reg), ldm (user reg), ldm (exc ret) are unpredictable in user mode *)
    else
      let is_after := bitb op Z4 =? Z0 in
      let is_decrement := bitb op Z3 =? Z0 in
      let is_store := bitb op Z0 =? Z0 in
      let op := match is_after, is_decrement, is_store with
                | true, true, true => ARM_STMDA
                | true, true, false => ARM_LDMDA
                | true, false, true => ARM_STMIA
                | true, false, false => ARM_LDMIA
                | false, true, true => ARM_STMDB
                | false, true, false => ARM_LDMDB
                | false, false, true => ARM_STMIB
                | false, false, false => ARM_LDMIB
                end in
      arm_decode_lsm op z
  else
    if (bitb op Z4 =? Z0) then arm_decode_b z
    else arm_decode_bl z. (* blx_i is unconditional inst *)

Definition arm_decode_svc z :=
  let cond := armcond z in
  let imm24 := zxbits z Z0 Z24 in
  ARM_SVC cond imm24.

Definition arm_decode_coproc_m is_cr z :=
  let cond := armcond z in
  let opc1 := zxbits z Z21 Z23 in
  let CRn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let coproc := zxbits z Z8 Z12 in
  let opc2 := zxbits z Z5 Z8 in
  let CRm := zxbits z Z0 Z4 in
  if (coproc =? Z10) || (coproc =? Z11) then ARM_UNDEFINED
  else if (is_cr) && (Rt =? Z15) then ARM_UNPREDICTABLE
  (* t=13 unpredictable in thumb mode *)
  else ARM_coproc_m is_cr cond opc1 CRn Rt coproc opc2 CRm.
Definition arm_decode_vls is_load z :=
  let is_single := bitb z Z8 =? Z0 in
  let cond := armcond z in
  let U := bitb z Z23 in
  let D := bitb z Z22 in
  let Rn := zxbits z Z16 Z20 in
  let Vd := zxbits z Z12 Z16 in
  let imm8 := zxbits z Z0 Z8 in
  (*unpredictable case in thumb for vstr*)
  ARM_vls is_load is_single cond U D Rn Vd imm8.
Definition arm_decode_vlsm is_load z :=
  let is_single := bitb z Z8 =? Z0 in
  let cond := armcond z in
  let P := bitb z Z24 in
  let U := bitb z Z23 in
  let D := bitb z Z22 in
  let W := bitb z Z21 in
  let Rn := zxbits z Z16 Z20 in
  let Vd := zxbits z Z12 Z16 in
  let imm8 := zxbits z Z0 Z8 in
  let ok := ARM_vlsm is_load is_single cond P U D W Rn Vd imm8 in
  if (Rn =? Z15) && (W =? Z1) (*or not arm mode*) then ARM_UNPREDICTABLE
  else if (is_single) then
    if (imm8 =? Z0) || (imm8 + (Vd << Z1) + D >? Z32) then ARM_UNPREDICTABLE
    else ok
  else
    if (bitb imm8 Z0 =? Z1) then idk (* idk what's going on with FSTMX *)
    else if (imm8 =? Z0) || (imm8 >? Z32) || ((D << Z4) + Vd + (imm8 >> Z1) >? Z32) then ARM_UNPREDICTABLE
    (* TODO: vfpsmallregisterbank??? *)
    else ok.

Definition arm_decode_vreg_ls z :=
  let Opcode := zxbits z Z20 Z25 in
  let o'2 := zxbits Opcode Z3 Z5 in
  let o_2 := zxbits Opcode Z0 Z2 in
  if (o'2 =? Z0) then ARM_UNDEFINED (*64bit transfer*)
  else if (o'2 =? Z1) then
    if (o_2 =? Z0) || (o_2 =? Z2) then arm_decode_vlsm false z
    else arm_decode_vlsm true z
  else if (o'2 =? Z2) then
    if (o_2 =? Z0) then arm_decode_vls false z
    else if (o_2 =? Z1) then arm_decode_vls true z
    else if (o_2 =? Z2) then arm_decode_vlsm false z
    else (*if (o_2 =? Z3) then *) arm_decode_vlsm true z
  else (*if (o'2 =? Z3) then*)
    if (o_2 =? Z0) then arm_decode_vls false z
    else if (o_2 =? Z1) then arm_decode_vls true z
    else ARM_UNDEFINED.

Definition arm_decode_vmov_i z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let imm4H := zxbits z Z16 Z20 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let imm4L := zxbits z Z0 Z4 in
  if (bitb z Z5 !=? Z0) || (bitb z Z7 !=? Z0) then ARM_UNPREDICTABLE
  else ARM_VMOV_i cond D imm4H Vd sz imm4L.

Definition arm_decode_vmov_r2 is_single z :=
  let cond := armcond z in
  let op := bitb z Z20 in
  let Rt2 := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  if (Rt =? Z15) || (Rt2 =? Z15) || (is_single && ((Vm << Z1) + M =? Z31)) then ARM_UNPREDICTABLE
  (* sp reg unpredictable in thumb *)
  else if (op =? Z1) && (Rt =? Rt2) then ARM_UNPREDICTABLE
  else ARM_VMOV_r2 is_single cond op Rt2 Rt M Vm.

Definition arm_decode_vmov_r1 z :=
  let cond := armcond z in
  let op := bitb z Z20 in
  let Vn := zxbits z Z16 Z20 in
  let Rt := zxbits z Z12 Z16 in
  let N := bitb z Z7 in
  if (Rt =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z5 Z7 !=? Z0) || (zxbits z Z0 Z4 !=? Z0) then ARM_UNPREDICTABLE
  else ARM_VMOV_r1 cond op Vn Rt N.

Definition arm_decode_vcmp z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let E := bitb z Z7 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  if (bitb z Z16 =? Z1) && ((M !=? Z0) || (Vm !=? Z0)) then ARM_UNPREDICTABLE
  else ARM_VCMP cond D Vd sz E M Vm.

Definition arm_decode_vfp op z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let Vn := zxbits z Z16 Z20 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let N := bitb z Z7 in
  let Op := bitb z Z6 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  ARM_vfp op cond D Vn Vd sz N Op M Vm.

Definition arm_decode_vcvt_ds z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  ARM_VCVT_ds cond D Vd sz M Vm.

Definition arm_decode_vcvt_fpi z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let opc2 := zxbits z Z16 Z19 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let op := bitb z Z7 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  ARM_VCVT_fpi cond D opc2 Vd sz op M Vm.

Definition arm_decode_vcvt_fpf z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let op := bitb z Z18 in
  let U := bitb z Z16 in
  let Vd := zxbits z Z12 Z16 in
  let sf := bitb z Z8 in
  let sx := bitb z Z7 in
  let i := bitb z Z5 in
  let imm4 := zxbits z Z0 Z4 in

  let size := if sx =? Z0 then Z16 else Z32 in
  if (size <? (imm4 << Z1) + i) then ARM_UNPREDICTABLE
  else ARM_VCVT_fpf cond D op U Vd sf sx i imm4.

Definition arm_decode_vfp_other op z :=
  let cond := armcond z in
  let D := bitb z Z22 in
  let Vd := zxbits z Z12 Z16 in
  let sz := bitb z Z8 in
  let M := bitb z Z5 in
  let Vm := zxbits z Z0 Z4 in
  ARM_vfp_other op cond D Vd sz M Vm.

Definition arm_decode_floating_data_processing z :=
  let opc1 := zxbits z Z20 Z24 in
  let opc2 := zxbits z Z16 Z20 in
  let opc3 := zxbits z Z6 Z8 in
  let opc1'1 := bitb opc1 Z3 in
  let opc1_2 := zxbits opc1 Z0 Z2 in
  if (opc1'1 =? Z0) then
    if (opc1_2 =? Z0) then arm_decode_vfp ARM_VMLA z
    else if (opc1_2 =? Z1) then arm_decode_vfp ARM_VNMLA z
    else if (opc1_2 =? Z2) then
      if (opc3 =? Z1) || (opc3 =? Z3) then arm_decode_vfp ARM_VNMLA z
      else arm_decode_vfp ARM_VMUL z
    else
      if (opc3 =? Z0) || (opc3 =? Z2) then arm_decode_vfp ARM_VADD z
      else arm_decode_vfp ARM_VSUB z
  else
    if (opc1_2 =? Z0) then arm_decode_vfp ARM_VDIV z
    else if (opc1_2 =? Z1) then arm_decode_vfp ARM_VFNMA z
    else if (opc1_2 =? Z2) then arm_decode_vfp ARM_VFMA z
    else (*other fp*)
      if (opc3 =? Z0) || (opc3 =? Z2) then arm_decode_vmov_i z
      else
        if (opc2 =? Z0) then
        if (opc3 =? Z1) then arm_decode_vfp_other ARM_VMOV z
          else arm_decode_vfp_other ARM_VABS z
        else if (opc2 =? Z1) then
          if (opc3 =? Z1) then arm_decode_vfp_other ARM_VNEG z
          else arm_decode_vfp_other ARM_VSQRT z
        else if (opc2 =? Z2) || (opc2 =? Z3) then idk (*vcvtb*)
        else if (opc2 =? Z4) || (opc2 =? Z5) then arm_decode_vcmp z
        else if (opc2 =? Z7) && (opc3 =? Z3) then arm_decode_vcvt_ds z
        else if (opc2 =? Z8) || (opc2 =? Z12) || (opc2 =? Z13) then arm_decode_vcvt_fpi z
        else if (opc2 =? Z10) || (opc2 =? Z11) || (opc2 =? Z14) || (opc2 =? Z15) then arm_decode_vcvt_fpf z
        else ARM_UNDEFINED.

Definition arm_decode_vmrs z :=
  let cond := armcond z in
  let Rt := zxbits z Z12 Z16 in
  if (zxbits z Z5 Z8 !=? Z0) || (zxbits z Z0 Z4 !=? Z0) then ARM_UNPREDICTABLE
  (*t=13 and thumb mode unpredictable*)
  else ARM_VMRS cond Rt.

Definition arm_decode_8_16_32bit_transfer z :=
  let A := zxbits z Z21 Z24 in
  let L := bitb z Z20 in
  let C := bitb z Z8 in
  if (L =? Z0) then
    if (C =? Z0) then
      if (A =? Z0) then arm_decode_vmov_r1 z
      else idk
    else idk
  else
    if (C =? Z0) then
      if (A =? Z0) then arm_decode_vmov_r1 z
      else if (A =? Z7) then arm_decode_vmrs z
      else ARM_UNDEFINED
    else idk.
Definition arm_decode_64bit_transfer z :=
  let C := bitb z Z8 in
  let op := zxbits z Z4 Z8 in
  if (C =? Z0) then
    if (op =? Z1) || (op =? Z3) then arm_decode_vmov_r2 true z
    else ARM_UNDEFINED
  else
    if (op =? Z1) || (op =? Z3) then arm_decode_vmov_r2 false z
    else ARM_UNDEFINED.

Definition arm_decode_coprocessor z := (* A5.6, pg A5-213 *)
  let op1 := zxbits z Z20 Z26 in
  let op := bitb z Z4 in
  let coproc := zxbits z Z8 Z12 in
  if (zxbits op1 Z1 Z6 =? Z0) then ARM_UNDEFINED
  else if (zxbits op1 Z4 Z6 =? Z3) then arm_decode_svc z
  else
    if (coproc =? Z10) || (coproc =? Z11) then (* coproc = 101x *)
      if (zxbits op1 Z4 Z6 =? Z2) then
        if (op =? Z0) then arm_decode_floating_data_processing z
        else arm_decode_8_16_32bit_transfer z
      else if (zxbits op1 Z1 Z6 =? Z2) then arm_decode_64bit_transfer z
      else arm_decode_vreg_ls z (*extension load/store*) (* op1 = 0xxxxx not 000x0x *)
    else (* coproc = not 101x *)
      if (op1 =? Z4) then idk (*mcrr*)
      else if (op1 =? Z5) then idk (*mcrc*)
      else if (zxbits op1 Z4 Z6 =? Z2) then
        if (op =? Z0) then idk (*cdp*)
        else if (bitb op1 Z0 =? Z0) then arm_decode_coproc_m true z
        else arm_decode_coproc_m false z
      else if (bitb op1 Z0 =? Z0) then idk (*stc*)
      else idk (*ldc*).

Definition arm_decode_simd (z:Z) :=
  idk.

Definition arm_decode_pld_r z :=
  let U := bitb z Z23 in
  let R := bitb z Z22 in
  let Rn := zxbits z Z16 Z20 in
  let imm5 := zxbits z Z7 Z12 in
  let type := zxbits z Z5 Z7 in
  let Rm := zxbits z Z0 Z4 in
  if (Rm =? Z15) || ((Rn =? Z15) && (R =? 0)) then ARM_UNPREDICTABLE
  else ARM_PLD_r U R Rn imm5 type Rm.

Definition arm_decode_pld_i z :=
  let U := bitb z Z23 in
  let R := bitb z Z22 in
  let Rn := zxbits z Z16 Z20 in
  let imm12 := zxbits z Z0 Z12 in
  if (zxbits z Z12 Z16 !=? Z15) then ARM_UNPREDICTABLE
  else if (Rn =? Z15) && (R =? 0) then ARM_UNPREDICTABLE
  else ARM_PLD_i U R Rn imm12.

Definition arm_decode_mem_hint_simd z :=
  let op1 := zxbits z Z20 Z27 in
  let op2 := zxbits z Z4 Z8 in
  let op1'3 := zxbits op1 Z4 Z7 in
  let op1_3 := zxbits op1 Z0 Z3 in
  if (op1'3 =? Z0) then ARM_UNDEFINED
  else if (op1'3 =? Z1) then idk
  else if (op1'3 =? Z2) || (op1'3 =? Z3) then arm_decode_simd z
  else if (op1'3 =? Z4) then idk
  else if (op1'3 =? Z5) then
    if (op1_3 =? Z1) || (op1_3 =? Z5) then arm_decode_pld_i z (* op1=101x001,rn=15 is checked in here *)
    else if (op1_3 =? Z3) then ARM_UNPREDICTABLE
    else if (op1_3 =? Z7) then
      if (bitb op1 Z3 =? Z1) then ARM_UNPREDICTABLE
      else if (op2 =? Z0) || (op2 =? Z2) || (op2 =? Z3) || (op2 >=? Z7) then ARM_UNPREDICTABLE
      else if (op2 =? Z1) then idk (*clrex*)
      else if (op2 =? Z4) then idk (*dsb*)
      else if (op2 =? Z5) then idk (*dmb*)
      else (*if (op2 =? Z6) then*) idk (*isb*)
    else ARM_UNDEFINED
  else if (op1'3 =? Z6) then
    if (bitb op2 Z0 =? Z0) then
      if (op1_3 =? Z1) then idk (* unallocated mem hint (nop) *)
      else if (op1_3 =? Z3) || (op1_3 =? Z7) then ARM_UNPREDICTABLE
      else if (op1_3 =? Z5) then idk (* pli reg *)
      else ARM_UNDEFINED
    else ARM_UNDEFINED
  else (* if (op1'3 =? Z7) then *)
    if (bitb op2 Z0 =? Z0) then
      if (op1_3 =? Z1) || (op1_3 =? Z5) then arm_decode_pld_r z (* pldw *)
      else if (op1_3 =? Z3) || (op1_3 =? Z7) then ARM_UNPREDICTABLE
      else ARM_UNDEFINED
    else ARM_UNDEFINED.

Definition arm_decode_unconditional z := (* A5.7, pg A5-214 *)
  let op1 := zxbits z Z20 Z28 in
  let op := bitb z Z4 in
  let op1_5 := zxbits op1 Z0 Z5 in
  let op1_3 := zxbits op1 Z5 Z8 in
  if (op1_3 =? Z0) || (op1_3 =? Z1) || (op1_3 =? Z2) || (op1_3 =? Z3) then arm_decode_mem_hint_simd z (*mem hints*)
  else if (op1_3 =? Z4) then
    if (bitb op1 Z0 =? Z0) && (bitb op1 Z2 =? Z1) then ARM_UNPREDICTABLE (*srs, unpredictable in user mode*)
    else if (bitb op1 Z0 =? Z1) && (bitb op1 Z2 =? Z0) then ARM_UNPREDICTABLE (*rfe, unpredictable in user mode*)
    else ARM_UNDEFINED
  else if (op1_3 =? Z5) then arm_decode_blx_i z
  else if (op1_3 =? Z6) then
    if (op1_5 =? Z4) then idk (*mcrr*)
    else if (op1_5 =? Z5) then idk (*mrrc*)
    else if (bitb op1 Z0 =? Z0) && (op1_5 !=? Z0) && (op1_5 !=? Z4) then idk (*stc*)
    else if (bitb op1 Z0 =? Z1) && (op1_5 !=? Z1) && (op1_5 !=? Z5) then idk (*ldc*)
    else ARM_UNDEFINED
  else if (op1_3 =? Z7) && (bitb op1 Z4 =? Z0) then
    if (op =? Z0) then idk (*cdp*)
    else if (bitb op1 Z0 =? Z0) then idk (*mcr*)
    else idk (*mrc*)
  else ARM_UNDEFINED.

Definition arm_decode z :=
  let cond := zxbits z Z28 Z32 in
  let op1 := zxbits z Z25 Z28 in
  let op := bitb z Z4 in
  if (z <=? Z0) then ARM_UNDEFINED
  else if (cond =? Z15) then arm_decode_unconditional z
  else
    if (op1 =? Z0) || (op1 =? Z1) then arm_decode_data_misc z
    else if (op1 =? Z2) || (op1 =? Z3) && (op =? Z0) then arm_decode_load_store z
    else if (op1 =? Z3) && (op =? Z1) then arm_decode_media z
    else if (op1 =? Z4) || (op1 =? Z5) then arm_decode_branch_block_transfer z
    else (*if (op1 =? Z6) || (op1 =? Z7) then*) arm_decode_coprocessor z.

(********** assembly **********)

Scheme Equality for arm_inst.

Definition arm_data_opcode op :=
  match op with
  | ARM_AND => Z0
  | ARM_EOR => Z1
  | ARM_SUB => Z2
  | ARM_RSB => Z3
  | ARM_ADD => Z4
  | ARM_ADC => Z5
  | ARM_SBC => Z6
  | ARM_RSC => Z7
  | ARM_TST => Z8
  | ARM_TEQ => Z9
  | ARM_CMP => Z10
  | ARM_CMN => Z11
  | ARM_ORR => Z12
  | ARM_MOV => Z13
  | ARM_BIC => Z14
  | ARM_MVN => Z15
  end.
Definition arm_assemble_data_r op cond s Rn Rd imm5 type Rm :=
  let op := arm_data_opcode op in
  (cond << Z28) .| (op << Z21) .| (s << Z20) .| (Rn << Z16) .| (Rd << Z12) .| (imm5 << Z7) .| (type << Z5) .| Rm.
Definition arm_assemble_data_rsr op cond s Rn Rd Rs type Rm :=
  let op := arm_data_opcode op in
  (cond << Z28) .| (op << Z21) .| (s << Z20) .| (Rn << Z16) .| (Rd << Z12) .| (Rs << Z8) .| (type << Z5) .| (Z1 << Z4) .| Rm.
Definition arm_assemble_data_i op cond s Rn Rd imm12 :=
  let op := arm_data_opcode op in
  (cond << Z28) .| (Z1 << Z25) .| (op << Z21) .| (s << Z20) .| (Rn << Z16) .| (Rd << Z12) .| imm12.
Definition arm_assemble_MOV_WT (is_w: bool) cond imm4 Rd imm12 :=
  let op := if is_w then Z16 else Z20 in
  (cond << Z28) .| (Z1 << Z25) .| (op << Z20) .| (imm4 << Z16) .| (Rd << Z12) .| imm12.
Definition arm_mul_opcode op :=
  match op with
  | ARM_MUL => Z0
  | ARM_MLA => Z1
  | ARM_UMAAL => Z2
  | ARM_MLS => Z3
  | ARM_UMULL => Z4
  | ARM_UMLAL => Z5
  | ARM_SMULL => Z6
  | ARM_SMLAL => Z7
  end.
Definition arm_assemble_mul op cond s Rd_RdHi Ra_RdLo Rm Rn :=
  let op := arm_mul_opcode op in
  (cond << Z28) .| (op << Z21) .| (s << Z20) .| (Rd_RdHi << Z16) .| (Ra_RdLo << Z12) .| (Rm << Z8) .| (Z9 << Z4) .| Rn.
Definition arm_sync_size_opcode size :=
  match size with
  | ARM_sync_word => Z0
  | ARM_sync_doubleword => Z1
  | ARM_sync_byte => Z2
  | ARM_sync_halfword => Z3
  end.
Definition arm_assemble_sync_l size cond Rn Rt :=
  let size := arm_sync_size_opcode size in
  (cond << Z28) .| (Z3 << Z23) .| (size << Z21) .| (Z1 << Z20) .| (Rn << Z16) .| (Rt << Z12) .| (Z15 << Z8) .| (Z9 << Z4) .| Z15.
Definition arm_assemble_sync_s size cond Rn Rd Rt :=
  let size := arm_sync_size_opcode size in
  (cond << Z28) .| (Z3 << Z23) .| (size << Z21) .| (Rn << Z16) .| (Rd << Z12) .| (Z15 << Z8) .| (Z9 << Z4) .| Rt.
Definition arm_assemble_BX cond Rm :=
  (cond << Z28) .| (Z9 << Z21) .| (Z4095 << Z8) .| (Z1 << Z4) .| Rm.
Definition arm_assemble_BLX_r cond Rm :=
  (cond << Z28) .| (Z9 << Z21) .| (Z4095 << Z8) .| (Z3 << Z4) .| Rm.
Definition arm_assemble_BXJ cond Rm :=
  (cond << Z28) .| (Z9 << Z21) .| (Z4095 << Z8) .| (Z2 << Z4) .| Rm.
Definition arm_assemble_CLZ cond Rd Rm :=
  (cond << Z28) .| (Z11 << Z21) .| (Z15 << Z16) .| (Rd << Z12) .| (Z15 << Z8) .| (Z1 << Z4) .| Rm.
Definition arm_assemble_BKPT cond imm12 imm4 :=
  (cond << Z28) .| (Z9 << Z21) .| (imm12 << Z8) .| (Z7 << Z4) .| imm4.
Definition arm_sat_opcode op :=
  match op with
  | ARM_QADD => Z0
  | ARM_QSUB => Z1
  | ARM_QDADD => Z2
  | ARM_QDSUB => Z3
  end.
Definition arm_assemble_sat op cond Rn Rd Rm :=
  let op := arm_sat_opcode op in
  (cond << Z28) .| (Z1 << Z24) .| (op << Z21) .| (Rn << Z16) .| (Rd << Z12) .| (Z5 << Z4) .| Rm.
Definition arm_assemble_hint cond op2 :=
  (cond << Z28) .| (Z25 << Z21) .| (Z15 << Z12) .| op2.
Definition arm_xmem_opcode op :=
  match op with
  | ARM_STRH => Z11
  | ARM_LDRH => Z11 .| (Z1 << Z16)
  | ARM_LDRD => Z13
  | ARM_LDRSB => Z13 .| (Z1 << Z16)
  | ARM_STRD => Z15
  | ARM_LDRSH => Z15 .| (Z1 << Z16)
  end.
Definition arm_assemble_extra_ls_i op cond P U W Rn Rt imm4H imm4L :=
  let op := arm_xmem_opcode op in
  (cond << Z28) .| (P << Z24) .| (U << Z23) .| (Z1 << Z22) .| (W << Z21) .| (Rn << Z16) .| (Rt << Z12) .| (imm4H << Z8) .| (op << Z4) .| imm4L.
Definition arm_assemble_extra_ls_r op cond P U W Rn Rt Rm :=
  let op := arm_xmem_opcode op in
  (cond << Z28) .| (P << Z24) .| (U << Z23) .| (W << Z21) .| (Rn << Z16) .| (Rt << Z12) .| (op << Z4) .| Rm.
Definition arm_mem_opcode op :=
  match op with
  | ARM_STR => Z0
  | ARM_LDR => Z1
  | ARM_STRB => Z4
  | ARM_LDRB => Z5
  end.
Definition arm_assemble_ls_i op cond P U W Rn Rt imm12 :=
  let op := arm_mem_opcode op in
  (cond << Z28) .| (Z1 << Z26) .| (P << Z24) .| (U << Z23) .| (W << Z21) .| (op << Z20) .| (Rn << Z16) .| (Rt << Z12) .| imm12.
Definition arm_assemble_ls_r op cond P U W Rn Rt imm5 type Rm :=
  let op := arm_mem_opcode op in
  (cond << Z28) .| (Z3 << Z25) .| (P << Z24) .| (U << Z23) .| (W << Z21) .| (op << Z20) .| (Rn << Z16) .| (Rt << Z12) .| (imm5 << Z7) .| (type << Z5) .| Rm.
Definition arm_memm_opcode op :=
  match op with
  | ARM_STMDA => Z0
  | ARM_LDMDA => Z1
  | ARM_STMIA => Z8
  | ARM_LDMIA => Z9
  | ARM_STMDB => Z16
  | ARM_LDMDB => Z17
  | ARM_STMIB => Z24
  | ARM_LDMIB => Z25
  end.
Definition arm_assemble_lsm op cond W Rn register_list :=
  let op := arm_memm_opcode op in
  (cond << Z28) .| (Z1 << Z27) .| (W << Z21) .| (op << Z20) .| (Rn << Z16) .| register_list.
Definition arm_assemble_B cond imm24 :=
  (cond << Z28) .| (Z10 << Z24) .| imm24.
Definition arm_assemble_BL cond imm24 :=
  (cond << Z28) .| (Z11 << Z24) .| imm24.
Definition arm_assemble_BLX_i H imm24 :=
  (Z15 << Z28) .| (Z10 << Z24) .| (H << Z24) .| imm24.
Definition arm_assemble_vls (is_load is_single: bool) cond U D Rn Vd imm8 :=
  let is_load := if is_load then Z1 else Z0 in
  let x := if is_single then Z10 else Z11 in
  (cond << Z28) .| (Z13 << Z24) .| (U << Z23) .| (D << Z22) .| (is_load << Z20) .| (Rn << Z16) .| (Vd << Z12) .| (x << Z8) .| imm8.

Definition arm_assemble i :=
  let z := match i with
           | ARM_data_r op cond s Rn Rd imm5 type Rm => arm_assemble_data_r op cond s Rn Rd imm5 type Rm
           | ARM_data_rsr op cond s Rn Rd Rs type Rm => arm_assemble_data_rsr op cond s Rn Rd Rs type Rm
           | ARM_data_i op cond s Rn Rd imm12 => arm_assemble_data_i op cond s Rn Rd imm12
           | ARM_MOV_WT is_w cond imm4 Rd imm12 => arm_assemble_MOV_WT is_w cond imm4 Rd imm12
           | ARM_mul op cond s Rd_RdHi Ra_RdLo Rm Rn => arm_assemble_mul op cond s Rd_RdHi Ra_RdLo Rm Rn
           | ARM_sync_l size cond Rn Rt => arm_assemble_sync_l size cond Rn Rt
           | ARM_sync_s size cond Rn Rd Rt => arm_assemble_sync_s size cond Rn Rd Rt
           | ARM_BX cond Rm => arm_assemble_BX cond Rm
           | ARM_BLX_r cond Rm => arm_assemble_BLX_r cond Rm
           | ARM_BXJ cond Rm => arm_assemble_BXJ cond Rm
           | ARM_CLZ cond Rd Rm => arm_assemble_CLZ cond Rd Rm
           | ARM_BKPT cond imm12 imm4 => arm_assemble_BKPT cond imm12 imm4
           | ARM_sat op cond Rn Rd Rm => arm_assemble_sat op cond Rn Rd Rm
           | ARM_hint cond op2 => arm_assemble_hint cond op2
           | ARM_extra_ls_i op cond P U W Rn Rt imm4H imm4L => arm_assemble_extra_ls_i op cond P U W Rn Rt imm4H imm4L
           | ARM_extra_ls_r op cond P U W Rn Rt Rm => arm_assemble_extra_ls_r op cond P U W Rn Rt Rm
           | ARM_ls_i op cond P U W Rn Rt imm12 => arm_assemble_ls_i op cond P U W Rn Rt imm12
           | ARM_ls_r op cond P U W Rn Rt imm5 type Rm => arm_assemble_ls_r op cond P U W Rn Rt imm5 type Rm
           | ARM_lsm op cond W Rn register_list => arm_assemble_lsm op cond W Rn register_list
           | ARM_B cond imm24 => arm_assemble_B cond imm24
           | ARM_BL cond imm24 => arm_assemble_BL cond imm24
           | ARM_BLX_i H imm24 => arm_assemble_BLX_i H imm24
           | ARM_vls is_load is_single cond U D Rn Vd imm8 => arm_assemble_vls is_load is_single cond U D Rn Vd imm8
           | _ => Z0
           end in
  if arm_inst_beq (arm_decode z) i then Some z
  else None.
Fixpoint arm_assemble_all l :=
  match l with
  | a::t => match arm_assemble a with
            | Some z => match arm_assemble_all t with
                        | Some zs => Some (z::zs)
                        | None => None
                        end
            | None => None
            end
  | nil => Some nil
  end.

Lemma arm_assemble_eq:
  forall i z,
    arm_assemble i = Some z ->
    arm_decode z = i.
Proof.
  intros. unfold arm_assemble in H.
  remember (match i with | _ => _ end : Z) as d.
  destruct arm_inst_beq eqn:e. apply internal_arm_inst_dec_bl. injection H. intro. rewrite <- H0. assumption.
  discriminate.
Qed.
Lemma arm_assemble_all_eq:
  forall l z,
    arm_assemble_all l = Some z ->
    map arm_decode z = l.
Proof.
  induction l.
    intros. inversion H. reflexivity.
    intros. unfold arm_assemble_all in H. destruct arm_assemble eqn:e, arm_assemble_all.
      inversion H. simpl. apply arm_assemble_eq in e. rewrite e. rewrite IHl; reflexivity.
      all: discriminate.
Qed.

(********** lifting **********)

Close Scope Z.

Definition arm_cond_il n stmt :=
  match n with
  (* EQ, NE *)
  | 0 => If (Var R_ZF) stmt Nop
  | 1 => If (Var R_ZF) Nop stmt
  (* CS, CC *)
  | 2 => If (Var R_CF) stmt Nop
  | 3 => If (Var R_CF) Nop stmt
  (* MI, PL *)
  | 4 => If (Var R_NF) stmt Nop
  | 5 => If (Var R_NF) Nop stmt
  (* VS, VC *)
  | 6 => If (Var R_VF) stmt Nop
  | 7 => If (Var R_VF) Nop stmt
  (* HI, LS *)
  | 8 => If (BinOp OP_AND (Var R_CF) (UnOp OP_NOT (Var R_CF))) stmt Nop
  | 9 => If (BinOp OP_AND (Var R_CF) (UnOp OP_NOT (Var R_CF))) Nop stmt
  (* GE, LT *)
  | 10 => If (BinOp OP_EQ (Var R_NF) (Var R_VF)) stmt Nop
  | 11 => If (BinOp OP_EQ (Var R_NF) (Var R_VF)) Nop stmt
  (* GT, LE *)
  | 12 => If (BinOp OP_AND (UnOp OP_NOT (Var R_ZF)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) stmt Nop
  | 13 => If (BinOp OP_AND (UnOp OP_NOT (Var R_ZF)) (BinOp OP_EQ (Var R_NF) (Var R_VF))) Nop stmt
  (* AL *)
  | _ => stmt
  end.

Definition arm_varid n :=
  match n with
  | 0 => R_R0
  | 1 => R_R1
  | 2 => R_R2
  | 3 => R_R3
  | 4 => R_R4
  | 5 => R_R5
  | 6 => R_R6
  | 7 => R_R7
  | 8 => R_R8
  | 9 => R_R9
  | 10 => R_R10
  | 11 => R_R11
  | 12 => R_R12
  | 13 => R_SP
  | 14 => R_LR
  | _ => R_PC
  end.
Notation temp0 := (V_TEMP 0).
Notation vtemp0 := (Var temp0).
Definition arm_assign_R n val := Move (arm_varid n) val.
Definition arm_R n := if (n =? 15) then BinOp OP_PLUS (Var R_PC) (Word 8 32) else Var (arm_varid n).
Definition arm_assign_MemU addr size val :=
  let s := fun e => (Move V_MEM32 (Store (Var V_MEM32) addr val e size)) in
    If (Var R_E) (s BigE) (s LittleE).
Definition arm_MemU addr size :=
  let s := fun e => Load (Var V_MEM32) addr e size in
    Ite (Var R_E) (s BigE) (s LittleE).

Notation "R[ m ] := v" := (arm_assign_R m v) (at level 0).
Notation "R[ m ]" := (arm_R m) (at level 0).
Notation "MemU[ a , s ] := v" := (arm_assign_MemU a s v) (at level 0).
Notation "MemU[ a , s ]" := (arm_MemU a s) (at level 0).

Variant arm_srtype :=
  | ARM_LSL
  | ARM_LSR
  | ARM_ASR
  | ARM_ROR
  | ARM_RRX.

Definition DecodeImmShift type imm5 :=
  match type, imm5 with
  | 0, _ => (ARM_LSL, Word imm5 32)
  | 1, 0 => (ARM_LSR, Word 32 32)
  | 1, _ => (ARM_LSR, Word imm5 32)
  | 2, 0 => (ARM_ASR, Word 32 32)
  | 2, _ => (ARM_ASR, Word imm5 32)
  | _, 0 => (ARM_RRX, Word 1 32)
  | _, _ => (ARM_ROR, Word imm5 32)
  end.
Definition DecodeRegShift type :=
  match type with
  | 0 => ARM_LSL
  | 1 => ARM_LSR
  | 2 => ARM_ASR
  | _ => ARM_ROR
  end.
Definition Shift_C value type amount carry_in :=
  let (result, carry_out) :=
    match type with
    | ARM_LSL =>
        let r := BinOp OP_LSHIFT value amount in
        let c := Cast CAST_HIGH 1 (BinOp OP_LSHIFT value (BinOp OP_MINUS amount (Word 1 32))) in
        (r, c)
    | ARM_LSR =>
        let r := BinOp OP_RSHIFT value amount in
        let c := Cast CAST_LOW 1 (BinOp OP_RSHIFT value (BinOp OP_MINUS amount (Word 1 32))) in
        (r, c)
    | ARM_ASR =>
        let r := BinOp OP_ARSHIFT value amount in
        let c := Cast CAST_LOW 1 (BinOp OP_ARSHIFT value (BinOp OP_MINUS amount (Word 1 32))) in
        (r, c)
    | ARM_ROR =>
        let x := BinOp OP_RSHIFT value amount in
        let y := BinOp OP_LSHIFT value (BinOp OP_MINUS (Word 32 32) amount) in
        let r := BinOp OP_OR x y in
        let c := Cast CAST_HIGH 1 r in
        (r, c)
    | ARM_RRX =>
        let x := Concat carry_in value in
        let y := BinOp OP_RSHIFT x (Word 1 33) in
        let r := Cast CAST_LOW 32 y in
        let c := Cast CAST_LOW 1 value in
        (r, c)
    end in
  let result := Ite (BinOp OP_EQ amount (Word 0 32)) value result in
  let carry_out := Ite (BinOp OP_EQ amount (Word 0 32)) carry_in carry_out in
  (result, carry_out).
Definition ARMExpandImm_C imm12 carry_in :=
  let unrotated := Word (xbits imm12 0 8) 32 in
  let shift_n := Word (2 * (xbits imm12 8 12)) 32 in
  Shift_C unrotated ARM_ROR shift_n carry_in.
Definition AddWithCarry x y carry_in :=
  let result := BinOp OP_PLUS (BinOp OP_PLUS x y) (Cast CAST_UNSIGNED 32 carry_in) in
  (* unsigned overflow *)
  let carry_out := BinOp OP_OR
    (BinOp OP_LT result x)
    (BinOp OP_AND (BinOp OP_EQ result (Word 0xffff_ffff 32)) carry_in) in
  (* signed overflow *)
  let overflow := BinOp OP_OR
    (BinOp OP_SLT
      (BinOp OP_AND (BinOp OP_XOR x result) (BinOp OP_XOR y result))  (* msb=1 if x and result, y and result have diff sign *)
      (Word 0 32))
    (BinOp OP_AND (BinOp OP_EQ result (Word 0x7fff_ffff 32)) carry_in) in
  (result, carry_out, overflow).

Definition sizeof v :=
  match arm7typctx v with
  | Some s => s
  | None => 0
  end.
Definition setunknown v :=
  match sizeof v with
  | 0 => Nop
  | s => Move v (Unknown s)
  end.

Definition arm_havoc :=
  Seq (fold_left Seq (
    map setunknown (
      V_MEM32::V_MEM64::
      R_R0::R_R1::R_R2::R_R3::R_R4::R_R5::R_R6::
      R_R7::R_R8::R_R9::R_R10::R_R11::R_R12::
      R_SP::R_LR::R_PC::
      R_M::R_T::R_F::R_I::R_A::R_E::R_IT::R_GE::
      R_DNM::R_JF::R_QF::R_VF::R_CF::R_ZF::R_NF::
      nil
    )
  ) Nop) (Jmp (Unknown 32)).
Definition BXWritePC address :=
  If (Extract 0 0 address) (
    Seq (Move R_T (Word 1 1)) (Seq (Move R_JF (Word 0 1)) (Jmp (BinOp OP_AND address (Word 0xffff_fffe 32))))
  ) (* else *) (
    If (BinOp OP_EQ (Extract 1 1 address) (Word 0 1)) (
      Jmp address
    ) (* else *) (
      arm_havoc
    )
  ).
Definition BranchWritePC address := Jmp (BinOp OP_AND address (Word 0xffff_fffc 32)). (* different in thumb mode or before v6 *)
Notation ALUWritePC := BXWritePC (only parsing). (* different in thumb mode or before v7 *)
Notation LoadWritePC := BXWritePC (only parsing). (* different before v5 *)
Definition arm_data_flag result carry overflow :=
  Seq (Move R_NF (Cast CAST_HIGH 1 result))
    (Seq (Move R_ZF (BinOp OP_EQ result (Word 0 32)))
      (Seq (Move R_CF carry)
        (Move R_VF overflow))).
Definition arm_data_il (assign: bool) cond S Rd result carry overflow :=
  arm_cond_il cond
    (if (Rd =? 15) then
      ALUWritePC result
    else
      let assign := if assign then R[Rd] := result else Nop in
      if (S =? 1) then
        (* the manual has the assign first, but that would mess up the value of result for the flag il *)
        Seq (arm_data_flag result carry overflow) assign
      else
        assign).
Definition arm_data_op_il op shiftc addwcarry : stmt :=
  match op with
  | ARM_AND => shiftc    true  (fun a b => BinOp OP_AND a b)
  | ARM_EOR => shiftc    true  (fun a b => BinOp OP_XOR a b)
  | ARM_SUB => addwcarry true  (fun a b => AddWithCarry a (UnOp OP_NOT b) (Word 1 1))
  | ARM_RSB => addwcarry true  (fun a b => AddWithCarry (UnOp OP_NOT a) b (Word 1 1))
  | ARM_ADD => addwcarry true  (fun a b => AddWithCarry a b (Word 0 1))
  | ARM_ADC => addwcarry true  (fun a b => AddWithCarry a b (Var R_CF))
  | ARM_SBC => addwcarry true  (fun a b => AddWithCarry a (UnOp OP_NOT b) (Var R_CF))
  | ARM_RSC => addwcarry true  (fun a b => AddWithCarry (UnOp OP_NOT a) b (Var R_CF))
  | ARM_TST => shiftc    false (fun a b => BinOp OP_AND a b)
  | ARM_TEQ => shiftc    false (fun a b => BinOp OP_XOR a b)
  | ARM_CMP => addwcarry false (fun a b => AddWithCarry a (UnOp OP_NOT b) (Word 1 1))
  | ARM_CMN => addwcarry false (fun a b => AddWithCarry a b (Word 0 1))
  | ARM_ORR => shiftc    true  (fun a b => BinOp OP_OR a b)
  | ARM_MOV => shiftc    true  (fun a b => b)
  | ARM_BIC => shiftc    true  (fun a b => BinOp OP_AND a (UnOp OP_NOT b))
  | ARM_MVN => shiftc    true  (fun a b => UnOp OP_NOT b)
  end.

Definition arm_data_r_shiftc cond S Rn Rd imm5 type Rm assign op :=
  let (shift_t, shift_n) := DecodeImmShift type imm5 in
  let (shifted, carry) := Shift_C R[Rm] shift_t shift_n (Var R_CF) in
  let result := op R[Rn] shifted in
  arm_data_il assign cond S Rd result carry (Var R_VF).
Definition arm_data_r_addwcarry cond S Rn Rd imm5 type Rm assign op :=
  let (shift_t, shift_n) := DecodeImmShift type imm5 in
  let (shifted, _) := Shift_C R[Rm] shift_t shift_n (Var R_CF) in
  let '(result, carry, overflow) := op R[Rn] shifted in
  arm_data_il assign cond S Rd result carry overflow.
Definition arm_data_r_il op cond S Rn Rd imm5 type Rm :=
  let shiftc := arm_data_r_shiftc cond S Rn Rd imm5 type Rm in
  let addwcarry := arm_data_r_addwcarry cond S Rn Rd imm5 type Rm in
  arm_data_op_il op shiftc addwcarry.

Definition arm_data_rsr_shiftc cond S Rn Rd Rs type Rm assign op :=
  let shift_t := DecodeRegShift type in
  let shift_n := BinOp OP_AND R[Rs] (Word 255 32) in
  let (shifted, carry) := Shift_C R[Rm] shift_t shift_n (Var R_CF) in
  let result := op R[Rn] shifted in
  arm_data_il assign cond S Rd result carry (Var R_VF).
Definition arm_data_rsr_addwcarry cond S Rn Rd Rs type Rm assign op :=
  let shift_t := DecodeRegShift type in
  let shift_n := BinOp OP_AND R[Rs] (Word 255 32) in
  let (shifted, _) := Shift_C R[Rm] shift_t shift_n (Var R_CF) in
  let '(result, carry, overflow) := op R[Rn] shifted in
  arm_data_il assign cond S Rd result carry overflow.
Definition arm_data_rsr_il op cond S Rn Rd Rs type Rm :=
  let shiftc := arm_data_rsr_shiftc cond S Rn Rd Rs type Rm in
  let addwcarry := arm_data_rsr_addwcarry cond S Rn Rd Rs type Rm in
  arm_data_op_il op shiftc addwcarry.

Definition arm_data_i_shiftc cond S Rn Rd imm12 assign op :=
  let (imm32, carry) := ARMExpandImm_C imm12 (Var R_CF) in
  let result := op R[Rn] imm32 in
  arm_data_il assign cond S Rd result carry (Var R_VF).
Definition arm_data_i_addwcarry cond S Rn Rd imm12 assign op :=
  let (imm32, _) := ARMExpandImm_C imm12 (Var R_CF) in
  let '(result, carry, overflow) := op R[Rn] imm32 in
  arm_data_il assign cond S Rd result carry overflow.
Definition arm_data_i_il op cond S Rn Rd imm12 :=
  let shiftc := arm_data_i_shiftc cond S Rn Rd imm12 in
  let addwcarry := arm_data_i_addwcarry cond S Rn Rd imm12 in
  arm_data_op_il op shiftc addwcarry.

Definition arm_mov_wt_il (is_w: bool) cond imm4 Rd imm12 :=
  let imm16 := cbits imm4 12 imm12 in
  arm_cond_il cond (
    if (is_w) then
      R[Rd] := (Word imm16 32)
    else
      R[Rd] := (BinOp OP_OR (BinOp OP_AND R[Rd] (Word 0xffff 32)) (Word (N.shiftl imm16 16) 32))).

Definition arm_ls_il op cond P U W Rn (Rt: N) offset :=
  let add := U =? 1 in
  let index := P =? 1 in
  let wback := (P =? 0) || (W =? 1) in
  let binop := if add then OP_PLUS else OP_MINUS in
  (* ldr literal aligns R[15] by 4, but since we only support ARM mode, this is the same *)
  let offset_addr := BinOp binop R[Rn] offset in
  let addr := if index then offset_addr else R[Rn] in
  let op := op addr Rt in
  if wback then
    (* the manual has the move occur first for some loads, but that would mess up the value of Rn in the load/store *)
    (* ldr is unpredictable when Rn=Rt with wback, so this is still fine *)
    arm_cond_il cond (Seq op (R[Rn] := offset_addr))
  else
    arm_cond_il cond op.
Definition arm_ls_op_il op :=
  let op := match op with
            | ARM_STR => fun addr Rt => MemU[addr, 4] := R[Rt]
            | ARM_STRB => fun addr Rt => MemU[addr, 1] := (Cast CAST_LOW 8 R[Rt])
            | ARM_LDR => fun addr Rt =>
                let data := MemU[addr, 4] in
                if Rt =? 15 then
                  If (BinOp OP_NEQ (BinOp OP_AND addr (Word 3 32)) (Word 0 32)) arm_havoc (LoadWritePC data)
                else
                  R[Rt] := data
            | ARM_LDRB => fun addr Rt => R[Rt] := (Cast CAST_UNSIGNED 32 MemU[addr, 1])
            end in
  arm_ls_il op.
Definition arm_ls_i_il op cond P U W Rn Rt imm12 :=
  arm_ls_op_il op cond P U W Rn Rt (Word imm12 32).
Definition arm_ls_r_il op cond P U W Rn Rt imm5 type Rm :=
  let (shift_t, shift_n) := DecodeImmShift type imm5 in
  let (offset, _) := Shift_C R[Rm] shift_t shift_n (Var R_CF) in
  arm_ls_op_il op cond P U W Rn Rt offset.
Definition arm_bx_il cond Rm :=
  arm_cond_il cond (BXWritePC R[Rm]).
Definition arm_blx_r_il cond Rm :=
  arm_cond_il cond (Seq
    (Move temp0 R[Rm]) (Seq
    (R[13] := (BinOp OP_PLUS (Var R_PC) (Word 4 32)))
    (BXWritePC vtemp0))
  ).
Definition arm_b_il cond imm24 :=
  let imm32 := scast 26 32 (N.shiftl imm24 2) in
  arm_cond_il cond (BranchWritePC (BinOp OP_PLUS R[15] (Word imm32 32))).
Definition arm_bl_il cond imm24 :=
  let imm32 := scast 26 32 (N.shiftl imm24 2) in
  arm_cond_il cond (Seq
    (R[13] := (BinOp OP_PLUS (Var R_PC) (Word 4 32)))
    (BranchWritePC (BinOp OP_PLUS R[15] (Word imm32 32)))
  ).

Definition for_0_14 reg_list start f : stmt :=
  let iter := fun i prev => Seq prev (if (xbits reg_list i (i+1) =? 1) then (f i) else Nop) in
  let i0 := iter 0 start in
  let i1 := iter 1 i0 in
  let i2 := iter 2 i1 in
  let i3 := iter 3 i2 in
  let i4 := iter 4 i3 in
  let i5 := iter 5 i4 in
  let i6 := iter 6 i5 in
  let i7 := iter 7 i6 in
  let i8 := iter 8 i7 in
  let i9 := iter 9 i8 in
  let i10 := iter 10 i9 in
  let i11 := iter 11 i10 in
  let i12 := iter 12 i11 in
  let i13 := iter 13 i12 in
  let i14 := iter 14 i13 in
  i14.
Definition arm_lsm_il_ f pc start_val wback_val cond W Rn register_list :=
  let addr := BinOp OP_PLUS R[Rn] (Word start_val 32) in
  let wback_val := BinOp OP_PLUS R[Rn] (Word wback_val 32) in
  let start := Move temp0 addr in
  let start := if (W =? 1) then Seq start (R[Rn] := wback_val) else start in
  let i14 := for_0_14 register_list start f in
  let i15 := if (xbits register_list 15 16 =? 1) then Seq i14 pc else i14 in
  (* all memory accesses should be aligned, but we only need to check that the value of Rn is aligned at the beginning *)
  let align_check := If (BinOp OP_EQ (BinOp OP_AND R[Rn] (Word 3 32)) (Word 0 32)) i15 (Exn 0x10) in
  arm_cond_il cond align_check.
Definition arm_ldm_il :=
  arm_lsm_il_
    (fun i =>
      Seq (R[i] := MemU[vtemp0, 4])
        (Move temp0 (BinOp OP_PLUS vtemp0 (Word 4 32))))
    (LoadWritePC MemU[vtemp0, 4]).

Fixpoint LowestSetBitP (p:positive) :=
  match p with
  | xO p => 1 + LowestSetBitP p
  | _ => 0
  end.
Definition LowestSetBit n size :=
  match n with
  | N0 => size
  | Npos p => LowestSetBitP p
  end.
Definition arm_stm_il start_val wback_val cond W Rn register_list :=
  let stored_val := fun i =>
    if (i =? Rn) && (W =? 1) && (negb (i =? LowestSetBit register_list 32)) then
      Unknown 32
    else
      R[i] in
  arm_lsm_il_
    (fun i =>
      Seq (MemU[vtemp0, 4] := (stored_val i))
        (Move temp0 (BinOp OP_PLUS vtemp0 (Word 4 32))))
    (MemU[vtemp0, 4] := R[15])
    start_val wback_val cond W Rn register_list.
Definition arm_lsm_op_type op :=
  match op with
  | ARM_STMDA | ARM_STMDB
  | ARM_STMIA | ARM_STMIB => arm_stm_il
  | ARM_LDMDA | ARM_LDMDB
  | ARM_LDMIA | ARM_LDMIB => arm_ldm_il
  end.
Definition arm_lsm_op_start op bc :=
  match op with
  | ARM_STMDA | ARM_LDMDA => (-bc+Z4)%Z
  | ARM_STMDB | ARM_LDMDB => (-bc)%Z
  | ARM_STMIA | ARM_LDMIA => Z0
  | ARM_STMIB | ARM_LDMIB => Z4
  end.
Definition arm_lsm_op_wback op bc :=
  match op with
  | ARM_STMDA | ARM_LDMDA
  | ARM_STMDB | ARM_LDMDB => (-bc)%Z
  | ARM_STMIA | ARM_LDMIA
  | ARM_STMIB | ARM_LDMIB => bc
  end.
Definition arm_lsm_op_il op register_list :=
  let bc := Z.of_N (4 * popcount register_list) in
  (arm_lsm_op_type op) (ofZ 32 (arm_lsm_op_start op bc)) (ofZ 32 (arm_lsm_op_wback op bc)).

Definition arm_lsm_il op cond W Rn register_list :=
  arm_lsm_op_il op register_list cond W Rn register_list.

Definition arm_pas_il (is_signed: bool) (type: arm_pas_type) (op: arm_pas_op) (cond Rn Rd Rm: N) :=
  arm_cond_il cond (
    match type with
    | ARM_pas_normal => Seq (R[Rd] := (Unknown 32)) (Move R_GE (Unknown 4))
    | _ => R[Rd] := (Unknown 32)
    end).
Definition arm_mul_il op cond (s Rd_RdHi Ra_RdLo Rm Rn: N) :=
  let assign := match op with
                | ARM_MUL | ARM_MLA | ARM_MLS => R[Rd_RdHi] := (Unknown 32)
                | _ => Seq (R[Rd_RdHi] := (Unknown 32)) (R[Ra_RdLo] := (Unknown 32))
                end in
  let flags := Seq (Move R_NF (Unknown 1)) (Move R_ZF (Unknown 1)) in
  arm_cond_il cond (if s =? 1 then Seq assign flags else assign).
Definition arm_sat_il (op: arm_sat_op) (cond Rn Rd Rm: N) :=
  arm_cond_il cond (Seq (R[Rd] := (Unknown 32)) (Move R_QF (Unknown 1))).
Definition arm_hint_il (cond op2: N) :=
  Nop.
Definition arm_svc_il cond (imm24: N) :=
  arm_cond_il cond (Exn 8).
Definition arm_rev_il (op: arm_rev_op) (cond Rd Rm: N) :=
  arm_cond_il cond (R[Rd] := (Unknown 32)).
Definition arm_extend_il (is_signed: bool) (op: arm_extend_op) (cond Rn Rd rotate Rm: N) :=
  arm_cond_il cond (R[Rd] := (Unknown 32)).


Notation "$ x" := (Z.to_N x) (at level 0, only parsing).
Definition arm2il (a:addr) inst :=
  let il := match inst with
            | ARM_data_r op cond s Rn Rd imm5 type Rm => arm_data_r_il op $cond $s $Rn $Rd $imm5 $type $Rm
            | ARM_data_rsr op cond s Rn Rd Rs type Rm => arm_data_rsr_il op $cond $s $Rn $Rd $Rs $type $Rm
            | ARM_data_i op cond s Rn Rd imm12 => arm_data_i_il op $cond $s $Rn $Rd $imm12
            | ARM_MOV_WT is_w cond imm4 Rd imm12 => arm_mov_wt_il is_w $cond $imm4 $Rd $imm12
            | ARM_ls_i op cond P U W Rn Rt imm12 => arm_ls_i_il op $cond $P $U $W $Rn $Rt $imm12
            | ARM_ls_r op cond P U W Rn Rt imm5 type Rm => arm_ls_r_il op $cond $P $U $W $Rn $Rt $imm5 $type $Rm
            | ARM_lsm op cond W Rn register_list => arm_lsm_il op $cond $W $Rn $register_list
            | ARM_BX cond Rm => arm_bx_il $cond $Rm
            | ARM_BLX_r cond Rm => arm_blx_r_il $cond $Rm
            | ARM_B cond imm24 => arm_b_il $cond $imm24
            | ARM_BL cond imm24 => arm_bl_il $cond $imm24
            | ARM_UNDEFINED => Exn 4
            | ARM_pas is_signed type op cond Rn Rd Rm => arm_pas_il is_signed type op $cond $Rn $Rd $Rm
            | ARM_mul op cond s Rd_RdHi Ra_RdLo Rm Rn => arm_mul_il op $cond $s $Rd_RdHi $Ra_RdLo $Rm $Rn
            | ARM_sat op cond Rn Rd Rm => arm_sat_il op $cond $Rn $Rd $Rm
            | ARM_hint cond op2 => arm_hint_il $cond $op2
            | ARM_SVC cond imm24 => arm_svc_il $cond $imm24
            | ARM_rev op cond Rd Rm => arm_rev_il op $cond $Rd $Rm
            | ARM_extend is_signed op cond Rn Rd rotate Rm => arm_extend_il is_signed op $cond $Rn $Rd $rotate $Rm
            | _ => arm_havoc
            end in
  Seq (Move R_PC (Word a 32)) il.

Definition arm_prog: program :=
  fun s a => match s R_T, s R_JF, a mod 4, a <? 2 ^ 32 with
             | 0, 0, 0, true =>
                 let i := arm_decode (Z.of_N (getmem 32 LittleE 4 (s V_MEM32) a)) in
                 match i with
                 | idk | ARM_UNPREDICTABLE => None
                 | _ => Some (4, arm2il a i)
                 end
             | _, _, _, _ => None
             end.

(********** well-typedness **********)

Ltac destruct_match := repeat match goal with |- context [ match ?x with _ => _ end ] => destruct x end.

Definition arm7typctx_temp := arm7typctx[V_TEMP 0 := Some 32].
Notation armc := arm7typctx (only parsing).
Notation armct := arm7typctx_temp (only parsing).

Lemma armct_sub: armc ⊆ armct.
Proof.
  unfold pfsub. intros. unfold armct. unfold update. destruct iseq. subst. discriminate. assumption.
Qed.
Lemma update_some:
  forall x y (c c': typctx),
    c x = Some y ->
    c ⊆ c' ->
    c ⊆ c'[x := Some y].
Proof.
  intros. rewrite <- store_upd_eq. assumption. apply H0. assumption.
Qed.

Lemma hastyp_arm_varid:
  forall c n,
    armc ⊆ c ->
    hastyp_exp c (Var (arm_varid n)) 32.
Proof.
  intros. apply hastyp_exp_weaken with (c1 := armc).
    unfold arm_varid; destruct_match; now constructor.
    assumption.
Qed.
Lemma sizeof_arm_varid:
  forall n, sizeof (arm_varid n) = 32.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.
Lemma typeof_arm_varid:
  forall n, arm7typctx (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. now destruct_match.
Qed.
Ltac etyp :=
  repeat match goal with
         | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ ?x _) _ => apply TBinOp with (w := s)
         | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ _ ?x) _ => apply TBinOp with (w := s)
         | |- hastyp_exp _ (BinOp _ (Word _ ?s) _) _ => apply TBinOp with (w := s)
         | |- hastyp_exp _ (BinOp _ _ (Word _ ?s)) _ => apply TBinOp with (w := s)
         | |- hastyp_exp _ (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := sizeof v)
         | |- hastyp_exp _ (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := sizeof v)
         | |- hastyp_exp _ (BinOp ?o ?x ?y) ?a => match eval compute in (widthof_binop o 0 =? 0) with true => apply TBinOp with (w := a) end
         | |- hastyp_exp _ (Var (arm_varid _)) 32 => apply hastyp_arm_varid
         | |- hastyp_exp _ (Var _) _ => apply TVar
         | |- hastyp_exp _ (Ite _ _ _) ?a => apply TIte with (w := 1)
         | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp
         | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
         | |- hastyp_exp _ (Word _ _) _ => apply TWord
         | |- hastyp_exp _ (Load _ _ _ _) _ => apply TLoad with (w := 32)
         | |- hastyp_exp _ (Store _ _ _ _ _) _ => apply TStore with (w := 32)
         | X: hastyp_exp _ ?x ?a, Y: hastyp_exp _ ?y ?b |- hastyp_exp _ (Concat ?x ?y) _ => apply TConcat with (w1 := a) (w2 := b)
         | |- pfsub arm7typctx arm7typctx  => reflexivity
         | |- context [R[_]] => unfold arm_R; destruct N.eqb
         | |- _ < _ => reflexivity
         | |- _ _ = Some _ => reflexivity
         end.
Ltac etypn size :=
  match goal with
  | |- hastyp_exp _ (BinOp _ _ _) _ => apply TBinOp with (w := size)
  | |- hastyp_exp _ (Cast _ _ _) _ => apply TCast with (w := size)
  | |- hastyp_exp _ (Extract _ _ _) _ => apply TExtract with (w := size)
  | |- _ <= _ => easy
  | |- _ < _ => reflexivity
  end.
Ltac etyps size := repeat (etyp + etypn size).
Ltac stypc c :=
  cbn; repeat match goal with
         | |- hastyp_stmt _ _ (Seq _ _) _ => apply TSeq with (c1 := c) (c2 := c)
         | |- hastyp_stmt _ _ (If _ _ _) _ => apply TIf with (c2 := c)
         | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
         | |- hastyp_stmt _ _ Nop _ => apply TNop
         | |- hastyp_stmt _ _ (Jmp _) _ => apply TJmp with (w := 32)
         | |- hastyp_stmt _ _ (Move temp0 _) _ => apply TMove with (w := 32)
         | |- hastyp_stmt _ _ (Move ?v _) _ => apply TMove with (w := sizeof v); [> right | | apply update_some]; try reflexivity
         | |- pfsub armc armc  => reflexivity
         | |- pfsub armc armct  => apply armct_sub
         | |- hastyp_exp _ _ _  => etyp
  end.
Ltac styp := stypc armc.
Ltac unfold_rec a :=
  match a with
  | ?x ?y => unfold_rec x
  | _ => unfold a
  end.
Ltac unfold_stmt := match goal with | |- hastyp_stmt _ _ ?a _ => unfold_rec a end.
Ltac stypu :=
  repeat match goal with
         | [ |- hastyp_stmt _ _ ?a _ ] => unfold_rec a
         | _ => styp
         end.

Lemma hastyp_setunknown:
  forall v, hastyp_stmt armc armc (setunknown v) armc.
Proof.
  destruct v; styp.
Qed.
Lemma hastyp_havoc:
  forall c,
    armc ⊆ c ->
    hastyp_stmt armc c arm_havoc c.
Proof.
  intros. unfold_stmt. stypc c; now try apply H.
Qed.
Lemma hastyp_arm_cond:
  forall c s,
    hastyp_stmt armc armc s armc ->
    hastyp_stmt armc armc (arm_cond_il c s) armc.
Proof.
  intros. unfold arm_cond_il. destruct_match; now styp.
Qed.
Lemma hastyp_DecodeImmShift:
  forall typ imm5 sr e,
    DecodeImmShift typ imm5 = (sr, e) ->
    imm5 < 2 ^ 32 ->
    hastyp_exp armc e 32.
Proof.
  intros typ imm5 sr e. unfold DecodeImmShift.
  destruct_match; intro; inversion H; now econstructor.
Qed.

Lemma hastyp_Shift_C:
  forall v t a ci r co,
    Shift_C v t a ci = (r, co) ->
    hastyp_exp armc v 32 ->
    hastyp_exp armc a 32 ->
    hastyp_exp armc ci 1 ->
    hastyp_exp armc r 32 /\ hastyp_exp armc co 1.
Proof.
  intros v t a ci r co. unfold Shift_C.
  split; destruct t; intros; inversion H; styp; first [now etyps 32 | now etyps 33].
Qed.

Lemma hastyp_R:
  forall c n,
    armc ⊆ c ->
    hastyp_exp c R[n] 32.
Proof.
  intros. unfold arm_R. destruct N.eqb; stypc c; now apply H.
Qed.
Lemma hastyp_assign_R:
  forall c n e,
    armc ⊆ c ->
    hastyp_exp c e 32 ->
    hastyp_stmt armc c (R[n] := e) c.
Proof.
  intros. unfold arm_assign_R. stypc c; rewrite sizeof_arm_varid; [
    > apply typeof_arm_varid
    | assumption
    | apply H; apply typeof_arm_varid ].
Qed.
Lemma hastyp_bxwritepc:
  forall c e,
    armc ⊆ c ->
      hastyp_exp c e 32 ->
      hastyp_stmt armc c (BXWritePC e) c.
Proof.
  intros. unfold BXWritePC. stypc c; first [now etyps 32 | now apply hastyp_havoc | now apply H].
Qed.
Lemma hastyp_memu:
  forall c a s,
    armc ⊆ c ->
    hastyp_exp c a 32 ->
    s <= 8 ->
    hastyp_exp c MemU[a, s] (s*8).
Proof.
  intros. unfold arm_MemU. etyp; try apply H; try easy; try lia.
Qed.
Lemma hastyp_assign_memu:
  forall c a s e,
    armc ⊆ c ->
    hastyp_exp c a 32 ->
    hastyp_exp c e (s*8) ->
    s <= 8 ->
    hastyp_stmt armc c (MemU[a, s] := e) c.
Proof.
  intros. unfold arm_assign_MemU. stypc c; try apply H; try easy; try lia.
Qed.
Ltac dshiftc :=
  let e := fresh "e" in
  destruct Shift_C eqn:e; apply hastyp_Shift_C in e; destruct e.
Ltac dimmshift :=
  let e := fresh "e" in
  let e1 := fresh "e1" in
  destruct DecodeImmShift eqn:e; apply hastyp_DecodeImmShift in e;
  [> dshiftc |].
Ltac hammer :=
  repeat match goal with
         | |- hastyp_stmt _ _ arm_havoc _ => apply hastyp_havoc
         | |- hastyp_stmt _ _ (arm_cond_il _ _) _ => apply hastyp_arm_cond
         | |- hastyp_exp _ R[_] _ => apply hastyp_R
         | |- hastyp_exp _ MemU[_, _] _ => apply hastyp_memu
         | |- hastyp_stmt _ _ (MemU[_, _] := _) _ => apply hastyp_assign_memu
         | |- hastyp_stmt _ _ (R[_] := _) _ => apply hastyp_assign_R
         | [ |- hastyp_stmt _ _ (BXWritePC _) _ ] => apply hastyp_bxwritepc
         | [ |- context [arm_data_flag] ] => unfold arm_data_flag
         | |- xbits _ ?i ?j < _ => transitivity (2^(j-i)); [> apply xbits_bound | reflexivity]
         | _ => styp
         end.
Lemma hastyp_arm_data:
  forall assign cond s Rd result carry overflow,
    hastyp_exp armc result 32 ->
    hastyp_exp armc carry 1 ->
    hastyp_exp armc overflow 1 ->
    hastyp_stmt armc armc (arm_data_il assign cond s Rd result carry overflow) armc.
Proof.
  intros. unfold_stmt. destruct_match; hammer; now etyps 32.
Qed.
Lemma hastyp_arm_data_op:
  forall op shiftc addwcarry,
    (forall f b,
      (forall x y,
        hastyp_exp armc x 32 ->
        hastyp_exp armc y 32 ->
        hastyp_exp armc (f x y) 32) ->
      hastyp_stmt armc armc (shiftc b f) armc) ->
    (forall f b,
      (forall x y,
        hastyp_exp armc x 32 ->
        hastyp_exp armc y 32 ->
        hastyp_exp armc (fst (fst (f x y))) 32
        /\ hastyp_exp armc (snd (fst (f x y))) 1
        /\ hastyp_exp armc (snd (f x y)) 1) ->
      hastyp_stmt armc armc (addwcarry b f) armc) ->
    hastyp_stmt armc armc (arm_data_op_il op shiftc addwcarry) armc.
Proof.
  intros. unfold_stmt. destruct_match; first
    [ apply H; intros; now etyp
    | apply H0; intros; repeat split; simpl; etyp;
        match goal with
        | |- context[Cast] => solve [etyps 1]
        | _ => assumption || etypn 32; now etyps 1
        end ].
Qed.
Lemma hastyp_arm_data_r:
  forall op cond s Rn Rd imm5 type Rm,
    imm5 < 2 ^ 5 ->
    hastyp_stmt armc armc (arm_data_r_il op cond s Rn Rd imm5 type Rm) armc.
Proof.
  intros. unfold_stmt. apply hastyp_arm_data_op; intros; unfold_stmt;
    (dimmshift; [ | now apply hastyp_R | assumption | hammer | lia ]).
      apply hastyp_arm_data; hammer; try apply H0; now hammer.
      destruct f eqn:?, p.
        specialize (H0 R[Rn] e1 (hastyp_R armc Rn ltac:(reflexivity)) H1).
        rewrite Heqp in H0. simpl in H0. destruct H0, H3. now apply hastyp_arm_data.
Qed.
Lemma hastyp_arm_data_rsr:
  forall op cond s Rn Rd Rs type Rm,
    hastyp_stmt armc armc (arm_data_rsr_il op cond s Rn Rd Rs type Rm) armc.
Proof.
  intros. unfold_stmt. apply hastyp_arm_data_op; intros; unfold_stmt; dshiftc; hammer.
    apply hastyp_arm_data; hammer; try apply H; now hammer.
    destruct f eqn:?, p.
      specialize (H R[Rn] e0 (hastyp_R armc Rn ltac:(reflexivity)) H0).
      rewrite Heqp in H. simpl in H. destruct H, H2. now apply hastyp_arm_data.
Qed.
Lemma hastyp_arm_data_i:
  forall op cond s Rn Rd imm12,
    hastyp_stmt armc armc (arm_data_i_il op cond s Rn Rd imm12) armc.
Proof.
  intros. unfold_stmt. apply hastyp_arm_data_op; intros; unfold_stmt; unfold ARMExpandImm_C;
    (dshiftc; hammer; [ | destruct xbits eqn:e; [ | specialize (xbits_bound imm12 8 12); rewrite e; simpl]; lia]).
      apply hastyp_arm_data; hammer; try apply H; now hammer.
      destruct f eqn:?, p.
        specialize (H R[Rn] e0 (hastyp_R armc Rn ltac:(reflexivity)) H0).
        rewrite Heqp in H. simpl in H. destruct H, H2. now apply hastyp_arm_data.
Qed.
Lemma hastyp_arm_mov_wt:
  forall is_w cond imm4 Rd imm12,
    imm4 < 2 ^ 4 ->
    imm12 < 2 ^ 12 ->
    hastyp_stmt armc armc (arm_mov_wt_il is_w cond imm4 Rd imm12) armc.
Proof.
  intros. unfold_stmt. destruct_match; hammer.
    apply (lor_bound 32); [> apply (shiftl_bound 20) | ]; lia.
    apply (shiftl_bound 16); apply (lor_bound 16); [> apply (shiftl_bound 4) | ]; lia.
Qed.
Lemma hastyp_arm_ls_i:
  forall op cond P U W Rn Rt imm12,
    imm12 < 2 ^ 12 ->
    hastyp_stmt armc armc (arm_ls_i_il op cond P U W Rn Rt imm12) armc.
Proof.
  intros. repeat unfold_stmt. destruct_match; hammer;
    match goal with
    | |- context[CAST_UNSIGNED] => etyps 8; hammer
    | |- context[CAST_LOW] => etyps 32
    | _ => idtac
    end; lia.
Qed.
Lemma hastyp_arm_ls_r:
  forall op cond P U W Rn Rt imm5 type Rm,
    imm5 < 2 ^ 5 ->
    hastyp_stmt armc armc (arm_ls_r_il op cond P U W Rn Rt imm5 type Rm) armc.
Proof.
  intros. repeat unfold_stmt. dimmshift; hammer.
    repeat unfold_stmt; destruct_match; hammer;
      match goal with
      | |- context[CAST_UNSIGNED] => etyps 8; hammer
      | |- context[CAST_LOW] => etyps 32
      | _ => idtac
      end; assumption || lia.
    assumption.
    lia.
Qed.
Lemma hastyp_arm_lsm_:
  forall f pc start_val wback_val cond W Rn register_list,
    start_val < 2 ^ 32 ->
    wback_val < 2 ^ 32 ->
    (forall n, hastyp_stmt armc armct (f n) armct) ->
    hastyp_stmt armc armct pc armct ->
    hastyp_stmt armc armc (arm_lsm_il_ f pc start_val wback_val cond W Rn register_list) armc.
Proof.
  intros. unfold_stmt. destruct_match; apply hastyp_arm_cond; apply TIf with (c2 := armc); stypc armct; try assumption.
  all: unfold for_0_14; stypc armct; [ now left | assumption | reflexivity | .. ].
  all: match goal with
       | |- context[pfsub] => reflexivity
       | |- context[if _ then _ else _] => destruct N.eqb; [ apply H1 | now apply TNop ]
       | _ => apply hastyp_assign_R; [ apply armct_sub | now styp ]
       end.
Qed.
Lemma hastyp_arm_lsm:
  forall op cond W Rn register_list,
    hastyp_stmt armc armc (arm_lsm_il op cond W Rn register_list) armc.
Proof.
  intros. repeat unfold_stmt. unfold arm_lsm_op_start, arm_lsm_op_wback.
  destruct_match; unfold_stmt; apply hastyp_arm_lsm_.
  all: match goal with
       | |- ofZ _ _ < _ => apply ofZ_bound
       | |- hastyp_stmt _ _ _ _ => now hammer
       | |- _ < _ => reflexivity
       | _ => intro
       end.
  all: stypc armct; [ destruct_match; now hammer | now left | now apply update_some | reflexivity ].
Qed.

Lemma hastyp_arm_bx:
  forall cond Rm,
    hastyp_stmt armc armc (arm_bx_il cond Rm) armc.
Proof.
  intros. unfold_stmt. hammer.
Qed.
Lemma hastyp_arm_blx_r:
  forall cond Rm,
    hastyp_stmt armc armc (arm_blx_r_il cond Rm) armc.
Proof.
  intros. unfold_stmt. apply hastyp_arm_cond. stypc armct; [ now left | now hammer .. ].
Qed.
Lemma hastyp_arm_b:
  forall cond imm24,
    hastyp_stmt armc armc (arm_b_il cond imm24) armc.
Proof.
  intros. repeat (unfold_stmt; hammer). apply ofZ_bound.
Qed.
Lemma hastyp_arm_bl:
  forall cond imm24,
    hastyp_stmt armc armc (arm_bl_il cond imm24) armc.
Proof.
  intros. repeat (unfold_stmt; hammer). apply ofZ_bound.
Qed.

Theorem welltyped_arm2il:
  forall a z,
    a < 2 ^ 32 ->
    hastyp_stmt armc armc (arm2il a (arm_decode z)) armc.
Proof.
  intros. unfold_stmt. styp. assumption.
  remember (arm_decode z) as i. revert Heqi.
  repeat match goal with
         | |- context[if ?a then _ else _] => destruct a eqn:?
         | |- context[i = ?a] => unfold_rec a
         end; intro; rewrite Heqi.
  all: match goal with
       | |- context[arm_data_i_il] => apply hastyp_arm_data_i
       | |- context[arm_data_rsr_il] => apply hastyp_arm_data_rsr
       | |- context[arm_data_r_il] => apply hastyp_arm_data_r
       | |- context[arm_mov_wt_il] => apply hastyp_arm_mov_wt
       | |- context[arm_ls_i_il] => apply hastyp_arm_ls_i
       | |- context[arm_ls_r_il] => apply hastyp_arm_ls_r
       | |- context[arm_lsm_il] => apply hastyp_arm_lsm
       | |- context[arm_bx_il] => apply hastyp_arm_bx
       | |- context[arm_blx_r_il] => apply hastyp_arm_blx_r
       | |- context[arm_b_il] => apply hastyp_arm_b
       | |- context[arm_bl_il] => apply hastyp_arm_bl
       | _ => hammer
       end.
  all: match goal with
       | |- Z.to_N (_ _ ?a ?b) < _ => change a with (Z.of_N $a); change b with (Z.of_N $b); rewrite zxbits_eq, <- xbits_Z2N; [ apply xbits_bound | lia ]
       | |- context[hastyp_stmt] => repeat (unfold_stmt; destruct_match; hammer)
       end.
Qed.
Theorem welltyped_arm_prog:
  welltyped_prog arm7typctx arm_prog.
Proof.
  intros s a. unfold arm_prog.
    destruct (s R_T), (s R_JF), (a mod 4); destruct (a <? 2 ^ 32) eqn:l; try apply I.
    rewrite N.ltb_lt in l.
    destruct arm_decode eqn:e; try apply I; rewrite <- e; exists armc; now apply welltyped_arm2il.
Qed.
