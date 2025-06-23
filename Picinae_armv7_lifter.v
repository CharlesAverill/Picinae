(* decoder/lifter for ARMv7 *)

Require Export Picinae_armv7.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
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

Inductive arm_data_op :=
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
Inductive arm_mul_op :=
  | ARM_MUL
  | ARM_MLA
  | ARM_UMAAL
  | ARM_MLS
  | ARM_UMULL
  | ARM_UMLAL
  | ARM_SMULL
  | ARM_SMLAL.
Inductive arm_sat_op :=
  | ARM_QADD
  | ARM_QSUB
  | ARM_QDADD
  | ARM_QDSUB.
Inductive arm_mem_op :=
  (* unpriviledged load/stores have a different mnemonic but can be determined by P and W fields *)
  | ARM_LDR
  | ARM_STR
  | ARM_LDRB
  | ARM_STRB.
Inductive arm_xmem_op :=
  | ARM_STRH
  | ARM_LDRH
  | ARM_LDRD
  | ARM_LDRSB
  | ARM_STRD
  | ARM_LDRSH.
Inductive arm_memm_op :=
  | ARM_STMDA
  | ARM_LDMDA
  | ARM_STMDB (* called PUSH when wback and rn=sp *)
  | ARM_LDMDB
  | ARM_STMIA
  | ARM_LDMIA (* called POP when wback rn=sp *)
  | ARM_STMIB
  | ARM_LDMIB.
Inductive arm_sync_size :=
  | ARM_sync_word
  | ARM_sync_doubleword
  | ARM_sync_byte
  | ARM_sync_halfword.
Inductive arm7_asm :=
  (* causes undefined instruction exception *)
  | ARM_UNDEFINED
  (* no behaviour guaranteed *)
  | ARM_UNPREDICTABLE
  (* decoding not implemented yet, treat as unpredictable *)
  | x

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
  (* synchronization load: A5.2.10, pg A5-203 *)
  | ARM_sync_l (size: arm_sync_size) (cond Rn Rt: Z)
  (* synchronization store: A5.2.10, pg A5-203 *)
  | ARM_sync_s (size: arm_sync_size) (cond Rn Rd Rt: Z)
  (* miscellaneous instructions: A5.2.12, pg A5-205 *)
  | ARM_MRS (cond Rd: Z)
  | ARM_MSR (cond mask Rn: Z)
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

  (* load/store multiple: A5.5, pg A5-212 *)
  | ARM_lsm (op: arm_memm_op) (cond W Rn register_list: Z)
  (* branch: A5.5, pg A5-212 *)
  | ARM_B (cond imm24: Z)
  | ARM_BL (cond imm24: Z)
  | ARM_BLX_i (H imm24: Z)
      .

Definition zxbits z i j := Z.shiftr z i mod Z.shiftl Z1 (Z.max Z0 (j - i)).
Definition zcbits z1 i z2 := Z.lor (Z.shiftl z1 i) z2.
Definition bitb z b := zxbits z b (b + Z1).
Notation "x !=? y" := (negb (Z.eqb x y)) (at level 25).

Definition armcond z := zxbits z Z28 Z32.


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
Definition arm_decode_data_rd0 (kind: arm_data_op -> Z -> arm7_asm) op z :=
  let Rd := zxbits z Z12 Z16 in
  if (Rd !=? Z0) then ARM_UNPREDICTABLE
  else kind op z.
Definition arm_decode_data_rn0 (kind: arm_data_op -> Z -> arm7_asm) op z :=
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
Definition arm_decode_mrs z := (* A8.8.110, pg A8-497 *)
  let cond := armcond z in
  let Rd := zxbits z Z12 Z16 in
  if (zxbits z Z16 Z20 !=? Z15) || (zxbits z Z0 Z12 !=? Z0) || (Rd =? Z15) then ARM_UNPREDICTABLE
  else ARM_MRS cond Rd.
Definition arm_decode_msr_a z := (* A8.8.113, pg A8-501 *)
  let cond := armcond z in
  let mask := zxbits z Z18 Z20 in
  let Rn := zxbits z Z0 Z4 in
  if (zxbits z Z8 Z12 !=? Z0) || (zxbits z Z12 Z16 !=? Z15) || (Rn =? Z15) || (mask =? Z0) then ARM_UNPREDICTABLE
  else ARM_MSR cond mask Rn.
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
      if (op =? Z0) || (op =? Z2) then x (*mrs*)
      else if (op =? Z1) then x (*msr reg*)
      else if (op =? Z3) then x (*msr reg*)
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

Definition arm_decode_halfword_multiply z := (* A5.2.7, pg A5-200,201 *)
  let op1 := zxbits z Z21 Z23 in
  let op := bitb z Z5 in
  if (op1 =? Z0) then x (*smlabb*)
  else if (op1 =? Z1) then
    if (op =? Z0) then x (*smlawb*)
    else x (*smulwb*)
  else if (op1 =? Z2) then x (*smlalbb*)
  else x (*smulbb*).

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
  let op := zxbits z Z24 Z28 in
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
  let Rt := zxbits z Z0 Z4 in
  if (Rt =? Z15) || (Rn =? Z15) then ARM_UNPREDICTABLE
  else if (zxbits z Z8 Z12 !=? Z15) || (zxbits z Z0 Z4 !=? Z15) then ARM_UNPREDICTABLE
  else if (match size with ARM_sync_doubleword => true | _ => false end) && ((bitb Rt Z0 =? Z1) || (Rt =? Z14)) then ARM_UNPREDICTABLE
  else ARM_sync_l size cond Rn Rt.
Definition arm_decode_sync_primitives z := (* A5.2.10, pg A5-203 *)
  let op := zxbits z Z20 Z24 in (* 3210:
     3=0 - swp/swpb, 3=1 - load/store exclusive
     2:1 - size
     0=0 - store, 0=1 - load *)
  if (bitb op Z3 =? Z0) then x (* swp/swpb *)
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
    else x (*msr imm*)
  else x (*msr imm*).

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
  let is_byte := bitb z Z22 =? Z1 in
  if (Rm =? Z15) || (wback && ((Rn =? Z15) || (Rn =? Rt))) then ARM_UNPREDICTABLE (* also "wback && m == n" if archversion < 6 but we are armv7 *)
  else if (is_byte) && (Rt =? Z15) then ARM_UNPREDICTABLE
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
  else if (is_byte) && (Rt =? Z15) then ARM_UNPREDICTABLE
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

Definition arm_decode_media (z: Z) :=
  x.

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

Definition arm_decode_coprocessor z := (* A5.6, pg A5-213 *)
  let op1 := zxbits z Z20 Z26 in
  let op := bitb z Z4 in
  let coproc := zxbits z Z8 Z12 in
  if (zxbits op1 Z1 Z6 =? Z0) then ARM_UNDEFINED
  else if (zxbits op1 Z4 Z6 =? Z3) then x (*svc*)
  else
    if (coproc =? Z10) || (coproc =? Z11) then (* coproc = 101x *)
      if (zxbits op1 Z4 Z6 =? Z2) then
        if (op =? Z0) then x (*floating point data*)
        else x (*8,16,32bit transfer*)
      else if (zxbits op1 Z1 Z6 =? Z2) then x (*64bit transfer*)
      else x (*extension load/store*) (* op1 = 0xxxxx not 000x0x *)
    else (* coproc = not 101x *)
      if (op1 =? Z4) then x (*mcrr*)
      else if (op1 =? Z5) then x (*mcrc*)
      else if (zxbits op1 Z4 Z6 =? Z2) then
        if (op =? Z0) then x (*cdp*)
        else if (bitb op1 Z0 =? Z0) then x (*mcr*)
        else x (*mrc*)
      else if (bitb op1 Z0 =? Z0) then x (*stc*)
      else x (*ldc*).

Definition arm_decode_unconditional z := (* A5.7, pg A5-214 *)
  let op1 := zxbits z Z20 Z28 in
  let op := bitb z Z4 in
  let op1_5 := zxbits op1 Z0 Z5 in
  let op1_3 := zxbits op1 Z5 Z8 in
  if (op1_3 =? Z0) || (op1_3 =? Z1) || (op1_3 =? Z2) || (op1_3 =? Z3) then x (*mem hints*)
  else if (op1_3 =? Z4) then
    if (bitb op1 Z0 =? Z0) && (bitb op1 Z2 =? Z1) then ARM_UNPREDICTABLE (*srs, unpredictable in user mode*)
    else if (bitb op1 Z0 =? Z1) && (bitb op1 Z2 =? Z0) then ARM_UNPREDICTABLE (*rfe, unpredictable in user mode*)
    else ARM_UNDEFINED
  else if (op1_3 =? Z5) then arm_decode_blx_i z
  else if (op1_3 =? Z6) then
    if (op1_5 =? Z4) then x (*mcrr*)
    else if (op1_5 =? Z5) then x (*mrrc*)
    else if (bitb op1 Z0 =? Z0) && (op1_5 !=? Z0) && (op1_5 !=? Z4) then x (*stc*)
    else if (bitb op1 Z0 =? Z1) && (op1_5 !=? Z1) && (op1_5 !=? Z5) then x (*ldc*)
    else ARM_UNDEFINED
  else if (op1_3 =? Z7) && (bitb op1 Z4 =? Z0) then
    if (op =? Z0) then x (*cdp*)
    else if (bitb op1 Z0 =? Z0) then x (*mcr*)
    else x (*mrc*)
  else ARM_UNDEFINED.

Definition arm_decode z :=
  let cond := zxbits z Z28 Z32 in
  let op1 := zxbits z Z25 Z28 in
  let op := bitb z Z4 in
  if (cond =? Z15) then arm_decode_unconditional z
  else
    if (op1 =? Z0) || (op1 =? Z1) then arm_decode_data_misc z
    else if (op1 =? Z2) || (op1 =? Z3) && (op =? Z0) then arm_decode_load_store z
    else if (op1 =? Z3) && (op =? Z1) then arm_decode_media z
    else if (op1 =? Z4) || (op1 =? Z5) then arm_decode_branch_block_transfer z
    else (*if (op1 =? Z6) || (op1 =? Z7) then*) arm_decode_coprocessor z.

(* todo: fix lifting for new decoder

(* ----------------------------- Intermediate Language Translation -----------------------------*)
(* Make stmt conditional, where n is the value of the cond field *)
Definition arm_cond n stmt :=
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
  | 14 | 15 => stmt
  | _ => Exn 6
  end.

(* Covert the second operand of data-processing and load/store instructions into an IL expression,
   where i is the bit indicating if it is an immediate or register operand and op2 is the 12-bit field *)
Definition arm_op2 i op2 :=
  match i with
  (* register / register-shifted register *)
  (* the first 4 bits hold a register id *)
  (* bits 5,6 indicate the type of rotation (left, right, arithmetic right, rotate right) *)
  (* bit 4 indicates if the shift amount is an immediate or register *)
  (* the last 5 bits hold an immediate value or a register id *)
  | 0 => let reg := Var (arm_varid (xbits op2 0 4)) in
         let type := xbits op2 5 7 in
         let shift := match (bitn op2 4) with
                      | 0 => Word (xbits op2 7 12) 32 (* register *)
                      | _ => BinOp OP_AND (Var (arm_varid (xbits op2 8 12))) (Word 255 32) (* register-shifted register *)
                      end in
         match type with (* TODO: edge cases like LSR #0 *)
         | 0 => BinOp OP_LSHIFT reg shift
         | 1 => BinOp OP_RSHIFT reg shift
         | 2 => BinOp OP_ARSHIFT reg shift
         | _ => BinOp OP_OR (BinOp OP_RSHIFT reg shift) (BinOp OP_LSHIFT reg (BinOp OP_MINUS (Word 32 32) shift))
         end
  (* immediate *)
  (* the first 8 bits hold an immediate value *)
  (* the last 4 bits hold the rotation value *)
  (* the operand = imm rotated right by 2*rot *)
  | _ => let imm := xbits op2 0 8 in
         let rot := xbits op2 8 12 in
         Word (N.land (N.shiftr (cbits imm 32 imm) (rot + rot)) (N.ones 32)) 32
  end.

(* Like arm_op2, but return the carry value *)
Definition arm_op2_carry i op2 :=
  match i with
  (* register / register-shifted register *)
  | 0 => let reg := Var (arm_varid (xbits op2 0 4)) in
         let type := xbits op2 5 7 in
         let shift := match (bitn op2 4) with
                      | 0 => Word ((xbits op2 7 12) - 1) 32 (* register *)
                      | _ => BinOp OP_MINUS (BinOp OP_AND (Var (arm_varid (xbits op2 8 12))) (Word 255 32)) (Word 1 32) (* register-shifted register *)
                      end in
         match type with (* TODO: edge cases like LSR #0 *)
         | 0 => Cast CAST_LOW 1 (BinOp OP_LSHIFT reg shift)
         | _ => Cast CAST_LOW 1 (BinOp OP_RSHIFT reg shift)
         end
  (* immediate *)
  | _ => let imm := xbits op2 0 8 in
         let rot := xbits op2 8 12 in
         (* TODO: this is well defined in the manual, but the pcode lifter just says its unknown so i will leave it like this *)
         Unknown 1
  end.

(* Get the offset address in a load/store instruction *)
Definition arm_load_store_offset_addr A op1 rn op2 :=
  let offset := match A with
                | 0 => Word (xbits op2 0 12) 32
                | _ => arm_op2 A op2
                end in
  match bitn op1 3 with
  | 0 => BinOp OP_MINUS (arm_var rn) offset
  | _ => BinOp OP_PLUS (arm_var rn) offset
  end.

(* Get the IL stmt that updates the register for load instructions / updates memory for store instructions *)
Definition arm_load_store_move_il type byte rt address :=
  match type, byte with
  | 0, 0 => Move (arm_varid rt) (Load (Var V_MEM32) address LittleE 4)
  | 0, _ => Move (arm_varid rt) (Cast CAST_UNSIGNED 32 (Load (Var V_MEM32) address LittleE 1))
  | _, 0 => Move V_MEM32 (Store (Var V_MEM32) address (arm_var rt) LittleE 4)
  | _, _ => Move V_MEM32 (Store (Var V_MEM32) address (Cast CAST_LOW 8 (arm_var rt)) LittleE 1)
  end.

(* Get the offset address in a load/store instruction *)
Definition arm_load_store_halfword_addr op1 rn op2 :=
  match op1 with
  | 4| 5 | 6 | 7 => arm_load_store_offset_addr 0 op1 rn op2
  | _ => arm_load_store_offset_addr 1 op1 rn op2
  end.

(* Get the il for loading halfwords *)
Definition arm_load_h_il cond op1 rn rt op2 bytes :=
  let offset_addr := arm_load_store_halfword_addr op1 rn op2 in
  let addr := match bitn op1 4 with
              | 0 => arm_var rn
              | _ => offset_addr
              end in
  let data := Load (Var V_MEM32) addr LittleE bytes in
  let wback := match bitn op1 4 with 
               | 0 => 1
               | _ => bitn op1 1
               end in
  match wback with
  | 1 => arm_cond cond (Seq (Move (arm_varid rt) data) (Move (arm_varid rn) offset_addr))
  | _ => arm_cond cond ((Move (arm_varid rt) data))
  end.

(*TODO: ldrt il traditionally has nullchecking for thumb but since we are not encoding thumb that will be a todo*)
Definition arm_load_store_il type byte cond A op1 rn rt op2 :=
  let offset_addr := arm_load_store_offset_addr A op1 rn op2 in
  let address := match bitn op1 4 with
                 | 0 => arm_var rn
                 | _ => offset_addr
                 end in
  let move_il := arm_load_store_move_il type byte rt address in
  match bitn op1 1, bitn op1 4 with
  | 0, 1 => arm_cond cond move_il
  | _, _ => arm_cond cond (Seq move_il (Move (arm_varid rn) offset_addr))
  end.

(* IL for data-processing instructions that have an equivalent IL binop, excluding flag setting *)
(* Save the result of the operation to V_TEMP 0 first,
   since if the destination is the same as one of the operands,
   it can mess up the flag computation. *)
Definition arm_data_binop binop i rn op2 :=
  (Move (V_TEMP 0) (BinOp binop (Var (arm_varid rn)) (arm_op2 i op2))).

(* IL for data-processing instructions that do not have an equivalent IL binop, excluding flag setting *)
Definition arm_data f i rn op2 :=
  (Move (V_TEMP 0) (f (Var (arm_varid rn)) (arm_op2 i op2))).

(* After flags have been set, the destination register can be updated *)
Definition arm_data_commit rd :=
  Move (arm_varid rd) (Var (V_TEMP 0)).

(* IL for setting flags *)
Definition arm_setzf :=
  Move R_ZF (BinOp OP_EQ (Var (V_TEMP 0)) (Word 0 32)).
Definition arm_setnf :=
  Move R_NF (Cast CAST_HIGH 1 (Var (V_TEMP 0))).
Definition arm_setcf e1 e2 :=
  Move R_CF (BinOp OP_LT e2 e1).
Definition signof expr :=
  Cast CAST_HIGH 1 expr.
Definition samesign e1 e2 :=
  BinOp OP_EQ (signof e1) (signof e2).
Definition diffsign e1 e2 :=
  BinOp OP_NEQ (signof e1) (signof e2).
Definition overflow e1 e2 e3 :=
  BinOp OP_AND (samesign e1 e2) (diffsign e1 e3).
Definition arm_setvf e1 e2 e3 :=
  Move R_VF (overflow e1 e2 e3).

(* Sets the flags for an instruction using the ShiftC() pseudofunction *)
Definition arm_shiftc_flag i op2 :=
  Seq (arm_setzf) (Seq (arm_setnf) (Move R_CF (arm_op2_carry i op2))).
(* Sets the flags for an instruction using the AddWithCarry() pseudofunction *)
Definition arm_addwcarry_flag x y_plus_carryin :=
  Seq (arm_setzf) (Seq (arm_setnf) (Seq (arm_setcf x (Var (V_TEMP 0))) (arm_setvf x y_plus_carryin (Var (V_TEMP 0))))).

(* Turns a (data processing) instruction into the IL specifically for setting flags *)
Definition arm2flagil inst :=
  match inst with
  | ARM_AND cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_EOR cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_SUB cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_RSB cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_ADD cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (arm_op2 i op2)
  | ARM_ADC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (arm_op2 i op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_SBC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (UnOp OP_NOT (arm_op2 i op2)) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_RSC cond i 1 rn rd op2 => arm_addwcarry_flag (arm_var rn) (BinOp OP_PLUS (UnOp OP_NOT (arm_op2 i op2)) (Cast CAST_UNSIGNED 32 (Var R_CF)))
  | ARM_TST cond i   rn    op2 => arm_shiftc_flag i op2
  | ARM_TEQ cond i   rn    op2 => arm_shiftc_flag i op2
  | ARM_CMP cond i   rn    op2 => arm_addwcarry_flag (arm_var rn) (UnOp OP_NEG (arm_op2 i op2))
  | ARM_CMN cond i   rn    op2 => arm_addwcarry_flag (arm_var rn) (arm_op2 i op2)
  | ARM_ORR cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_MOV cond i 1    rd op2 => arm_shiftc_flag i op2
  | ARM_BIC cond i 1 rn rd op2 => arm_shiftc_flag i op2
  | ARM_MVN cond i 1    rd op2 => arm_shiftc_flag i op2
  | _ => Nop
  end.

Fixpoint arm_pushil (n : N) (i : nat) :=
  let sp := Move R_SP (BinOp OP_MINUS (Var R_SP) (Word 4 32)) in
  let store := Move V_MEM32 (Store (Var V_MEM32) (Var R_SP) (arm_var (N.of_nat i)) LittleE 4) in
  match i, bitn n (N.of_nat i) with
  | O, 0 => Nop
  | O, _ => Seq sp store
  | S i', 0 => arm_pushil n i'
  | S i', _ => Seq sp (Seq store (arm_pushil n i'))
  end.
Fixpoint arm_popil (n : N) (i : nat) :=
  let sp := Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 4 32)) in
  let load := Move (arm_varid (15 - N.of_nat i)) (Load (Var V_MEM32) (Var R_SP) LittleE 4) in
  match i, bitn n (15 - N.of_nat i) with
  | O, 0 => Nop
  | O, _ => Seq load (Seq sp (Jmp (Var R_PC)))
  | S i', 0 => arm_popil n i'
  | S i', _ => Seq load (Seq sp (arm_popil n i'))
  end.

Definition arm2il (a:addr) inst :=
  match inst with
  | ARM_AND cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_AND i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_EOR cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_XOR i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_SUB cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_MINUS i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_RSB cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS op2 rn)) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_ADD cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_PLUS i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_ADC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_PLUS (BinOp OP_PLUS rn op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_SBC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS (BinOp OP_MINUS rn op2) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_RSC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => (BinOp OP_MINUS (BinOp OP_MINUS op2 rn) (Cast CAST_UNSIGNED 32 (Var R_CF)))) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_TST cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_AND i rn op2)
                                                  (arm2flagil inst))
  | ARM_TEQ cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_XOR i rn op2)
                                                  (arm2flagil inst))
  | ARM_CMP cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_MINUS i rn op2)
                                                  (arm2flagil inst))
  | ARM_CMN cond i   rn    op2 => arm_cond cond (Seq (arm_data_binop OP_PLUS i rn op2)
                                                  (arm2flagil inst))
  | ARM_ORR cond i s rn rd op2 => arm_cond cond (Seq (arm_data_binop OP_OR i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_MOV cond i s    rd op2 => arm_cond cond (Seq (Move (V_TEMP 0) (arm_op2 i op2))
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_BIC cond i s rn rd op2 => arm_cond cond (Seq (arm_data (fun rn op2 => BinOp OP_AND rn (UnOp OP_NOT op2)) i rn op2)
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))
  | ARM_MVN cond i s    rd op2 => arm_cond cond (Seq (Move (V_TEMP 0) (UnOp OP_NEG (arm_op2 i op2)))
                                                  (Seq (arm2flagil inst) (arm_data_commit rd)))

  | ARM_MOVT cond imm4 rd imm12 => arm_cond cond (Move (arm_varid rd) (BinOp OP_OR
                                                   (BinOp OP_AND (arm_var rd) (Word 0xffff 32))
                                                   (Word (N.shiftl (cbits imm4 12 imm12) 16) 32)))
  | ARM_MOVW cond imm4 rd imm12 => arm_cond cond (Move (arm_varid rd) (Word (cbits imm4 12 imm12) 32))

  | ARM_LDR cond A op1 rn B rt op2 => arm_load_store_il 0 0 cond A op1 rn rt op2
  | ARM_LDRT cond A op1 rn B rt op2 => arm_load_store_il 0 0 cond A op1 rn rt op2
  | ARM_LDRB cond A op1 rn B rt op2 => arm_load_store_il 0 1 cond A op1 rn rt op2
  | ARM_LDRBT cond A op1 rn B rt op2 => arm_load_store_il 0 1 cond A op1 rn rt op2

  | ARM_STR cond A op1 rn B rt op2 => arm_load_store_il 1 0 cond A op1 rn rt op2
  | ARM_STRT cond A op1 rn B rt op2 => arm_load_store_il 1 0 cond A op1 rn rt op2
  | ARM_STRB cond A op1 rn B rt op2 => arm_load_store_il 1 1 cond A op1 rn rt op2
  | ARM_STRBT cond A op1 rn B rt op2 => arm_load_store_il 1 1 cond A op1 rn rt op2

  | ARM_B cond imm24 => arm_cond cond (Jmp (Word (sbop1 Z.add 32 (a + 8) (scast 26 32 (N.shiftl imm24 2))) 32))
  | ARM_BL cond imm24 => arm_cond cond (Seq (Move R_LR (BinOp OP_MINUS (Var R_PC) (Word 4 32)))
                                           (Jmp (Word (sbop1 Z.add 32 (a + 8) (scast 26 32 (N.shiftl imm24 2))) 32)))
  | ARM_BLX cond rm => arm_cond cond (Seq (Move R_LR (BinOp OP_MINUS (Var R_PC) (Word 4 32))) (Jmp (arm_var rm))) 
  | ARM_BX cond rm => arm_cond cond (Jmp (arm_var rm))

  | ARM_POP cond regs => arm_cond cond (arm_popil regs 16)
  | ARM_PUSH cond regs => arm_cond cond (arm_pushil regs 16)
  
  | ARM_NOP cond => arm_cond cond Nop

  | ARM_SVC cond imm24 => arm_cond cond (Exn (imm24 mod 2^16))
  
  | _ => Exn 6
  end.

Definition arm_stmt m a :=
  arm2il a match a mod 4 with 0 => arm_decode (getmem 32 LittleE 4 m a) | _ => ARM_InvalidI end.

Definition arm_prog : program :=
  fun s a => Some (4, arm_stmt (getmem 32 LittleE 1 (s V_MEM32) a) a).

(* Well-typedness proof *)

(* The only temp variable used is V_TEMP 0, and it is always a NumT 32 *)
Definition arm7tempctx := arm7typctx[V_TEMP 0 := Some 32].

Ltac destruct_match :=
  repeat match goal with |- context [ match ?x with _ => _ end ] =>
    destruct x
  end.

Lemma has_type_xbits:
  forall n i j w c, 2 ^ (j - i) < 2 ^ w -> arm7typctx ⊆ c -> hastyp_exp c (Word (xbits n i j) w) (w).
Proof.
  intros. apply TWord. transitivity (2 ^ (j - i)). apply xbits_bound. assumption.
Qed.

Lemma update_some:
  forall x y (c c': typctx), c x = Some y -> c ⊆ c' -> c ⊆ c'[x := Some y].
Proof.
  intros. rewrite <- store_upd_eq. assumption. apply H0. assumption.
Qed.

Lemma arm7tempctx_subset:
  arm7typctx ⊆ arm7tempctx.
Proof.
  unfold pfsub. intros. unfold arm7tempctx. unfold update. destruct iseq. subst. discriminate. assumption.
Qed.

Lemma has_type_arm_cond:
  forall n stmt, hastyp_stmt arm7typctx arm7typctx stmt arm7typctx ->
    hastyp_stmt arm7typctx arm7typctx (arm_cond n stmt) arm7typctx.
Proof.
  intros. unfold arm_cond. destruct_match.
    all: repeat first
      [ apply TBinOp with (w := 1)
      | econstructor
      | reflexivity
      | apply H ].
Qed.

Lemma varid_type:
  forall n c, arm7typctx ⊆ c -> c (arm_varid n) = Some 32.
Proof.
  intros. unfold arm_varid. destruct_match; apply H; reflexivity.
Qed.

Lemma has_type_varid:
  forall n c, arm7typctx ⊆ c -> hastyp_exp c (Var (arm_varid n)) 32.
Proof.
  intros. apply TVar. apply varid_type. assumption.
Qed.

Lemma has_type_op2:
  forall i n c, arm7typctx ⊆ c -> hastyp_exp c (arm_op2 i n) 32.
Proof.
  intros. unfold arm_op2. destruct_match.
  13: apply TWord; rewrite N.land_comm; apply land_bound; reflexivity.
  all: repeat first
    [ apply TBinOp with (w := 32)
    | apply has_type_varid
    | apply has_type_xbits
    | constructor
    | reflexivity
    | destruct (xbits _ 4 5)
    | assumption ].
Qed.

Lemma has_type_setzf:
  hastyp_stmt arm7typctx arm7tempctx arm_setzf arm7tempctx.
Proof.
  unfold arm_setzf. eapply TMove.
    right. reflexivity.
    apply TBinOp with (w := 32).
      apply TVar; reflexivity.
      apply TWord; reflexivity.
    apply update_some; reflexivity.
Qed.

Lemma has_type_setnf:
  hastyp_stmt arm7typctx arm7tempctx arm_setnf arm7tempctx.
Proof.
  unfold arm_setnf. eapply TMove.
    right; reflexivity.
    apply TCast with (w:=32).
      apply TVar; reflexivity.
      apply N.lt_le_incl; reflexivity.
    apply update_some; reflexivity.
Qed.

Lemma has_type_data_binop:
  forall bop n1 n2 n3, hastyp_stmt arm7typctx arm7typctx (arm_data_binop bop n1 n2 n3)
                         (arm7typctx[V_TEMP 0 := Some (widthof_binop bop 32)]).
Proof.
  intros. unfold arm_data_binop. eapply TMove.
    left; reflexivity.
    apply TBinOp.
      apply has_type_varid; reflexivity.
      apply has_type_op2; reflexivity.
    reflexivity.
Qed.

Lemma lt_sub:
  forall x y z, x < y -> x - z < y.
Proof.
  intros. assert (x - z <= x). apply N.le_sub_l.
  rewrite N.le_lteq in H0. destruct H0.
    transitivity x; assumption.
    rewrite H0; assumption.
Qed.

Lemma has_type_shiftc:
  forall i op2, hastyp_stmt arm7typctx arm7tempctx (arm_shiftc_flag i op2) arm7tempctx.
Proof.
  intros. unfold arm_shiftc_flag. eapply TSeq. 3: reflexivity.
    apply has_type_setzf.
    eapply TSeq. 3: reflexivity.
      apply has_type_setnf.
      eapply TMove. 3: apply update_some; reflexivity.
        right; reflexivity.
        unfold arm_op2_carry. destruct_match.
          all: repeat first 
            [ apply TBinOp with (w := 32)
            | econstructor
            | apply N.lt_le_incl
            | apply varid_type
            | apply arm7tempctx_subset
            | reflexivity ].
          all: apply lt_sub; transitivity (2 ^ 5); solve [ apply xbits_bound | reflexivity ].
Qed.

Lemma has_type_data_commit:
  forall n, hastyp_stmt arm7typctx arm7tempctx (arm_data_commit n) arm7typctx.
Proof.
  intros. unfold arm_data_commit. apply TMove with (w := 32).
    right; apply varid_type; reflexivity.
    apply TVar; reflexivity.
    apply update_some.
      apply varid_type; reflexivity.
      apply arm7tempctx_subset.
Qed.

Lemma has_type_signof:
  forall e, hastyp_exp arm7tempctx e 32 -> hastyp_exp arm7tempctx (signof e) 1.
Proof.
  intros. unfold signof. apply TCast with (w := 32).
    assumption.
    apply N.lt_le_incl; reflexivity.
Qed.

Lemma has_type_addwcarry_flag:
  forall n e, hastyp_exp arm7tempctx e 32 -> hastyp_stmt arm7typctx arm7tempctx
    (arm_addwcarry_flag (arm_var n) e)
    arm7tempctx.
Proof.
  intros. unfold arm_addwcarry_flag. eapply TSeq with (c2 := arm7tempctx).
    apply has_type_setzf. 2: reflexivity.
  eapply TSeq with (c2 := arm7tempctx).
    apply has_type_setnf. 2: reflexivity.
  eapply TSeq with (c1 := arm7tempctx) (c2 := arm7tempctx).
    unfold arm_setcf. eapply TMove.
      right; reflexivity.
      apply TBinOp with (w := 32).
        eapply TVar; reflexivity.
        apply has_type_varid; apply arm7tempctx_subset.
      apply update_some; reflexivity.
    unfold arm_setvf. eapply TMove.
      right; reflexivity.
      unfold overflow. apply TBinOp with (w := 1).
        unfold samesign. apply TBinOp with (w := 1).
          apply has_type_signof. apply has_type_varid. apply arm7tempctx_subset.
          apply has_type_signof. apply H.
        unfold diffsign. apply TBinOp with (w := 1).
          apply has_type_signof. apply has_type_varid. apply arm7tempctx_subset.
          apply has_type_signof. apply TVar. reflexivity.
      apply update_some. all: reflexivity.
Qed.

Lemma has_type_flagil:
  forall i, hastyp_stmt arm7typctx arm7tempctx (arm2flagil i) arm7tempctx.
Proof.
  intros. unfold arm2flagil. destruct_match.
    all: repeat first
      [ apply has_type_shiftc
      | apply has_type_addwcarry_flag
      | apply has_type_op2
      | apply TBinOp with (w := 32)
      | apply N.lt_le_incl
      | econstructor
      | reflexivity
      | apply arm7tempctx_subset ].
Qed.

Lemma has_type_data_op:
  forall a n1 n2 n3 n4 n5 n6 n7,
    hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_data_opcode n1 n2 n3 n4 n5 n6 n7)) arm7typctx.
Proof.
  intros. unfold arm_data_opcode. destruct_match.
    all: unfold arm2il.
    all: repeat first
      [ apply has_type_arm_cond
      | apply has_type_flagil
      | apply has_type_data_commit
      | reflexivity
      | constructor
      | apply arm7tempctx_subset
      | eapply TSeq ].
    all: try apply has_type_data_binop. all: unfold arm_data.
    all: repeat first
      [ econstructor
      | apply has_type_op2
      | apply varid_type
      | reflexivity
      | apply N.lt_le_incl ].
Qed.

Lemma has_type_extra_load_store:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_extra_load_store n)) arm7typctx.
Proof.
  intros. unfold arm_decode_extra_load_store. destruct_match.
    all: unfold arm2il; constructor; reflexivity.
Qed.
Lemma has_type_mul_and_sync:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_mul_and_sync n)) arm7typctx.
Proof.
  intros. unfold arm_decode_mul_and_sync. constructor. reflexivity.
Qed.

Lemma has_type_data:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_data n)) arm7typctx.
Proof.
  intros. unfold arm_decode_data, arm_decode_misc. destruct_match.
    all: try solve [ apply has_type_data_op | apply has_type_extra_load_store | apply has_type_mul_and_sync ] .
    all: unfold arm2il; apply has_type_arm_cond.
    all: try eapply TJmp; try apply has_type_varid; try reflexivity.
    apply TMove with (w := 32).
      right; apply varid_type; reflexivity.
      repeat apply TBinOp with (w := 32).
        apply has_type_varid; reflexivity.
        apply TWord; reflexivity.
        apply TWord. unfold cbits. rewrite N.shiftl_lor. apply lor_bound.
          rewrite N.shiftl_shiftl. apply (shiftl_bound 4 _ 28). apply xbits_bound.
          transitivity (2 ^ 28). apply (shiftl_bound 12 _ 16). apply xbits_bound. reflexivity.
      apply update_some. apply varid_type. 1, 2: reflexivity.
    apply TMove with (w := 32).
      right; apply varid_type; reflexivity.
      apply TWord. unfold cbits. apply lor_bound.
        transitivity (2 ^ 16). apply (shiftl_bound 4 _ 12). apply xbits_bound. reflexivity.
        transitivity (2 ^ 12). apply xbits_bound. reflexivity.
      apply update_some. apply varid_type. all: reflexivity.
Qed.

Lemma has_type_load_store_offset_addr:
  forall n1 n2 n3 n4, hastyp_exp arm7typctx
    (arm_load_store_offset_addr n1 n2 n3 n4) 32.
Proof.
  intros. unfold arm_load_store_offset_addr. destruct_match.
    all: apply TBinOp with (w := 32);
      first [ apply has_type_xbits | apply has_type_varid | apply has_type_op2 ];
      reflexivity.
Qed.

Lemma has_type_load_store_move_il:
  forall n1 n2 n3 e, hastyp_exp arm7typctx e 32 -> hastyp_stmt arm7typctx arm7typctx
    (arm_load_store_move_il n1 n2 n3 e) arm7typctx.
Proof.
  intros. unfold arm_load_store_move_il. destruct_match.
    all: repeat first
        [ right
        | eapply TMove
        | eapply TStore with (w := 32)
        | eapply TLoad with (w := 32)
        | apply varid_type
        | apply update_some
        | reflexivity
        | assumption ].
    3: apply TCast with (w := 8).
    3: apply TLoad with (w := 32).
    12: apply TCast with (w := 32).
    all: repeat first [ apply N.lt_le_incl | constructor | apply varid_type | reflexivity | assumption ].
Qed.

Lemma has_type_load_store_il:
  forall n1 n2 n3 n4 n5 n6 n7 n8, hastyp_stmt arm7typctx arm7typctx
    (arm_load_store_il n1 n2 n3 n4 n5 n6 n7 n8) arm7typctx.
Proof.
  intros. unfold arm_load_store_il. destruct_match.
    all: repeat first
        [ apply has_type_arm_cond
        | apply has_type_load_store_move_il
        | apply has_type_load_store_offset_addr
        | apply varid_type
        | right
        | econstructor
        | reflexivity ].
    all: apply update_some; try apply varid_type; reflexivity.
Qed.

Theorem has_type_load_store:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode_load_and_store n)) arm7typctx.
Proof.
  intros. unfold arm_decode_load_and_store. unfold arm_load_and_store_opcode. destruct_match.
  all: try apply has_type_load_store_il.
  all: unfold arm2il; constructor; reflexivity.
Qed.

Lemma has_type_pop:
  forall n i, hastyp_stmt arm7typctx arm7typctx (arm_popil n i) arm7typctx.
Proof.
  induction i.
    unfold arm_popil. destruct_match.
      constructor; reflexivity.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ]; reflexivity.
    unfold arm_popil; fold arm_popil. destruct_match.
      assumption.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
      3: rewrite <- store_upd_eq; try apply varid_type. 1-4: reflexivity.
      repeat rewrite <- store_upd_eq. assumption. 1, 3: apply varid_type. all: reflexivity.
Qed.

Lemma has_type_push:
  forall n i, hastyp_stmt arm7typctx arm7typctx (arm_pushil n i) arm7typctx.
Proof.
  induction i.
    unfold arm_pushil. destruct_match.
      constructor; reflexivity.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | eapply TStore with (w := 32)
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
    unfold arm_pushil; fold arm_pushil. destruct_match.
      assumption.
      repeat first
        [ apply TBinOp with (w := 32)
        | right
        | econstructor
        | eapply TStore with (w := 32)
        | apply varid_type
        | apply N.lt_le_incl
        | reflexivity
        | apply update_some ].
       repeat rewrite <- store_upd_eq. assumption. all: reflexivity.
Qed.

Lemma has_type_branch:
  forall a n, hastyp_stmt arm7typctx arm7typctx
    (arm2il a (arm_decode_branch n)) arm7typctx.
Proof.
  intros. unfold arm_decode_branch. destruct_match.
    all: unfold arm2il; try constructor; try reflexivity.
    all: apply has_type_arm_cond.
    all: repeat first
      [ apply TBinOp with (w := 32)
      | right
      | econstructor
      | reflexivity
      | apply update_some
      | apply varid_type ].
    all: solve [ apply ofZ_bound | apply has_type_pop | apply has_type_push ].
Qed.

(*
Lemma has_type_unconditional:
  forall a n, hastyp_stmt arm7typctx arm7typctx
    (arm2il a (arm_decode_unconditional n)) arm7typctx.
Proof.
  intros. unfold arm_decode_unconditional. destruct_match.
    all: constructor; reflexivity.
Qed.

 *)
Theorem welltyped_arm2il:
  forall a n, hastyp_stmt arm7typctx arm7typctx (arm2il a (arm_decode n)) arm7typctx.
Proof.
  intros. unfold arm_decode. destruct_match.
    all: try constructor; try reflexivity.
    all: solve  (* this seems to spin forever if a and n are not given *)
      [ apply (has_type_load_store a n)
      | apply (has_type_data a n)
      | apply (has_type_branch a n)
      | apply (has_type_unconditional a n) ].
Qed.

Theorem welltyped_arm_prog:
  welltyped_prog arm7typctx arm_prog.
Proof.
  intros s a. unfold arm_prog. 
    exists arm7typctx. unfold arm_stmt. destruct (a mod 4).
      apply welltyped_arm2il.
      constructor. reflexivity.
Qed.
*)
