
type arm_data_op =
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
| ARM_MOV
| ARM_BIC
| ARM_MVN

type arm_mul_op =
| ARM_MUL
| ARM_MLA
| ARM_UMAAL
| ARM_MLS
| ARM_UMULL
| ARM_UMLAL
| ARM_SMULL
| ARM_SMLAL

type arm_hmul_op =
| ARM_SMLABB
| ARM_SMLAWB
| ARM_SMULWB
| ARM_SMLALBB
| ARM_SMULBB

type arm_sat_op =
| ARM_QADD
| ARM_QSUB
| ARM_QDADD
| ARM_QDSUB

type arm_mem_op =
| ARM_LDR
| ARM_STR
| ARM_LDRB
| ARM_STRB

type arm_xmem_op =
| ARM_STRH
| ARM_LDRH
| ARM_LDRD
| ARM_LDRSB
| ARM_STRD
| ARM_LDRSH

type arm_memm_op =
| ARM_STMDA
| ARM_LDMDA
| ARM_STMDB
| ARM_LDMDB
| ARM_STMIA
| ARM_LDMIA
| ARM_STMIB
| ARM_LDMIB

type arm_sync_size =
| ARM_sync_word
| ARM_sync_doubleword
| ARM_sync_byte
| ARM_sync_halfword

type arm_pas_op =
| ARM_ADD16
| ARM_ASX
| ARM_SAX
| ARM_SUB16
| ARM_ADD8
| ARM_SUB8

type arm_pas_type =
| ARM_pas_normal
| ARM_pas_saturating
| ARM_pas_halving

type arm_rev_op =
| ARM_REV
| ARM_REV16
| ARM_RBIT
| ARM_REVSH

type arm_extend_op =
| ARM_XTAB16
| ARM_XTAB
| ARM_XTAH

type arm_vfp_op =
| ARM_VMLA
| ARM_VNMLA
| ARM_VMUL
| ARM_VADD
| ARM_VSUB
| ARM_VDIV
| ARM_VFNMA
| ARM_VFMA

type arm_vfp_other_op =
| ARM_VMOV
| ARM_VABS
| ARM_VNEG
| ARM_VSQRT

type arm_inst =
| ARM_UNDEFINED
| ARM_UNPREDICTABLE
| Coq_idk
| ARM_data_r of arm_data_op * int * int * int * int * int * int * int
| ARM_data_rsr of arm_data_op * int * int * int * int * int * int * int
| ARM_data_i of arm_data_op * int * int * int * int * int
| ARM_MOV_WT of bool * int * int * int * int
| ARM_mul of arm_mul_op * int * int * int * int * int * int
| ARM_hmul of arm_hmul_op * int * int * int * int * int * int * int
| ARM_sync_l of arm_sync_size * int * int * int
| ARM_sync_s of arm_sync_size * int * int * int * int
| ARM_BX of int * int
| ARM_BLX_r of int * int
| ARM_BXJ of int * int
| ARM_CLZ of int * int * int
| ARM_BKPT of int * int * int
| ARM_sat of arm_sat_op * int * int * int * int
| ARM_hint of int * int
| ARM_extra_ls_i of arm_xmem_op * int * int * int * int * int * int * 
   int * int
| ARM_extra_ls_r of arm_xmem_op * int * int * int * int * int * int * int
| ARM_ls_i of arm_mem_op * int * int * int * int * int * int * int
| ARM_ls_r of arm_mem_op * int * int * int * int * int * int * int * int * int
| ARM_pas of bool * arm_pas_type * arm_pas_op * int * int * int * int
| ARM_rev of arm_rev_op * int * int * int
| ARM_extend of bool * arm_extend_op * int * int * int * int * int
| ARM_bfx of bool * int * int * int * int * int
| ARM_lsm of arm_memm_op * int * int * int * int
| ARM_B of int * int
| ARM_BL of int * int
| ARM_BLX_i of int * int
| ARM_SVC of int * int
| ARM_coproc_m of bool * int * int * int * int * int * int * int
| ARM_vls of bool * bool * int * int * int * int * int * int
| ARM_vlsm of bool * bool * int * int * int * int * int * int * int * int
| ARM_VMOV_i of int * int * int * int * int * int
| ARM_VMOV_r2 of bool * int * int * int * int * int * int
| ARM_VMOV_r1 of int * int * int * int * int
| ARM_vfp of arm_vfp_op * int * int * int * int * int * int * int * int * int
| ARM_VCMP of int * int * int * int * int * int * int
| ARM_VMRS of int * int
| ARM_VCVT_fpi of int * int * int * int * int * int * int * int
| ARM_VCVT_fpf of int * int * int * int * int * int * int * int * int
| ARM_VCVT_ds of int * int * int * int * int * int
| ARM_vfp_other of arm_vfp_other_op * int * int * int * int * int * int
| ARM_PLD_i of int * int * int * int
| ARM_PLD_r of int * int * int * int * int * int

(** val zxbits : int -> int -> int -> int **)

let zxbits z i j =
  (fun x y -> ((x mod y) + y) mod y) ((lsr) z i) ((lsl) 1 ((max) 0 ((-) j i)))

(** val bitb : int -> int -> int **)

let bitb z b =
  zxbits z b ((+) b 1)

(** val arm_decode_data_r : arm_data_op -> int -> arm_inst **)

let arm_decode_data_r op z =
  let cond = zxbits z 28 32 in
  let s = bitb z 20 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let imm5 = zxbits z 7 12 in
  let type0 = zxbits z 5 7 in
  let rm = zxbits z 0 4 in ARM_data_r (op, cond, s, rn, rd, imm5, type0, rm)

(** val arm_decode_data_rsr : arm_data_op -> int -> arm_inst **)

let arm_decode_data_rsr op z =
  let cond = zxbits z 28 32 in
  let s = bitb z 20 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let rs = zxbits z 8 12 in
  let type0 = zxbits z 5 7 in
  let rm = zxbits z 0 4 in
  if if if if (=) rd 15 then true else (=) rn 15 then true else (=) rm 15
     then true
     else (=) rs 15
  then ARM_UNPREDICTABLE
  else ARM_data_rsr (op, cond, s, rn, rd, rs, type0, rm)

(** val arm_decode_data_i : arm_data_op -> int -> arm_inst **)

let arm_decode_data_i op z =
  let cond = zxbits z 28 32 in
  let s = bitb z 20 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let imm12 = zxbits z 0 12 in ARM_data_i (op, cond, s, rn, rd, imm12)

(** val arm_decode_data_rd0 :
    (arm_data_op -> int -> arm_inst) -> arm_data_op -> int -> arm_inst **)

let arm_decode_data_rd0 kind op z =
  let rd = zxbits z 12 16 in
  if (not) ((=) rd 0) then ARM_UNPREDICTABLE else kind op z

(** val arm_decode_data_rn0 :
    (arm_data_op -> int -> arm_inst) -> arm_data_op -> int -> arm_inst **)

let arm_decode_data_rn0 kind op z =
  let rn = zxbits z 16 20 in
  if (not) ((=) rn 0) then ARM_UNPREDICTABLE else kind op z

(** val arm_decode_data_processing :
    (arm_data_op -> int -> arm_inst) -> int -> arm_inst **)

let arm_decode_data_processing kind z =
  let op = zxbits z 21 25 in
  if (=) op 0
  then kind ARM_AND z
  else if (=) op 1
       then kind ARM_EOR z
       else if (=) op 2
            then kind ARM_SUB z
            else if (=) op 3
                 then kind ARM_RSB z
                 else if (=) op 4
                      then kind ARM_ADD z
                      else if (=) op 5
                           then kind ARM_ADC z
                           else if (=) op 6
                                then kind ARM_SBC z
                                else if (=) op 7
                                     then kind ARM_RSC z
                                     else if (=) op 8
                                          then arm_decode_data_rd0 kind
                                                 ARM_TST z
                                          else if (=) op 9
                                               then arm_decode_data_rd0 kind
                                                      ARM_TEQ z
                                               else if (=) op 10
                                                    then arm_decode_data_rd0
                                                           kind ARM_CMP z
                                                    else if (=) op 11
                                                         then arm_decode_data_rd0
                                                                kind ARM_CMN z
                                                         else if (=) op 12
                                                              then kind
                                                                    ARM_ORR z
                                                              else if 
                                                                    (=) op 13
                                                                   then 
                                                                    arm_decode_data_rn0
                                                                    kind
                                                                    ARM_MOV z
                                                                   else 
                                                                    if 
                                                                    (=) op 14
                                                                    then 
                                                                    kind
                                                                    ARM_BIC z
                                                                    else 
                                                                    arm_decode_data_rn0
                                                                    kind
                                                                    ARM_MVN z

(** val arm_decode_sat : arm_sat_op -> int -> arm_inst **)

let arm_decode_sat op z =
  let cond = zxbits z 28 32 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let rm = zxbits z 0 4 in
  if if if (=) rd 15 then true else (=) rn 15 then true else (=) rm 15
  then ARM_UNPREDICTABLE
  else if (not) ((=) (zxbits z 8 12) 0)
       then ARM_UNPREDICTABLE
       else ARM_sat (op, cond, rn, rd, rm)

(** val arm_decode_saturating_add_sub : int -> arm_inst **)

let arm_decode_saturating_add_sub z =
  let op = zxbits z 21 23 in
  if (=) op 0
  then arm_decode_sat ARM_QADD z
  else if (=) op 1
       then arm_decode_sat ARM_QSUB z
       else if (=) op 2
            then arm_decode_sat ARM_QDADD z
            else arm_decode_sat ARM_QDSUB z

(** val arm_decode_mov_wt : bool -> int -> arm_inst **)

let arm_decode_mov_wt is_w z =
  let cond = zxbits z 28 32 in
  let imm4 = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let imm12 = zxbits z 0 12 in
  if (=) rd 15
  then ARM_UNPREDICTABLE
  else ARM_MOV_WT (is_w, cond, imm4, rd, imm12)

(** val arm_decode_bx : int -> arm_inst **)

let arm_decode_bx z =
  let cond = zxbits z 28 32 in
  let rm = zxbits z 0 4 in
  if (not) ((=) (zxbits z 8 20) 4095)
  then ARM_UNPREDICTABLE
  else ARM_BX (cond, rm)

(** val arm_decode_clz : int -> arm_inst **)

let arm_decode_clz z =
  let cond = zxbits z 28 32 in
  let rd = zxbits z 12 16 in
  let rm = zxbits z 0 4 in
  if if if if (not) ((=) (zxbits z 8 12) 15)
           then true
           else (not) ((=) (zxbits z 16 20) 15)
        then true
        else (=) rd 15
     then true
     else (=) rm 15
  then ARM_UNPREDICTABLE
  else ARM_CLZ (cond, rd, rm)

(** val arm_decode_bxj : int -> arm_inst **)

let arm_decode_bxj z =
  let cond = zxbits z 28 32 in
  let rm = zxbits z 0 4 in
  if if (not) ((=) (zxbits z 8 20) 4095) then true else (=) rm 15
  then ARM_UNPREDICTABLE
  else ARM_BXJ (cond, rm)

(** val arm_decode_blx_r : int -> arm_inst **)

let arm_decode_blx_r z =
  let cond = zxbits z 28 32 in
  let rm = zxbits z 0 4 in
  if if (not) ((=) (zxbits z 8 20) 4095) then true else (=) rm 15
  then ARM_UNPREDICTABLE
  else ARM_BLX_r (cond, rm)

(** val arm_decode_bkpt : int -> arm_inst **)

let arm_decode_bkpt z =
  let cond = zxbits z 28 32 in
  let imm12 = zxbits z 8 20 in
  let imm4 = zxbits z 0 4 in
  if (not) ((=) cond 14)
  then ARM_UNPREDICTABLE
  else ARM_BKPT (cond, imm12, imm4)

(** val arm_decode_b : int -> arm_inst **)

let arm_decode_b z =
  let cond = zxbits z 28 32 in
  let imm24 = zxbits z 0 24 in ARM_B (cond, imm24)

(** val arm_decode_bl : int -> arm_inst **)

let arm_decode_bl z =
  let cond = zxbits z 28 32 in
  let imm24 = zxbits z 0 24 in ARM_BL (cond, imm24)

(** val arm_decode_blx_i : int -> arm_inst **)

let arm_decode_blx_i z =
  let h = bitb z 24 in let imm24 = zxbits z 0 24 in ARM_BLX_i (h, imm24)

(** val arm_decode_misc : int -> arm_inst **)

let arm_decode_misc z =
  let op = zxbits z 21 23 in
  let op2 = zxbits z 4 7 in
  let b = bitb z 9 in
  if (=) op2 0
  then if (=) b 1
       then ARM_UNPREDICTABLE
       else if if (=) op 0 then true else (=) op 2
            then Coq_idk
            else if (=) op 1
                 then Coq_idk
                 else if (=) op 3 then Coq_idk else ARM_UNDEFINED
  else if (=) op2 1
       then if (=) op 1
            then arm_decode_bx z
            else if (=) op 3 then arm_decode_clz z else ARM_UNDEFINED
       else if if (=) op2 2 then (=) op 1 else false
            then arm_decode_bxj z
            else if if (=) op2 3 then (=) op 1 else false
                 then arm_decode_blx_r z
                 else if (=) op2 5
                      then arm_decode_saturating_add_sub z
                      else if if (=) op2 6 then (=) op 3 else false
                           then ARM_UNPREDICTABLE
                           else if (=) op2 7
                                then if (=) op 1
                                     then arm_decode_bkpt z
                                     else ARM_UNDEFINED
                                else ARM_UNDEFINED

(** val arm_decode_hmul : arm_hmul_op -> int -> arm_inst **)

let arm_decode_hmul op z =
  let cond = zxbits z 28 32 in
  let rd = zxbits z 16 20 in
  let ra = zxbits z 12 16 in
  let rm = zxbits z 8 12 in
  let m = bitb z 6 in
  let n = bitb z 5 in
  let rn = zxbits z 0 4 in
  if if if if (=) rd 15 then true else (=) rn 15 then true else (=) rm 15
     then true
     else (=) ra 15
  then ARM_UNPREDICTABLE
  else if match op with
          | ARM_SMLABB -> false
          | ARM_SMLAWB -> false
          | ARM_SMLALBB -> (=) rd ra
          | _ -> (not) ((=) ra 0)
       then ARM_UNPREDICTABLE
       else ARM_hmul (op, cond, rd, ra, rm, m, n, rn)

(** val arm_decode_halfword_multiply : int -> arm_inst **)

let arm_decode_halfword_multiply z =
  let op1 = zxbits z 21 23 in
  let op = bitb z 5 in
  if (=) op1 0
  then arm_decode_hmul ARM_SMLABB z
  else if (=) op1 1
       then if (=) op 0
            then arm_decode_hmul ARM_SMLAWB z
            else arm_decode_hmul ARM_SMULWB z
       else if (=) op1 2
            then arm_decode_hmul ARM_SMLALBB z
            else arm_decode_hmul ARM_SMULBB z

(** val arm_decode_mul : arm_mul_op -> int -> arm_inst **)

let arm_decode_mul op z =
  let cond = zxbits z 28 32 in
  let s = bitb z 20 in
  let rd_RdHi = zxbits z 16 20 in
  let ra_RdLo = zxbits z 12 16 in
  let rm = zxbits z 8 12 in
  let rn = zxbits z 0 4 in
  if if if if (=) rd_RdHi 15 then true else (=) rn 15 then true else (=) rm 15
     then true
     else (=) ra_RdLo 15
  then ARM_UNPREDICTABLE
  else if match op with
          | ARM_MUL -> (not) ((=) ra_RdLo 0)
          | ARM_MLA -> false
          | ARM_MLS -> false
          | _ -> (=) rd_RdHi ra_RdLo
       then ARM_UNPREDICTABLE
       else ARM_mul (op, cond, s, rd_RdHi, ra_RdLo, rm, rn)

(** val arm_decode_multiply : int -> arm_inst **)

let arm_decode_multiply z =
  let op = zxbits z 20 24 in
  if if (=) op 0 then true else (=) op 1
  then arm_decode_mul ARM_MUL z
  else if if (=) op 2 then true else (=) op 3
       then arm_decode_mul ARM_MLA z
       else if (=) op 4
            then arm_decode_mul ARM_UMAAL z
            else if (=) op 5
                 then ARM_UNDEFINED
                 else if (=) op 6
                      then arm_decode_mul ARM_MLS z
                      else if (=) op 7
                           then ARM_UNDEFINED
                           else if if (=) op 8 then true else (=) op 9
                                then arm_decode_mul ARM_UMULL z
                                else if if (=) op 10 then true else (=) op 11
                                     then arm_decode_mul ARM_UMLAL z
                                     else if if (=) op 12
                                             then true
                                             else (=) op 13
                                          then arm_decode_mul ARM_SMULL z
                                          else arm_decode_mul ARM_SMLAL z

(** val arm_decode_sync_s : arm_sync_size -> int -> arm_inst **)

let arm_decode_sync_s size z =
  let cond = zxbits z 28 32 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let rt = zxbits z 0 4 in
  if if if (=) rd 15 then true else (=) rt 15 then true else (=) rn 15
  then ARM_UNPREDICTABLE
  else if if (=) rd rn then true else (=) rd rt
       then ARM_UNPREDICTABLE
       else if (not) ((=) (zxbits z 8 12) 15)
            then ARM_UNPREDICTABLE
            else if match size with
                    | ARM_sync_doubleword ->
                      if if (=) (bitb rt 0) 1 then true else (=) rt 14
                      then true
                      else (=) rd ((+) rt 1)
                    | _ -> false
                 then ARM_UNPREDICTABLE
                 else ARM_sync_s (size, cond, rn, rd, rt)

(** val arm_decode_sync_l : arm_sync_size -> int -> arm_inst **)

let arm_decode_sync_l size z =
  let cond = zxbits z 28 32 in
  let rn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  if if (=) rt 15 then true else (=) rn 15
  then ARM_UNPREDICTABLE
  else if if (not) ((=) (zxbits z 8 12) 15)
          then true
          else (not) ((=) (zxbits z 0 4) 15)
       then ARM_UNPREDICTABLE
       else if match size with
               | ARM_sync_doubleword ->
                 if (=) (bitb rt 0) 1 then true else (=) rt 14
               | _ -> false
            then ARM_UNPREDICTABLE
            else ARM_sync_l (size, cond, rn, rt)

(** val arm_decode_sync_primitives : int -> arm_inst **)

let arm_decode_sync_primitives z =
  let op = zxbits z 20 24 in
  if (=) (bitb op 3) 0
  then Coq_idk
  else let size =
         if (=) (bitb op 2) 0
         then if (=) (bitb op 1) 0 then ARM_sync_word else ARM_sync_doubleword
         else if (=) (bitb op 1) 0 then ARM_sync_byte else ARM_sync_halfword
       in
       if (=) (bitb op 0) 0
       then arm_decode_sync_s size z
       else arm_decode_sync_l size z

(** val arm_decode_extra_ls_i : arm_xmem_op -> int -> arm_inst **)

let arm_decode_extra_ls_i op z =
  let cond = zxbits z 28 32 in
  let p = bitb z 24 in
  let u = bitb z 23 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let imm4H = zxbits z 8 12 in
  let imm4L = zxbits z 0 4 in
  let wback = if (=) p 0 then true else (=) w 1 in
  if if (=) rt 15
     then true
     else if wback then if (=) rn 15 then true else (=) rn rt else false
  then ARM_UNPREDICTABLE
  else if match op with
          | ARM_LDRD ->
            if if if if wback then (=) rn ((+) rt 1) else false
                  then true
                  else (=) (bitb rt 0) 1
               then true
               else if (=) p 0 then (=) w 1 else false
            then true
            else (=) rt 14
          | ARM_STRD ->
            if if if if wback then (=) rn ((+) rt 1) else false
                  then true
                  else (=) (bitb rt 0) 1
               then true
               else if (=) p 0 then (=) w 1 else false
            then true
            else (=) rt 14
          | _ -> false
       then ARM_UNPREDICTABLE
       else ARM_extra_ls_i (op, cond, p, u, w, rn, rt, imm4H, imm4L)

(** val arm_decode_extra_ls_r : arm_xmem_op -> int -> arm_inst **)

let arm_decode_extra_ls_r op z =
  let cond = zxbits z 28 32 in
  let p = bitb z 24 in
  let u = bitb z 23 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let rm = zxbits z 0 4 in
  let wback = if (=) p 0 then true else (=) w 1 in
  if if if (=) rt 15 then true else (=) rm 15
     then true
     else if wback then if (=) rn 15 then true else (=) rn rt else false
  then ARM_UNPREDICTABLE
  else if (not) ((=) (zxbits z 8 12) 0)
       then ARM_UNPREDICTABLE
       else if match op with
               | ARM_LDRD ->
                 if if if if wback then (=) rn ((+) rt 1) else false
                       then true
                       else (=) (bitb rt 0) 1
                    then true
                    else if (=) p 0 then (=) w 1 else false
                 then true
                 else (=) rt 14
               | ARM_STRD ->
                 if if if if wback then (=) rn ((+) rt 1) else false
                       then true
                       else (=) (bitb rt 0) 1
                    then true
                    else if (=) p 0 then (=) w 1 else false
                 then true
                 else (=) rt 14
               | _ -> false
            then ARM_UNPREDICTABLE
            else if match op with
                    | ARM_LDRD ->
                      if (=) rm rt then true else (=) rm ((+) rt 1)
                    | _ -> false
                 then ARM_UNPREDICTABLE
                 else ARM_extra_ls_r (op, cond, p, u, w, rn, rt, rm)

(** val arm_decode_extra_load_store : int -> arm_inst **)

let arm_decode_extra_load_store z =
  let op2 = zxbits z 5 7 in
  let op1_0 = bitb z 20 in
  let kind =
    if (=) (bitb z 22) 0 then arm_decode_extra_ls_r else arm_decode_extra_ls_i
  in
  if (=) op2 1
  then if (=) op1_0 0 then kind ARM_STRH z else kind ARM_LDRH z
  else if (=) op2 2
       then if (=) op1_0 0 then kind ARM_LDRD z else kind ARM_LDRSB z
       else if (=) op2 3
            then if (=) op1_0 0 then kind ARM_STRD z else kind ARM_LDRSH z
            else ARM_UNDEFINED

(** val arm_decode_hint : int -> arm_inst **)

let arm_decode_hint z =
  let cond = zxbits z 28 32 in
  let op2 = zxbits z 0 8 in
  if if (=) op2 20 then (not) ((=) cond 14) else false
  then ARM_UNPREDICTABLE
  else if if (not) ((=) (zxbits z 12 16) 15)
          then true
          else (not) ((=) (zxbits z 8 12) 0)
       then ARM_UNPREDICTABLE
       else ARM_hint (cond, op2)

(** val arm_decode_msr_hints : int -> arm_inst **)

let arm_decode_msr_hints z =
  let op = bitb z 22 in
  let op1 = zxbits z 16 20 in
  if (=) op 0
  then if (=) op1 0 then arm_decode_hint z else Coq_idk
  else Coq_idk

(** val arm_decode_data_misc : int -> arm_inst **)

let arm_decode_data_misc z =
  let op = bitb z 25 in
  let op1 = zxbits z 20 25 in
  let op2 = zxbits z 4 8 in
  if (=) op 0
  then if (=) op2 9
       then if (=) (bitb z 24) 0
            then arm_decode_multiply z
            else arm_decode_sync_primitives z
       else if if (=) (bitb z 4) 0 then true else (=) (bitb z 7) 0
            then if if if if (=) op1 16 then true else (=) op1 18
                       then true
                       else (=) op1 20
                    then true
                    else (=) op1 22
                 then if (=) (bitb z 7) 0
                      then arm_decode_misc z
                      else arm_decode_halfword_multiply z
                 else if (=) (bitb op2 0) 0
                      then arm_decode_data_processing arm_decode_data_r z
                      else if (=) (bitb op2 3) 0
                           then arm_decode_data_processing
                                  arm_decode_data_rsr z
                           else ARM_UNDEFINED
            else arm_decode_extra_load_store z
  else if (=) op1 16
       then arm_decode_mov_wt true z
       else if (=) op1 20
            then arm_decode_mov_wt false z
            else if if (=) op1 18 then true else (=) op1 22
                 then arm_decode_msr_hints z
                 else arm_decode_data_processing arm_decode_data_i z

(** val arm_decode_ls_r : arm_mem_op -> int -> arm_inst **)

let arm_decode_ls_r op z =
  let cond = zxbits z 28 32 in
  let p = bitb z 24 in
  let u = bitb z 23 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let imm5 = zxbits z 7 12 in
  let type0 = zxbits z 5 7 in
  let rm = zxbits z 0 4 in
  let wback = if (=) p 0 then true else (=) w 1 in
  if if (=) rm 15
     then true
     else if wback then if (=) rn 15 then true else (=) rn rt else false
  then ARM_UNPREDICTABLE
  else if if match op with
             | ARM_LDR -> if (=) p 0 then (=) w 1 else false
             | ARM_STR -> false
             | _ -> true
          then (=) rt 15
          else false
       then ARM_UNPREDICTABLE
       else ARM_ls_r (op, cond, p, u, w, rn, rt, imm5, type0, rm)

(** val arm_decode_ls_i : arm_mem_op -> int -> arm_inst **)

let arm_decode_ls_i op z =
  let cond = zxbits z 28 32 in
  let p = bitb z 24 in
  let u = bitb z 23 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let imm12 = zxbits z 0 12 in
  let wback = if (=) p 0 then true else (=) w 1 in
  if if wback then if (=) rn 15 then true else (=) rn rt else false
  then ARM_UNPREDICTABLE
  else if if match op with
             | ARM_LDR -> if (=) p 0 then (=) w 1 else false
             | ARM_STR -> false
             | _ -> true
          then (=) rt 15
          else false
       then ARM_UNPREDICTABLE
       else ARM_ls_i (op, cond, p, u, w, rn, rt, imm12)

(** val arm_decode_load_store : int -> arm_inst **)

let arm_decode_load_store z =
  let a = bitb z 25 in
  let b = bitb z 4 in
  let op1 = zxbits z 20 25 in
  let is_load = (=) (bitb op1 0) 1 in
  let is_byte = (=) (bitb op1 2) 1 in
  if if (=) a 1 then (=) b 1 else false
  then ARM_UNDEFINED
  else let kind = if (=) a 0 then arm_decode_ls_i else arm_decode_ls_r in
       let op =
         if is_load
         then if is_byte then ARM_LDRB else ARM_LDR
         else if is_byte then ARM_STRB else ARM_STR
       in
       kind op z

(** val arm_decode_pas :
    bool -> arm_pas_type -> arm_pas_op -> int -> arm_inst **)

let arm_decode_pas is_signed type0 op z =
  let cond = zxbits z 28 32 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let rm = zxbits z 0 4 in
  if (not) ((=) (zxbits z 8 12) 15)
  then ARM_UNPREDICTABLE
  else if if if (=) rd 15 then true else (=) rn 15 then true else (=) rm 15
       then ARM_UNPREDICTABLE
       else ARM_pas (is_signed, type0, op, cond, rn, rd, rm)

(** val arm_decode_parallel_add_sub : int -> arm_inst **)

let arm_decode_parallel_add_sub z =
  let is_signed = (=) (bitb z 22) 0 in
  let op1 = zxbits z 20 22 in
  let op2 = zxbits z 5 8 in
  let type0 =
    if (=) op1 1
    then Some ARM_pas_normal
    else if (=) op1 2
         then Some ARM_pas_saturating
         else if (=) op1 3 then Some ARM_pas_halving else None
  in
  let op =
    if (=) op2 0
    then Some ARM_ADD16
    else if (=) op2 1
         then Some ARM_ASX
         else if (=) op2 2
              then Some ARM_SAX
              else if (=) op2 3
                   then Some ARM_SUB16
                   else if (=) op2 4
                        then Some ARM_ADD8
                        else if (=) op2 7 then Some ARM_SUB8 else None
  in
  (match type0 with
   | Some type1 ->
     (match op with
      | Some op0 -> arm_decode_pas is_signed type1 op0 z
      | None -> ARM_UNDEFINED)
   | None -> ARM_UNDEFINED)

(** val arm_decode_rev : arm_rev_op -> int -> arm_inst **)

let arm_decode_rev op z =
  let cond = zxbits z 28 32 in
  let rd = zxbits z 12 16 in
  let rm = zxbits z 0 4 in
  if if (=) rd 15 then true else (=) rm 15
  then ARM_UNPREDICTABLE
  else if if (not) ((=) (zxbits z 16 20) 15)
          then true
          else (not) ((=) (zxbits z 8 12) 15)
       then ARM_UNPREDICTABLE
       else ARM_rev (op, cond, rd, rm)

(** val arm_decode_extend : bool -> arm_extend_op -> int -> arm_inst **)

let arm_decode_extend is_signed op z =
  let cond = zxbits z 28 32 in
  let rn = zxbits z 16 20 in
  let rd = zxbits z 12 16 in
  let rotate = zxbits z 10 12 in
  let rm = zxbits z 0 4 in
  if if (=) rd 15 then true else (=) rm 15
  then ARM_UNPREDICTABLE
  else if (not) ((=) (zxbits z 8 10) 0)
       then ARM_UNPREDICTABLE
       else ARM_extend (is_signed, op, cond, rn, rd, rotate, rm)

(** val arm_decode_packing : int -> arm_inst **)

let arm_decode_packing z =
  let op1 = zxbits z 20 23 in
  let op1'2 = zxbits op1 1 3 in
  let op1_1 = bitb op1 0 in
  let op2 = zxbits z 5 8 in
  let op2_1 = bitb op2 0 in
  if (=) op1'2 0
  then if (=) op2_1 0
       then Coq_idk
       else if (=) op2 3
            then arm_decode_extend true ARM_XTAB16 z
            else if (=) op2 5 then Coq_idk else ARM_UNDEFINED
  else if (=) op1'2 1
       then if (=) op2_1 0
            then Coq_idk
            else if (=) op1_1 0
                 then if (=) op2 1
                      then Coq_idk
                      else if (=) op2 3
                           then arm_decode_extend true ARM_XTAB z
                           else ARM_UNDEFINED
                 else if (=) op2 1
                      then arm_decode_rev ARM_REV z
                      else if (=) op2 3
                           then arm_decode_extend true ARM_XTAH z
                           else if (=) op2 5
                                then arm_decode_rev ARM_REV16 z
                                else ARM_UNDEFINED
       else if (=) op1'2 2
            then if if (=) op1_1 0 then (=) op2 3 else false
                 then arm_decode_extend false ARM_XTAB16 z
                 else ARM_UNDEFINED
            else if (=) op2_1 0
                 then Coq_idk
                 else if (=) op1_1 0
                      then if (=) op2 1
                           then Coq_idk
                           else if (=) op2 3
                                then arm_decode_extend false ARM_XTAB z
                                else ARM_UNDEFINED
                      else if (=) op2 1
                           then arm_decode_rev ARM_RBIT z
                           else if (=) op2 3
                                then arm_decode_extend false ARM_XTAH z
                                else if (=) op2 5
                                     then arm_decode_rev ARM_REVSH z
                                     else ARM_UNDEFINED

(** val arm_decode_signed_multiply : int -> arm_inst **)

let arm_decode_signed_multiply _ =
  Coq_idk

(** val arm_decode_bfx : bool -> int -> arm_inst **)

let arm_decode_bfx is_signed z =
  let cond = zxbits z 28 32 in
  let widthm1 = zxbits z 16 21 in
  let rd = zxbits z 12 16 in
  let lsb = zxbits z 7 12 in
  let rn = zxbits z 0 4 in
  if if if (=) rd 15 then true else (=) rn 15
     then true
     else (>) ((+) lsb widthm1) 31
  then ARM_UNPREDICTABLE
  else ARM_bfx (is_signed, cond, widthm1, rd, lsb, rn)

(** val arm_decode_media : int -> arm_inst **)

let arm_decode_media z =
  let op1 = zxbits z 20 25 in
  let op1'2 = zxbits op1 3 5 in
  let op1_3 = zxbits op1 0 3 in
  let op2 = zxbits z 5 8 in
  if (=) op1'2 0
  then arm_decode_parallel_add_sub z
  else if (=) op1'2 1
       then arm_decode_packing z
       else if (=) op1'2 2
            then arm_decode_signed_multiply z
            else if (=) op1_3 0
                 then if (=) op2 0 then Coq_idk else ARM_UNDEFINED
                 else if if (=) op1_3 2 then true else (=) op1_3 3
                      then if if (=) op2 2 then true else (=) op2 6
                           then arm_decode_bfx true z
                           else ARM_UNDEFINED
                      else if if (=) op1_3 4 then true else (=) op1_3 5
                           then if if (=) op2 0 then true else (=) op2 4
                                then Coq_idk
                                else ARM_UNDEFINED
                           else if if (=) op1_3 6 then true else (=) op1_3 7
                                then if if (=) op2 2 then true else (=) op2 6
                                     then arm_decode_bfx false z
                                     else ARM_UNDEFINED
                                else ARM_UNDEFINED

(** val arm_decode_lsm : arm_memm_op -> int -> arm_inst **)

let arm_decode_lsm op z =
  let cond = zxbits z 28 32 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let register_list = zxbits z 0 16 in
  if if (=) rn 15 then true else (=) register_list 0
  then ARM_UNPREDICTABLE
  else if if if (=) w 1 then (=) (bitb z 20) 1 else false
          then (=) (bitb z rn) 1
          else false
       then ARM_UNPREDICTABLE
       else ARM_lsm (op, cond, w, rn, register_list)

(** val arm_decode_branch_block_transfer : int -> arm_inst **)

let arm_decode_branch_block_transfer z =
  let op = zxbits z 20 26 in
  if (=) (bitb op 5) 0
  then if (=) (bitb op 2) 1
       then ARM_UNPREDICTABLE
       else let is_after = (=) (bitb op 4) 0 in
            let is_decrement = (=) (bitb op 3) 0 in
            let is_store = (=) (bitb op 0) 0 in
            let op0 =
              if is_after
              then if is_decrement
                   then if is_store then ARM_STMDA else ARM_LDMDA
                   else if is_store then ARM_STMIA else ARM_LDMIA
              else if is_decrement
                   then if is_store then ARM_STMDB else ARM_LDMDB
                   else if is_store then ARM_STMIB else ARM_LDMIB
            in
            arm_decode_lsm op0 z
  else if (=) (bitb op 4) 0 then arm_decode_b z else arm_decode_bl z

(** val arm_decode_svc : int -> arm_inst **)

let arm_decode_svc z =
  let cond = zxbits z 28 32 in
  let imm24 = zxbits z 0 24 in ARM_SVC (cond, imm24)

(** val arm_decode_coproc_m : bool -> int -> arm_inst **)

let arm_decode_coproc_m is_cr z =
  let cond = zxbits z 28 32 in
  let opc1 = zxbits z 21 23 in
  let cRn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let coproc = zxbits z 8 12 in
  let opc2 = zxbits z 5 8 in
  let cRm = zxbits z 0 4 in
  if if (=) coproc 10 then true else (=) coproc 11
  then ARM_UNDEFINED
  else if if is_cr then (=) rt 15 else false
       then ARM_UNPREDICTABLE
       else ARM_coproc_m (is_cr, cond, opc1, cRn, rt, coproc, opc2, cRm)

(** val arm_decode_vls : bool -> int -> arm_inst **)

let arm_decode_vls is_load z =
  let is_single = (=) (bitb z 8) 0 in
  let cond = zxbits z 28 32 in
  let u = bitb z 23 in
  let d = bitb z 22 in
  let rn = zxbits z 16 20 in
  let vd = zxbits z 12 16 in
  let imm8 = zxbits z 0 8 in
  ARM_vls (is_load, is_single, cond, u, d, rn, vd, imm8)

(** val arm_decode_vlsm : bool -> int -> arm_inst **)

let arm_decode_vlsm is_load z =
  let is_single = (=) (bitb z 8) 0 in
  let cond = zxbits z 28 32 in
  let p = bitb z 24 in
  let u = bitb z 23 in
  let d = bitb z 22 in
  let w = bitb z 21 in
  let rn = zxbits z 16 20 in
  let vd = zxbits z 12 16 in
  let imm8 = zxbits z 0 8 in
  let ok = ARM_vlsm (is_load, is_single, cond, p, u, d, w, rn, vd, imm8) in
  if if (=) rn 15 then (=) w 1 else false
  then ARM_UNPREDICTABLE
  else if is_single
       then if if (=) imm8 0
               then true
               else (>) ((+) ((+) imm8 ((lsl) vd 1)) d) 32
            then ARM_UNPREDICTABLE
            else ok
       else if (=) (bitb imm8 0) 1
            then Coq_idk
            else if if if (=) imm8 0 then true else (>) imm8 32
                    then true
                    else (>) ((+) ((+) ((lsl) d 4) vd) ((lsr) imm8 1)) 32
                 then ARM_UNPREDICTABLE
                 else ok

(** val arm_decode_vreg_ls : int -> arm_inst **)

let arm_decode_vreg_ls z =
  let opcode = zxbits z 20 25 in
  let o'2 = zxbits opcode 3 5 in
  let o_2 = zxbits opcode 0 2 in
  if (=) o'2 0
  then ARM_UNDEFINED
  else if (=) o'2 1
       then if if (=) o_2 0 then true else (=) o_2 2
            then arm_decode_vlsm false z
            else arm_decode_vlsm true z
       else if (=) o'2 2
            then if (=) o_2 0
                 then arm_decode_vls false z
                 else if (=) o_2 1
                      then arm_decode_vls true z
                      else if (=) o_2 2
                           then arm_decode_vlsm false z
                           else arm_decode_vlsm true z
            else if (=) o_2 0
                 then arm_decode_vls false z
                 else if (=) o_2 1
                      then arm_decode_vls true z
                      else ARM_UNDEFINED

(** val arm_decode_vmov_i : int -> arm_inst **)

let arm_decode_vmov_i z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let imm4H = zxbits z 16 20 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let imm4L = zxbits z 0 4 in
  if if (not) ((=) (bitb z 5) 0) then true else (not) ((=) (bitb z 7) 0)
  then ARM_UNPREDICTABLE
  else ARM_VMOV_i (cond, d, imm4H, vd, sz, imm4L)

(** val arm_decode_vmov_r2 : bool -> int -> arm_inst **)

let arm_decode_vmov_r2 is_single z =
  let cond = zxbits z 28 32 in
  let op = bitb z 20 in
  let rt2 = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in
  if if if (=) rt 15 then true else (=) rt2 15
     then true
     else if is_single then (=) ((+) ((lsl) vm 1) m) 31 else false
  then ARM_UNPREDICTABLE
  else if if (=) op 1 then (=) rt rt2 else false
       then ARM_UNPREDICTABLE
       else ARM_VMOV_r2 (is_single, cond, op, rt2, rt, m, vm)

(** val arm_decode_vmov_r1 : int -> arm_inst **)

let arm_decode_vmov_r1 z =
  let cond = zxbits z 28 32 in
  let op = bitb z 20 in
  let vn = zxbits z 16 20 in
  let rt = zxbits z 12 16 in
  let n = bitb z 7 in
  if (=) rt 15
  then ARM_UNPREDICTABLE
  else if if (not) ((=) (zxbits z 5 7) 0)
          then true
          else (not) ((=) (zxbits z 0 4) 0)
       then ARM_UNPREDICTABLE
       else ARM_VMOV_r1 (cond, op, vn, rt, n)

(** val arm_decode_vcmp : int -> arm_inst **)

let arm_decode_vcmp z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let e = bitb z 7 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in
  if if (=) (bitb z 16) 1
     then if (not) ((=) m 0) then true else (not) ((=) vm 0)
     else false
  then ARM_UNPREDICTABLE
  else ARM_VCMP (cond, d, vd, sz, e, m, vm)

(** val arm_decode_vfp : arm_vfp_op -> int -> arm_inst **)

let arm_decode_vfp op z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let vn = zxbits z 16 20 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let n = bitb z 7 in
  let op0 = bitb z 6 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in ARM_vfp (op, cond, d, vn, vd, sz, n, op0, m, vm)

(** val arm_decode_vcvt_ds : int -> arm_inst **)

let arm_decode_vcvt_ds z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in ARM_VCVT_ds (cond, d, vd, sz, m, vm)

(** val arm_decode_vcvt_fpi : int -> arm_inst **)

let arm_decode_vcvt_fpi z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let opc2 = zxbits z 16 19 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let op = bitb z 7 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in ARM_VCVT_fpi (cond, d, opc2, vd, sz, op, m, vm)

(** val arm_decode_vcvt_fpf : int -> arm_inst **)

let arm_decode_vcvt_fpf z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let op = bitb z 18 in
  let u = bitb z 16 in
  let vd = zxbits z 12 16 in
  let sf = bitb z 8 in
  let sx = bitb z 7 in
  let i = bitb z 5 in
  let imm4 = zxbits z 0 4 in
  let size = if (=) sx 0 then 16 else 32 in
  if (<) size ((+) ((lsl) imm4 1) i)
  then ARM_UNPREDICTABLE
  else ARM_VCVT_fpf (cond, d, op, u, vd, sf, sx, i, imm4)

(** val arm_decode_vfp_other : arm_vfp_other_op -> int -> arm_inst **)

let arm_decode_vfp_other op z =
  let cond = zxbits z 28 32 in
  let d = bitb z 22 in
  let vd = zxbits z 12 16 in
  let sz = bitb z 8 in
  let m = bitb z 5 in
  let vm = zxbits z 0 4 in ARM_vfp_other (op, cond, d, vd, sz, m, vm)

(** val arm_decode_floating_data_processing : int -> arm_inst **)

let arm_decode_floating_data_processing z =
  let opc1 = zxbits z 20 24 in
  let opc2 = zxbits z 16 20 in
  let opc3 = zxbits z 6 8 in
  let opc1'1 = bitb opc1 3 in
  let opc1_2 = zxbits opc1 0 2 in
  if (=) opc1'1 0
  then if (=) opc1_2 0
       then arm_decode_vfp ARM_VMLA z
       else if (=) opc1_2 1
            then arm_decode_vfp ARM_VNMLA z
            else if (=) opc1_2 2
                 then if if (=) opc3 1 then true else (=) opc3 3
                      then arm_decode_vfp ARM_VNMLA z
                      else arm_decode_vfp ARM_VMUL z
                 else if if (=) opc3 0 then true else (=) opc3 2
                      then arm_decode_vfp ARM_VADD z
                      else arm_decode_vfp ARM_VSUB z
  else if (=) opc1_2 0
       then arm_decode_vfp ARM_VDIV z
       else if (=) opc1_2 1
            then arm_decode_vfp ARM_VFNMA z
            else if (=) opc1_2 2
                 then arm_decode_vfp ARM_VFMA z
                 else if if (=) opc3 0 then true else (=) opc3 2
                      then arm_decode_vmov_i z
                      else if (=) opc2 0
                           then if (=) opc3 1
                                then arm_decode_vfp_other ARM_VMOV z
                                else arm_decode_vfp_other ARM_VABS z
                           else if (=) opc2 1
                                then if (=) opc3 1
                                     then arm_decode_vfp_other ARM_VNEG z
                                     else arm_decode_vfp_other ARM_VSQRT z
                                else if if (=) opc2 2
                                        then true
                                        else (=) opc2 3
                                     then Coq_idk
                                     else if if (=) opc2 4
                                             then true
                                             else (=) opc2 5
                                          then arm_decode_vcmp z
                                          else if if (=) opc2 7
                                                  then (=) opc3 3
                                                  else false
                                               then arm_decode_vcvt_ds z
                                               else if if if (=) opc2 8
                                                          then true
                                                          else (=) opc2 12
                                                       then true
                                                       else (=) opc2 13
                                                    then arm_decode_vcvt_fpi z
                                                    else if if if if 
                                                                    (=) opc2
                                                                    10
                                                                  then true
                                                                  else 
                                                                    (=) opc2
                                                                    11
                                                               then true
                                                               else (=) opc2
                                                                    14
                                                            then true
                                                            else (=) opc2 15
                                                         then arm_decode_vcvt_fpf
                                                                z
                                                         else ARM_UNDEFINED

(** val arm_decode_vmrs : int -> arm_inst **)

let arm_decode_vmrs z =
  let cond = zxbits z 28 32 in
  let rt = zxbits z 12 16 in
  if if (not) ((=) (zxbits z 5 8) 0)
     then true
     else (not) ((=) (zxbits z 0 4) 0)
  then ARM_UNPREDICTABLE
  else ARM_VMRS (cond, rt)

(** val arm_decode_8_16_32bit_transfer : int -> arm_inst **)

let arm_decode_8_16_32bit_transfer z =
  let a = zxbits z 21 24 in
  let l = bitb z 20 in
  let c = bitb z 8 in
  if (=) l 0
  then if (=) c 0
       then if (=) a 0 then arm_decode_vmov_r1 z else Coq_idk
       else Coq_idk
  else if (=) c 0
       then if (=) a 0
            then arm_decode_vmov_r1 z
            else if (=) a 7 then arm_decode_vmrs z else ARM_UNDEFINED
       else Coq_idk

(** val arm_decode_64bit_transfer : int -> arm_inst **)

let arm_decode_64bit_transfer z =
  let c = bitb z 8 in
  let op = zxbits z 4 8 in
  if (=) c 0
  then if if (=) op 1 then true else (=) op 3
       then arm_decode_vmov_r2 true z
       else ARM_UNDEFINED
  else if if (=) op 1 then true else (=) op 3
       then arm_decode_vmov_r2 false z
       else ARM_UNDEFINED

(** val arm_decode_coprocessor : int -> arm_inst **)

let arm_decode_coprocessor z =
  let op1 = zxbits z 20 26 in
  let op = bitb z 4 in
  let coproc = zxbits z 8 12 in
  if (=) (zxbits op1 1 6) 0
  then ARM_UNDEFINED
  else if (=) (zxbits op1 4 6) 3
       then arm_decode_svc z
       else if if (=) coproc 10 then true else (=) coproc 11
            then if (=) (zxbits op1 4 6) 2
                 then if (=) op 0
                      then arm_decode_floating_data_processing z
                      else arm_decode_8_16_32bit_transfer z
                 else if (=) (zxbits op1 1 6) 2
                      then arm_decode_64bit_transfer z
                      else arm_decode_vreg_ls z
            else if (=) op1 4
                 then Coq_idk
                 else if (=) op1 5
                      then Coq_idk
                      else if (=) (zxbits op1 4 6) 2
                           then if (=) op 0
                                then Coq_idk
                                else arm_decode_coproc_m ((=) (bitb op1 0) 0)
                                       z
                           else Coq_idk

(** val arm_decode_simd : int -> arm_inst **)

let arm_decode_simd _ =
  Coq_idk

(** val arm_decode_pld_r : int -> arm_inst **)

let arm_decode_pld_r z =
  let u = bitb z 23 in
  let r = bitb z 22 in
  let rn = zxbits z 16 20 in
  let imm5 = zxbits z 7 12 in
  let type0 = zxbits z 5 7 in
  let rm = zxbits z 0 4 in
  if if (=) rm 15 then true else if (=) rn 15 then (=) r 0 else false
  then ARM_UNPREDICTABLE
  else ARM_PLD_r (u, r, rn, imm5, type0, rm)

(** val arm_decode_pld_i : int -> arm_inst **)

let arm_decode_pld_i z =
  let u = bitb z 23 in
  let r = bitb z 22 in
  let rn = zxbits z 16 20 in
  let imm12 = zxbits z 0 12 in
  if (not) ((=) (zxbits z 12 16) 15)
  then ARM_UNPREDICTABLE
  else if if (=) rn 15 then (=) r 0 else false
       then ARM_UNPREDICTABLE
       else ARM_PLD_i (u, r, rn, imm12)

(** val arm_decode_mem_hint_simd : int -> arm_inst **)

let arm_decode_mem_hint_simd z =
  let op1 = zxbits z 20 27 in
  let op2 = zxbits z 4 8 in
  let op1'3 = zxbits op1 4 7 in
  let op1_3 = zxbits op1 0 3 in
  if (=) op1'3 0
  then ARM_UNDEFINED
  else if (=) op1'3 1
       then Coq_idk
       else if if (=) op1'3 2 then true else (=) op1'3 3
            then arm_decode_simd z
            else if (=) op1'3 4
                 then Coq_idk
                 else if (=) op1'3 5
                      then if if (=) op1_3 1 then true else (=) op1_3 5
                           then arm_decode_pld_i z
                           else if (=) op1_3 3
                                then ARM_UNPREDICTABLE
                                else if (=) op1_3 7
                                     then if (=) (bitb op1 3) 1
                                          then ARM_UNPREDICTABLE
                                          else if if if if (=) op2 0
                                                        then true
                                                        else (=) op2 2
                                                     then true
                                                     else (=) op2 3
                                                  then true
                                                  else (>=) op2 7
                                               then ARM_UNPREDICTABLE
                                               else Coq_idk
                                     else ARM_UNDEFINED
                      else if (=) op1'3 6
                           then if (=) (bitb op2 0) 0
                                then if (=) op1_3 1
                                     then Coq_idk
                                     else if if (=) op1_3 3
                                             then true
                                             else (=) op1_3 7
                                          then ARM_UNPREDICTABLE
                                          else if (=) op1_3 5
                                               then Coq_idk
                                               else ARM_UNDEFINED
                                else ARM_UNDEFINED
                           else if (=) (bitb op2 0) 0
                                then if if (=) op1_3 1
                                        then true
                                        else (=) op1_3 5
                                     then arm_decode_pld_r z
                                     else if if (=) op1_3 3
                                             then true
                                             else (=) op1_3 7
                                          then ARM_UNPREDICTABLE
                                          else ARM_UNDEFINED
                                else ARM_UNDEFINED

(** val arm_decode_unconditional : int -> arm_inst **)

let arm_decode_unconditional z =
  let op1 = zxbits z 20 28 in
  let op1_5 = zxbits op1 0 5 in
  let op1_3 = zxbits op1 5 8 in
  if if if if (=) op1_3 0 then true else (=) op1_3 1
        then true
        else (=) op1_3 2
     then true
     else (=) op1_3 3
  then arm_decode_mem_hint_simd z
  else if (=) op1_3 4
       then if if (=) (bitb op1 0) 0 then (=) (bitb op1 2) 1 else false
            then ARM_UNPREDICTABLE
            else if if (=) (bitb op1 0) 1 then (=) (bitb op1 2) 0 else false
                 then ARM_UNPREDICTABLE
                 else ARM_UNDEFINED
       else if (=) op1_3 5
            then arm_decode_blx_i z
            else if (=) op1_3 6
                 then if (=) op1_5 4
                      then Coq_idk
                      else if (=) op1_5 5
                           then Coq_idk
                           else if if if (=) (bitb op1 0) 0
                                      then (not) ((=) op1_5 0)
                                      else false
                                   then (not) ((=) op1_5 4)
                                   else false
                                then Coq_idk
                                else if if if (=) (bitb op1 0) 1
                                           then (not) ((=) op1_5 1)
                                           else false
                                        then (not) ((=) op1_5 5)
                                        else false
                                     then Coq_idk
                                     else ARM_UNDEFINED
                 else if if (=) op1_3 7 then (=) (bitb op1 4) 0 else false
                      then Coq_idk
                      else ARM_UNDEFINED

(** val arm_decode : int -> arm_inst **)

let arm_decode z =
  let cond = zxbits z 28 32 in
  let op1 = zxbits z 25 28 in
  let op = bitb z 4 in
  if (<=) z 0
  then ARM_UNDEFINED
  else if (=) cond 15
       then arm_decode_unconditional z
       else if if (=) op1 0 then true else (=) op1 1
            then arm_decode_data_misc z
            else if if (=) op1 2
                    then true
                    else if (=) op1 3 then (=) op 0 else false
                 then arm_decode_load_store z
                 else if if (=) op1 3 then (=) op 1 else false
                      then arm_decode_media z
                      else if if (=) op1 4 then true else (=) op1 5
                           then arm_decode_branch_block_transfer z
                           else arm_decode_coprocessor z

(** val internal_arm_vfp_other_op_beq :
    arm_vfp_other_op -> arm_vfp_other_op -> bool **)

let internal_arm_vfp_other_op_beq x y =
  match x with
  | ARM_VMOV -> (match y with
                 | ARM_VMOV -> true
                 | _ -> false)
  | ARM_VABS -> (match y with
                 | ARM_VABS -> true
                 | _ -> false)
  | ARM_VNEG -> (match y with
                 | ARM_VNEG -> true
                 | _ -> false)
  | ARM_VSQRT -> (match y with
                  | ARM_VSQRT -> true
                  | _ -> false)

(** val internal_arm_vfp_op_beq : arm_vfp_op -> arm_vfp_op -> bool **)

let internal_arm_vfp_op_beq x y =
  match x with
  | ARM_VMLA -> (match y with
                 | ARM_VMLA -> true
                 | _ -> false)
  | ARM_VNMLA -> (match y with
                  | ARM_VNMLA -> true
                  | _ -> false)
  | ARM_VMUL -> (match y with
                 | ARM_VMUL -> true
                 | _ -> false)
  | ARM_VADD -> (match y with
                 | ARM_VADD -> true
                 | _ -> false)
  | ARM_VSUB -> (match y with
                 | ARM_VSUB -> true
                 | _ -> false)
  | ARM_VDIV -> (match y with
                 | ARM_VDIV -> true
                 | _ -> false)
  | ARM_VFNMA -> (match y with
                  | ARM_VFNMA -> true
                  | _ -> false)
  | ARM_VFMA -> (match y with
                 | ARM_VFMA -> true
                 | _ -> false)

(** val internal_bool_beq : bool -> bool -> bool **)

let internal_bool_beq x y =
  if x then y else if y then false else true

(** val internal_arm_memm_op_beq : arm_memm_op -> arm_memm_op -> bool **)

let internal_arm_memm_op_beq x y =
  match x with
  | ARM_STMDA -> (match y with
                  | ARM_STMDA -> true
                  | _ -> false)
  | ARM_LDMDA -> (match y with
                  | ARM_LDMDA -> true
                  | _ -> false)
  | ARM_STMDB -> (match y with
                  | ARM_STMDB -> true
                  | _ -> false)
  | ARM_LDMDB -> (match y with
                  | ARM_LDMDB -> true
                  | _ -> false)
  | ARM_STMIA -> (match y with
                  | ARM_STMIA -> true
                  | _ -> false)
  | ARM_LDMIA -> (match y with
                  | ARM_LDMIA -> true
                  | _ -> false)
  | ARM_STMIB -> (match y with
                  | ARM_STMIB -> true
                  | _ -> false)
  | ARM_LDMIB -> (match y with
                  | ARM_LDMIB -> true
                  | _ -> false)

(** val internal_arm_extend_op_beq :
    arm_extend_op -> arm_extend_op -> bool **)

let internal_arm_extend_op_beq x y =
  match x with
  | ARM_XTAB16 -> (match y with
                   | ARM_XTAB16 -> true
                   | _ -> false)
  | ARM_XTAB -> (match y with
                 | ARM_XTAB -> true
                 | _ -> false)
  | ARM_XTAH -> (match y with
                 | ARM_XTAH -> true
                 | _ -> false)

(** val internal_arm_rev_op_beq : arm_rev_op -> arm_rev_op -> bool **)

let internal_arm_rev_op_beq x y =
  match x with
  | ARM_REV -> (match y with
                | ARM_REV -> true
                | _ -> false)
  | ARM_REV16 -> (match y with
                  | ARM_REV16 -> true
                  | _ -> false)
  | ARM_RBIT -> (match y with
                 | ARM_RBIT -> true
                 | _ -> false)
  | ARM_REVSH -> (match y with
                  | ARM_REVSH -> true
                  | _ -> false)

(** val internal_arm_pas_op_beq : arm_pas_op -> arm_pas_op -> bool **)

let internal_arm_pas_op_beq x y =
  match x with
  | ARM_ADD16 -> (match y with
                  | ARM_ADD16 -> true
                  | _ -> false)
  | ARM_ASX -> (match y with
                | ARM_ASX -> true
                | _ -> false)
  | ARM_SAX -> (match y with
                | ARM_SAX -> true
                | _ -> false)
  | ARM_SUB16 -> (match y with
                  | ARM_SUB16 -> true
                  | _ -> false)
  | ARM_ADD8 -> (match y with
                 | ARM_ADD8 -> true
                 | _ -> false)
  | ARM_SUB8 -> (match y with
                 | ARM_SUB8 -> true
                 | _ -> false)

(** val internal_arm_pas_type_beq : arm_pas_type -> arm_pas_type -> bool **)

let internal_arm_pas_type_beq x y =
  match x with
  | ARM_pas_normal -> (match y with
                       | ARM_pas_normal -> true
                       | _ -> false)
  | ARM_pas_saturating ->
    (match y with
     | ARM_pas_saturating -> true
     | _ -> false)
  | ARM_pas_halving -> (match y with
                        | ARM_pas_halving -> true
                        | _ -> false)

(** val internal_arm_mem_op_beq : arm_mem_op -> arm_mem_op -> bool **)

let internal_arm_mem_op_beq x y =
  match x with
  | ARM_LDR -> (match y with
                | ARM_LDR -> true
                | _ -> false)
  | ARM_STR -> (match y with
                | ARM_STR -> true
                | _ -> false)
  | ARM_LDRB -> (match y with
                 | ARM_LDRB -> true
                 | _ -> false)
  | ARM_STRB -> (match y with
                 | ARM_STRB -> true
                 | _ -> false)

(** val internal_arm_xmem_op_beq : arm_xmem_op -> arm_xmem_op -> bool **)

let internal_arm_xmem_op_beq x y =
  match x with
  | ARM_STRH -> (match y with
                 | ARM_STRH -> true
                 | _ -> false)
  | ARM_LDRH -> (match y with
                 | ARM_LDRH -> true
                 | _ -> false)
  | ARM_LDRD -> (match y with
                 | ARM_LDRD -> true
                 | _ -> false)
  | ARM_LDRSB -> (match y with
                  | ARM_LDRSB -> true
                  | _ -> false)
  | ARM_STRD -> (match y with
                 | ARM_STRD -> true
                 | _ -> false)
  | ARM_LDRSH -> (match y with
                  | ARM_LDRSH -> true
                  | _ -> false)

(** val internal_arm_sat_op_beq : arm_sat_op -> arm_sat_op -> bool **)

let internal_arm_sat_op_beq x y =
  match x with
  | ARM_QADD -> (match y with
                 | ARM_QADD -> true
                 | _ -> false)
  | ARM_QSUB -> (match y with
                 | ARM_QSUB -> true
                 | _ -> false)
  | ARM_QDADD -> (match y with
                  | ARM_QDADD -> true
                  | _ -> false)
  | ARM_QDSUB -> (match y with
                  | ARM_QDSUB -> true
                  | _ -> false)

(** val internal_arm_sync_size_beq :
    arm_sync_size -> arm_sync_size -> bool **)

let internal_arm_sync_size_beq x y =
  match x with
  | ARM_sync_word -> (match y with
                      | ARM_sync_word -> true
                      | _ -> false)
  | ARM_sync_doubleword ->
    (match y with
     | ARM_sync_doubleword -> true
     | _ -> false)
  | ARM_sync_byte -> (match y with
                      | ARM_sync_byte -> true
                      | _ -> false)
  | ARM_sync_halfword -> (match y with
                          | ARM_sync_halfword -> true
                          | _ -> false)

(** val internal_arm_hmul_op_beq : arm_hmul_op -> arm_hmul_op -> bool **)

let internal_arm_hmul_op_beq x y =
  match x with
  | ARM_SMLABB -> (match y with
                   | ARM_SMLABB -> true
                   | _ -> false)
  | ARM_SMLAWB -> (match y with
                   | ARM_SMLAWB -> true
                   | _ -> false)
  | ARM_SMULWB -> (match y with
                   | ARM_SMULWB -> true
                   | _ -> false)
  | ARM_SMLALBB -> (match y with
                    | ARM_SMLALBB -> true
                    | _ -> false)
  | ARM_SMULBB -> (match y with
                   | ARM_SMULBB -> true
                   | _ -> false)

(** val internal_arm_mul_op_beq : arm_mul_op -> arm_mul_op -> bool **)

let internal_arm_mul_op_beq x y =
  match x with
  | ARM_MUL -> (match y with
                | ARM_MUL -> true
                | _ -> false)
  | ARM_MLA -> (match y with
                | ARM_MLA -> true
                | _ -> false)
  | ARM_UMAAL -> (match y with
                  | ARM_UMAAL -> true
                  | _ -> false)
  | ARM_MLS -> (match y with
                | ARM_MLS -> true
                | _ -> false)
  | ARM_UMULL -> (match y with
                  | ARM_UMULL -> true
                  | _ -> false)
  | ARM_UMLAL -> (match y with
                  | ARM_UMLAL -> true
                  | _ -> false)
  | ARM_SMULL -> (match y with
                  | ARM_SMULL -> true
                  | _ -> false)
  | ARM_SMLAL -> (match y with
                  | ARM_SMLAL -> true
                  | _ -> false)

(** val internal_arm_data_op_beq : arm_data_op -> arm_data_op -> bool **)

let internal_arm_data_op_beq x y =
  match x with
  | ARM_AND -> (match y with
                | ARM_AND -> true
                | _ -> false)
  | ARM_EOR -> (match y with
                | ARM_EOR -> true
                | _ -> false)
  | ARM_SUB -> (match y with
                | ARM_SUB -> true
                | _ -> false)
  | ARM_RSB -> (match y with
                | ARM_RSB -> true
                | _ -> false)
  | ARM_ADD -> (match y with
                | ARM_ADD -> true
                | _ -> false)
  | ARM_ADC -> (match y with
                | ARM_ADC -> true
                | _ -> false)
  | ARM_SBC -> (match y with
                | ARM_SBC -> true
                | _ -> false)
  | ARM_RSC -> (match y with
                | ARM_RSC -> true
                | _ -> false)
  | ARM_TST -> (match y with
                | ARM_TST -> true
                | _ -> false)
  | ARM_TEQ -> (match y with
                | ARM_TEQ -> true
                | _ -> false)
  | ARM_CMP -> (match y with
                | ARM_CMP -> true
                | _ -> false)
  | ARM_CMN -> (match y with
                | ARM_CMN -> true
                | _ -> false)
  | ARM_ORR -> (match y with
                | ARM_ORR -> true
                | _ -> false)
  | ARM_MOV -> (match y with
                | ARM_MOV -> true
                | _ -> false)
  | ARM_BIC -> (match y with
                | ARM_BIC -> true
                | _ -> false)
  | ARM_MVN -> (match y with
                | ARM_MVN -> true
                | _ -> false)

(** val arm_inst_beq : arm_inst -> arm_inst -> bool **)

let arm_inst_beq x y =
  match x with
  | ARM_UNDEFINED -> (match y with
                      | ARM_UNDEFINED -> true
                      | _ -> false)
  | ARM_UNPREDICTABLE -> (match y with
                          | ARM_UNPREDICTABLE -> true
                          | _ -> false)
  | Coq_idk -> (match y with
                | Coq_idk -> true
                | _ -> false)
  | ARM_data_r (op, cond, s, rn, rd, imm5, type0, rm) ->
    (match y with
     | ARM_data_r (op0, cond0, s0, rn0, rd0, imm6, type1, rm0) ->
       if internal_arm_data_op_beq op op0
       then if (=) cond cond0
            then if (=) s s0
                 then if (=) rn rn0
                      then if (=) rd rd0
                           then if (=) imm5 imm6
                                then if (=) type0 type1
                                     then (=) rm rm0
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_data_rsr (op, cond, s, rn, rd, rs, type0, rm) ->
    (match y with
     | ARM_data_rsr (op0, cond0, s0, rn0, rd0, rs0, type1, rm0) ->
       if internal_arm_data_op_beq op op0
       then if (=) cond cond0
            then if (=) s s0
                 then if (=) rn rn0
                      then if (=) rd rd0
                           then if (=) rs rs0
                                then if (=) type0 type1
                                     then (=) rm rm0
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_data_i (op, cond, s, rn, rd, imm12) ->
    (match y with
     | ARM_data_i (op0, cond0, s0, rn0, rd0, imm13) ->
       if internal_arm_data_op_beq op op0
       then if (=) cond cond0
            then if (=) s s0
                 then if (=) rn rn0
                      then if (=) rd rd0 then (=) imm12 imm13 else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_MOV_WT (is_w, cond, imm4, rd, imm12) ->
    (match y with
     | ARM_MOV_WT (is_w0, cond0, imm5, rd0, imm13) ->
       if internal_bool_beq is_w is_w0
       then if (=) cond cond0
            then if (=) imm4 imm5
                 then if (=) rd rd0 then (=) imm12 imm13 else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_mul (op, cond, s, rd_RdHi, ra_RdLo, rm, rn) ->
    (match y with
     | ARM_mul (op0, cond0, s0, rd_RdHi0, ra_RdLo0, rm0, rn0) ->
       if internal_arm_mul_op_beq op op0
       then if (=) cond cond0
            then if (=) s s0
                 then if (=) rd_RdHi rd_RdHi0
                      then if (=) ra_RdLo ra_RdLo0
                           then if (=) rm rm0 then (=) rn rn0 else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_hmul (op, cond, rd, ra, rm, m, n, rn) ->
    (match y with
     | ARM_hmul (op0, cond0, rd0, ra0, rm0, m0, n0, rn0) ->
       if internal_arm_hmul_op_beq op op0
       then if (=) cond cond0
            then if (=) rd rd0
                 then if (=) ra ra0
                      then if (=) rm rm0
                           then if (=) m m0
                                then if (=) n n0 then (=) rn rn0 else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_sync_l (size, cond, rn, rt) ->
    (match y with
     | ARM_sync_l (size0, cond0, rn0, rt0) ->
       if internal_arm_sync_size_beq size size0
       then if (=) cond cond0
            then if (=) rn rn0 then (=) rt rt0 else false
            else false
       else false
     | _ -> false)
  | ARM_sync_s (size, cond, rn, rd, rt) ->
    (match y with
     | ARM_sync_s (size0, cond0, rn0, rd0, rt0) ->
       if internal_arm_sync_size_beq size size0
       then if (=) cond cond0
            then if (=) rn rn0
                 then if (=) rd rd0 then (=) rt rt0 else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_BX (cond, rm) ->
    (match y with
     | ARM_BX (cond0, rm0) -> if (=) cond cond0 then (=) rm rm0 else false
     | _ -> false)
  | ARM_BLX_r (cond, rm) ->
    (match y with
     | ARM_BLX_r (cond0, rm0) -> if (=) cond cond0 then (=) rm rm0 else false
     | _ -> false)
  | ARM_BXJ (cond, rm) ->
    (match y with
     | ARM_BXJ (cond0, rm0) -> if (=) cond cond0 then (=) rm rm0 else false
     | _ -> false)
  | ARM_CLZ (cond, rd, rm) ->
    (match y with
     | ARM_CLZ (cond0, rd0, rm0) ->
       if (=) cond cond0
       then if (=) rd rd0 then (=) rm rm0 else false
       else false
     | _ -> false)
  | ARM_BKPT (cond, imm12, imm4) ->
    (match y with
     | ARM_BKPT (cond0, imm13, imm5) ->
       if (=) cond cond0
       then if (=) imm12 imm13 then (=) imm4 imm5 else false
       else false
     | _ -> false)
  | ARM_sat (op, cond, rn, rd, rm) ->
    (match y with
     | ARM_sat (op0, cond0, rn0, rd0, rm0) ->
       if internal_arm_sat_op_beq op op0
       then if (=) cond cond0
            then if (=) rn rn0
                 then if (=) rd rd0 then (=) rm rm0 else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_hint (cond, op2) ->
    (match y with
     | ARM_hint (cond0, op3) -> if (=) cond cond0 then (=) op2 op3 else false
     | _ -> false)
  | ARM_extra_ls_i (op, cond, p, u, w, rn, rt, imm4H, imm4L) ->
    (match y with
     | ARM_extra_ls_i (op0, cond0, p0, u0, w0, rn0, rt0, imm4H0, imm4L0) ->
       if internal_arm_xmem_op_beq op op0
       then if (=) cond cond0
            then if (=) p p0
                 then if (=) u u0
                      then if (=) w w0
                           then if (=) rn rn0
                                then if (=) rt rt0
                                     then if (=) imm4H imm4H0
                                          then (=) imm4L imm4L0
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_extra_ls_r (op, cond, p, u, w, rn, rt, rm) ->
    (match y with
     | ARM_extra_ls_r (op0, cond0, p0, u0, w0, rn0, rt0, rm0) ->
       if internal_arm_xmem_op_beq op op0
       then if (=) cond cond0
            then if (=) p p0
                 then if (=) u u0
                      then if (=) w w0
                           then if (=) rn rn0
                                then if (=) rt rt0 then (=) rm rm0 else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_ls_i (op, cond, p, u, w, rn, rt, imm12) ->
    (match y with
     | ARM_ls_i (op0, cond0, p0, u0, w0, rn0, rt0, imm13) ->
       if internal_arm_mem_op_beq op op0
       then if (=) cond cond0
            then if (=) p p0
                 then if (=) u u0
                      then if (=) w w0
                           then if (=) rn rn0
                                then if (=) rt rt0
                                     then (=) imm12 imm13
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_ls_r (op, cond, p, u, w, rn, rt, imm5, type0, rm) ->
    (match y with
     | ARM_ls_r (op0, cond0, p0, u0, w0, rn0, rt0, imm6, type1, rm0) ->
       if internal_arm_mem_op_beq op op0
       then if (=) cond cond0
            then if (=) p p0
                 then if (=) u u0
                      then if (=) w w0
                           then if (=) rn rn0
                                then if (=) rt rt0
                                     then if (=) imm5 imm6
                                          then if (=) type0 type1
                                               then (=) rm rm0
                                               else false
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_pas (is_signed, type0, op, cond, rn, rd, rm) ->
    (match y with
     | ARM_pas (is_signed0, type1, op0, cond0, rn0, rd0, rm0) ->
       if internal_bool_beq is_signed is_signed0
       then if internal_arm_pas_type_beq type0 type1
            then if internal_arm_pas_op_beq op op0
                 then if (=) cond cond0
                      then if (=) rn rn0
                           then if (=) rd rd0 then (=) rm rm0 else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_rev (op, cond, rd, rm) ->
    (match y with
     | ARM_rev (op0, cond0, rd0, rm0) ->
       if internal_arm_rev_op_beq op op0
       then if (=) cond cond0
            then if (=) rd rd0 then (=) rm rm0 else false
            else false
       else false
     | _ -> false)
  | ARM_extend (is_signed, op, cond, rn, rd, rotate, rm) ->
    (match y with
     | ARM_extend (is_signed0, op0, cond0, rn0, rd0, rotate0, rm0) ->
       if internal_bool_beq is_signed is_signed0
       then if internal_arm_extend_op_beq op op0
            then if (=) cond cond0
                 then if (=) rn rn0
                      then if (=) rd rd0
                           then if (=) rotate rotate0
                                then (=) rm rm0
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_bfx (is_signed, cond, widthm1, rd, lsb, rn) ->
    (match y with
     | ARM_bfx (is_signed0, cond0, widthm2, rd0, lsb0, rn0) ->
       if internal_bool_beq is_signed is_signed0
       then if (=) cond cond0
            then if (=) widthm1 widthm2
                 then if (=) rd rd0
                      then if (=) lsb lsb0 then (=) rn rn0 else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_lsm (op, cond, w, rn, register_list) ->
    (match y with
     | ARM_lsm (op0, cond0, w0, rn0, register_list0) ->
       if internal_arm_memm_op_beq op op0
       then if (=) cond cond0
            then if (=) w w0
                 then if (=) rn rn0
                      then (=) register_list register_list0
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_B (cond, imm24) ->
    (match y with
     | ARM_B (cond0, imm25) ->
       if (=) cond cond0 then (=) imm24 imm25 else false
     | _ -> false)
  | ARM_BL (cond, imm24) ->
    (match y with
     | ARM_BL (cond0, imm25) ->
       if (=) cond cond0 then (=) imm24 imm25 else false
     | _ -> false)
  | ARM_BLX_i (h, imm24) ->
    (match y with
     | ARM_BLX_i (h0, imm25) -> if (=) h h0 then (=) imm24 imm25 else false
     | _ -> false)
  | ARM_SVC (cond, imm24) ->
    (match y with
     | ARM_SVC (cond0, imm25) ->
       if (=) cond cond0 then (=) imm24 imm25 else false
     | _ -> false)
  | ARM_coproc_m (is_cr, cond, opc1, cRn, rt, coproc, opc2, cRm) ->
    (match y with
     | ARM_coproc_m (is_cr0, cond0, opc3, cRn0, rt0, coproc0, opc4, cRm0) ->
       if internal_bool_beq is_cr is_cr0
       then if (=) cond cond0
            then if (=) opc1 opc3
                 then if (=) cRn cRn0
                      then if (=) rt rt0
                           then if (=) coproc coproc0
                                then if (=) opc2 opc4
                                     then (=) cRm cRm0
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_vls (is_load, is_single, cond, u, d, rn, vd, imm8) ->
    (match y with
     | ARM_vls (is_load0, is_single0, cond0, u0, d0, rn0, vd0, imm9) ->
       if internal_bool_beq is_load is_load0
       then if internal_bool_beq is_single is_single0
            then if (=) cond cond0
                 then if (=) u u0
                      then if (=) d d0
                           then if (=) rn rn0
                                then if (=) vd vd0
                                     then (=) imm8 imm9
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_vlsm (is_load, is_single, cond, p, u, d, w, rn, rd, imm8) ->
    (match y with
     | ARM_vlsm (is_load0, is_single0, cond0, p0, u0, d0, w0, rn0, rd0, imm9) ->
       if internal_bool_beq is_load is_load0
       then if internal_bool_beq is_single is_single0
            then if (=) cond cond0
                 then if (=) p p0
                      then if (=) u u0
                           then if (=) d d0
                                then if (=) w w0
                                     then if (=) rn rn0
                                          then if (=) rd rd0
                                               then (=) imm8 imm9
                                               else false
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VMOV_i (cond, d, imm4H, vd, sz, imm4L) ->
    (match y with
     | ARM_VMOV_i (cond0, d0, imm4H0, vd0, sz0, imm4L0) ->
       if (=) cond cond0
       then if (=) d d0
            then if (=) imm4H imm4H0
                 then if (=) vd vd0
                      then if (=) sz sz0 then (=) imm4L imm4L0 else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VMOV_r2 (is_single, cond, op, rt2, rt, m, vm) ->
    (match y with
     | ARM_VMOV_r2 (is_single0, cond0, op0, rt3, rt0, m0, vm0) ->
       if internal_bool_beq is_single is_single0
       then if (=) cond cond0
            then if (=) op op0
                 then if (=) rt2 rt3
                      then if (=) rt rt0
                           then if (=) m m0 then (=) vm vm0 else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VMOV_r1 (cond, op, vn, rt, n) ->
    (match y with
     | ARM_VMOV_r1 (cond0, op0, vn0, rt0, n0) ->
       if (=) cond cond0
       then if (=) op op0
            then if (=) vn vn0
                 then if (=) rt rt0 then (=) n n0 else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_vfp (op, cond, d, vn, vd, sz, n, op0, m, vm) ->
    (match y with
     | ARM_vfp (op1, cond0, d0, vn0, vd0, sz0, n0, op2, m0, vm0) ->
       if internal_arm_vfp_op_beq op op1
       then if (=) cond cond0
            then if (=) d d0
                 then if (=) vn vn0
                      then if (=) vd vd0
                           then if (=) sz sz0
                                then if (=) n n0
                                     then if (=) op0 op2
                                          then if (=) m m0
                                               then (=) vm vm0
                                               else false
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VCMP (cond, d, vd, sz, e, m, vm) ->
    (match y with
     | ARM_VCMP (cond0, d0, vd0, sz0, e0, m0, vm0) ->
       if (=) cond cond0
       then if (=) d d0
            then if (=) vd vd0
                 then if (=) sz sz0
                      then if (=) e e0
                           then if (=) m m0 then (=) vm vm0 else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VMRS (cond, rt) ->
    (match y with
     | ARM_VMRS (cond0, rt0) -> if (=) cond cond0 then (=) rt rt0 else false
     | _ -> false)
  | ARM_VCVT_fpi (cond, d, opc2, vd, sz, op, m, vm) ->
    (match y with
     | ARM_VCVT_fpi (cond0, d0, opc3, vd0, sz0, op0, m0, vm0) ->
       if (=) cond cond0
       then if (=) d d0
            then if (=) opc2 opc3
                 then if (=) vd vd0
                      then if (=) sz sz0
                           then if (=) op op0
                                then if (=) m m0 then (=) vm vm0 else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VCVT_fpf (cond, d, op, u, vd, sf, sx, i, imm4) ->
    (match y with
     | ARM_VCVT_fpf (cond0, d0, op0, u0, vd0, sf0, sx0, i0, imm5) ->
       if (=) cond cond0
       then if (=) d d0
            then if (=) op op0
                 then if (=) u u0
                      then if (=) vd vd0
                           then if (=) sf sf0
                                then if (=) sx sx0
                                     then if (=) i i0
                                          then (=) imm4 imm5
                                          else false
                                     else false
                                else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_VCVT_ds (cond, d, vd, sz, m, vm) ->
    (match y with
     | ARM_VCVT_ds (cond0, d0, vd0, sz0, m0, vm0) ->
       if (=) cond cond0
       then if (=) d d0
            then if (=) vd vd0
                 then if (=) sz sz0
                      then if (=) m m0 then (=) vm vm0 else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_vfp_other (op, cond, d, vd, sz, m, vm) ->
    (match y with
     | ARM_vfp_other (op0, cond0, d0, vd0, sz0, m0, vm0) ->
       if internal_arm_vfp_other_op_beq op op0
       then if (=) cond cond0
            then if (=) d d0
                 then if (=) vd vd0
                      then if (=) sz sz0
                           then if (=) m m0 then (=) vm vm0 else false
                           else false
                      else false
                 else false
            else false
       else false
     | _ -> false)
  | ARM_PLD_i (u, r, rn, imm12) ->
    (match y with
     | ARM_PLD_i (u0, r0, rn0, imm13) ->
       if (=) u u0
       then if (=) r r0
            then if (=) rn rn0 then (=) imm12 imm13 else false
            else false
       else false
     | _ -> false)
  | ARM_PLD_r (u, r, rn, imm5, type0, rm) ->
    (match y with
     | ARM_PLD_r (u0, r0, rn0, imm6, type1, rm0) ->
       if (=) u u0
       then if (=) r r0
            then if (=) rn rn0
                 then if (=) imm5 imm6
                      then if (=) type0 type1 then (=) rm rm0 else false
                      else false
                 else false
            else false
       else false
     | _ -> false)

(** val arm_data_opcode : arm_data_op -> int **)

let arm_data_opcode = function
| ARM_AND -> 0
| ARM_EOR -> 1
| ARM_SUB -> 2
| ARM_RSB -> 3
| ARM_ADD -> 4
| ARM_ADC -> 5
| ARM_SBC -> 6
| ARM_RSC -> 7
| ARM_TST -> 8
| ARM_TEQ -> 9
| ARM_CMP -> 10
| ARM_CMN -> 11
| ARM_ORR -> 12
| ARM_MOV -> 13
| ARM_BIC -> 14
| ARM_MVN -> 15

(** val arm_assemble_data_r :
    arm_data_op -> int -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_data_r op cond s rn rd imm5 type0 rm =
  let op0 = arm_data_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) op0 21)) ((lsl) s 20))
            ((lsl) rn 16)) ((lsl) rd 12)) ((lsl) imm5 7)) ((lsl) type0 5)) rm

(** val arm_assemble_data_rsr :
    arm_data_op -> int -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_data_rsr op cond s rn rd rs type0 rm =
  let op0 = arm_data_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor)
              ((lor) ((lor) ((lsl) cond 28) ((lsl) op0 21)) ((lsl) s 20))
              ((lsl) rn 16)) ((lsl) rd 12)) ((lsl) rs 8)) ((lsl) type0 5))
      ((lsl) 1 4)) rm

(** val arm_assemble_data_i :
    arm_data_op -> int -> int -> int -> int -> int -> int **)

let arm_assemble_data_i op cond s rn rd imm12 =
  let op0 = arm_data_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 1 25)) ((lsl) op0 21))
          ((lsl) s 20)) ((lsl) rn 16)) ((lsl) rd 12)) imm12

(** val arm_assemble_MOV_WT : bool -> int -> int -> int -> int -> int **)

let arm_assemble_MOV_WT is_w cond imm4 rd imm12 =
  let op = if is_w then 16 else 20 in
  (lor)
    ((lor)
      ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 1 25)) ((lsl) op 20))
        ((lsl) imm4 16)) ((lsl) rd 12)) imm12

(** val arm_mul_opcode : arm_mul_op -> int **)

let arm_mul_opcode = function
| ARM_MUL -> 0
| ARM_MLA -> 1
| ARM_UMAAL -> 2
| ARM_MLS -> 3
| ARM_UMULL -> 4
| ARM_UMLAL -> 5
| ARM_SMULL -> 6
| ARM_SMLAL -> 7

(** val arm_assemble_mul :
    arm_mul_op -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_mul op cond s rd_RdHi ra_RdLo rm rn =
  let op0 = arm_mul_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) op0 21)) ((lsl) s 20))
            ((lsl) rd_RdHi 16)) ((lsl) ra_RdLo 12)) ((lsl) rm 8)) ((lsl) 9 4))
    rn

(** val arm_sync_size_opcode : arm_sync_size -> int **)

let arm_sync_size_opcode = function
| ARM_sync_word -> 0
| ARM_sync_doubleword -> 1
| ARM_sync_byte -> 2
| ARM_sync_halfword -> 3

(** val arm_assemble_sync_l : arm_sync_size -> int -> int -> int -> int **)

let arm_assemble_sync_l size cond rn rt =
  let size0 = arm_sync_size_opcode size in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor)
              ((lor) ((lor) ((lsl) cond 28) ((lsl) 3 23)) ((lsl) size0 21))
              ((lsl) 1 20)) ((lsl) rn 16)) ((lsl) rt 12)) ((lsl) 15 8))
      ((lsl) 9 4)) 15

(** val arm_assemble_sync_s :
    arm_sync_size -> int -> int -> int -> int -> int **)

let arm_assemble_sync_s size cond rn rd rt =
  let size0 = arm_sync_size_opcode size in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor) ((lor) ((lsl) cond 28) ((lsl) 3 23)) ((lsl) size0 21))
            ((lsl) rn 16)) ((lsl) rd 12)) ((lsl) 15 8)) ((lsl) 9 4)) rt

(** val arm_assemble_BX : int -> int -> int **)

let arm_assemble_BX cond rm =
  (lor)
    ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 9 21)) ((lsl) 4095 8))
      ((lsl) 1 4)) rm

(** val arm_assemble_BLX_r : int -> int -> int **)

let arm_assemble_BLX_r cond rm =
  (lor)
    ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 9 21)) ((lsl) 4095 8))
      ((lsl) 3 4)) rm

(** val arm_assemble_BXJ : int -> int -> int **)

let arm_assemble_BXJ cond rm =
  (lor)
    ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 9 21)) ((lsl) 4095 8))
      ((lsl) 2 4)) rm

(** val arm_assemble_CLZ : int -> int -> int -> int **)

let arm_assemble_CLZ cond rd rm =
  (lor)
    ((lor)
      ((lor)
        ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 11 21)) ((lsl) 15 16))
          ((lsl) rd 12)) ((lsl) 15 8)) ((lsl) 1 4)) rm

(** val arm_assemble_BKPT : int -> int -> int -> int **)

let arm_assemble_BKPT cond imm12 imm4 =
  (lor)
    ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 9 21)) ((lsl) imm12 8))
      ((lsl) 7 4)) imm4

(** val arm_sat_opcode : arm_sat_op -> int **)

let arm_sat_opcode = function
| ARM_QADD -> 0
| ARM_QSUB -> 1
| ARM_QDADD -> 2
| ARM_QDSUB -> 3

(** val arm_assemble_sat : arm_sat_op -> int -> int -> int -> int -> int **)

let arm_assemble_sat op cond rn rd rm =
  let op0 = arm_sat_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 1 24)) ((lsl) op0 21))
          ((lsl) rn 16)) ((lsl) rd 12)) ((lsl) 5 4)) rm

(** val arm_assemble_hint : int -> int -> int **)

let arm_assemble_hint cond op2 =
  (lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 25 21)) ((lsl) 15 12)) op2

(** val arm_xmem_opcode : arm_xmem_op -> int **)

let arm_xmem_opcode = function
| ARM_STRH -> 11
| ARM_LDRH -> (lor) 11 ((lsl) 1 16)
| ARM_LDRD -> 13
| ARM_LDRSB -> (lor) 13 ((lsl) 1 16)
| ARM_STRD -> 15
| ARM_LDRSH -> (lor) 15 ((lsl) 1 16)

(** val arm_assemble_extra_ls_i :
    arm_xmem_op -> int -> int -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_extra_ls_i op cond p u w rn rt imm4H imm4L =
  let op0 = arm_xmem_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor)
              ((lor)
                ((lor) ((lor) ((lsl) cond 28) ((lsl) p 24)) ((lsl) u 23))
                ((lsl) 1 22)) ((lsl) w 21)) ((lsl) rn 16)) ((lsl) rt 12))
        ((lsl) imm4H 8)) ((lsl) op0 4)) imm4L

(** val arm_assemble_extra_ls_r :
    arm_xmem_op -> int -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_extra_ls_r op cond p u w rn rt rm =
  let op0 = arm_xmem_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) p 24)) ((lsl) u 23))
            ((lsl) w 21)) ((lsl) rn 16)) ((lsl) rt 12)) ((lsl) op0 4)) rm

(** val arm_mem_opcode : arm_mem_op -> int **)

let arm_mem_opcode = function
| ARM_LDR -> 1
| ARM_STR -> 0
| ARM_LDRB -> 5
| ARM_STRB -> 4

(** val arm_assemble_ls_i :
    arm_mem_op -> int -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_ls_i op cond p u w rn rt imm12 =
  let op0 = arm_mem_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 1 26)) ((lsl) p 24))
              ((lsl) u 23)) ((lsl) w 21)) ((lsl) op0 20)) ((lsl) rn 16))
      ((lsl) rt 12)) imm12

(** val arm_assemble_ls_r :
    arm_mem_op -> int -> int -> int -> int -> int -> int -> int -> int -> int
    -> int **)

let arm_assemble_ls_r op cond p u w rn rt imm5 type0 rm =
  let op0 = arm_mem_opcode op in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor)
              ((lor)
                ((lor)
                  ((lor) ((lor) ((lsl) cond 28) ((lsl) 3 25)) ((lsl) p 24))
                  ((lsl) u 23)) ((lsl) w 21)) ((lsl) op0 20)) ((lsl) rn 16))
          ((lsl) rt 12)) ((lsl) imm5 7)) ((lsl) type0 5)) rm

(** val arm_memm_opcode : arm_memm_op -> int **)

let arm_memm_opcode = function
| ARM_STMDA -> 0
| ARM_LDMDA -> 1
| ARM_STMDB -> 16
| ARM_LDMDB -> 17
| ARM_STMIA -> 8
| ARM_LDMIA -> 9
| ARM_STMIB -> 24
| ARM_LDMIB -> 25

(** val arm_assemble_lsm : arm_memm_op -> int -> int -> int -> int -> int **)

let arm_assemble_lsm op cond w rn register_list =
  let op0 = arm_memm_opcode op in
  (lor)
    ((lor)
      ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 1 27)) ((lsl) w 21))
        ((lsl) op0 20)) ((lsl) rn 16)) register_list

(** val arm_assemble_B : int -> int -> int **)

let arm_assemble_B cond imm24 =
  (lor) ((lor) ((lsl) cond 28) ((lsl) 10 24)) imm24

(** val arm_assemble_BL : int -> int -> int **)

let arm_assemble_BL cond imm24 =
  (lor) ((lor) ((lsl) cond 28) ((lsl) 11 24)) imm24

(** val arm_assemble_BLX_i : int -> int -> int **)

let arm_assemble_BLX_i h imm24 =
  (lor) ((lor) ((lor) ((lsl) 15 28) ((lsl) 10 24)) ((lsl) h 24)) imm24

(** val arm_assemble_vls :
    bool -> bool -> int -> int -> int -> int -> int -> int -> int **)

let arm_assemble_vls is_load is_single cond u d rn vd imm8 =
  let is_load0 = if is_load then 1 else 0 in
  let x = if is_single then 10 else 11 in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor)
            ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 13 24)) ((lsl) u 23))
              ((lsl) d 22)) ((lsl) is_load0 20)) ((lsl) rn 16)) ((lsl) vd 12))
      ((lsl) x 8)) imm8

(** val arm_assemble_bfx : bool -> int -> int -> int -> int -> int -> int **)

let arm_assemble_bfx is_signed cond msb_widthm1 rd lsb rn =
  let op1 = if is_signed then 13 else 15 in
  (lor)
    ((lor)
      ((lor)
        ((lor)
          ((lor) ((lor) ((lor) ((lsl) cond 28) ((lsl) 3 25)) ((lsl) op1 21))
            ((lsl) msb_widthm1 16)) ((lsl) rd 12)) ((lsl) lsb 7)) ((lsl) 5 4))
    rn

(** val arm_assemble : arm_inst -> int option **)

let arm_assemble i =
  let z =
    match i with
    | ARM_data_r (op, cond, s, rn, rd, imm5, type0, rm) ->
      arm_assemble_data_r op cond s rn rd imm5 type0 rm
    | ARM_data_rsr (op, cond, s, rn, rd, rs, type0, rm) ->
      arm_assemble_data_rsr op cond s rn rd rs type0 rm
    | ARM_data_i (op, cond, s, rn, rd, imm12) ->
      arm_assemble_data_i op cond s rn rd imm12
    | ARM_MOV_WT (is_w, cond, imm4, rd, imm12) ->
      arm_assemble_MOV_WT is_w cond imm4 rd imm12
    | ARM_mul (op, cond, s, rd_RdHi, ra_RdLo, rm, rn) ->
      arm_assemble_mul op cond s rd_RdHi ra_RdLo rm rn
    | ARM_sync_l (size, cond, rn, rt) -> arm_assemble_sync_l size cond rn rt
    | ARM_sync_s (size, cond, rn, rd, rt) ->
      arm_assemble_sync_s size cond rn rd rt
    | ARM_BX (cond, rm) -> arm_assemble_BX cond rm
    | ARM_BLX_r (cond, rm) -> arm_assemble_BLX_r cond rm
    | ARM_BXJ (cond, rm) -> arm_assemble_BXJ cond rm
    | ARM_CLZ (cond, rd, rm) -> arm_assemble_CLZ cond rd rm
    | ARM_BKPT (cond, imm12, imm4) -> arm_assemble_BKPT cond imm12 imm4
    | ARM_sat (op, cond, rn, rd, rm) -> arm_assemble_sat op cond rn rd rm
    | ARM_hint (cond, op2) -> arm_assemble_hint cond op2
    | ARM_extra_ls_i (op, cond, p, u, w, rn, rt, imm4H, imm4L) ->
      arm_assemble_extra_ls_i op cond p u w rn rt imm4H imm4L
    | ARM_extra_ls_r (op, cond, p, u, w, rn, rt, rm) ->
      arm_assemble_extra_ls_r op cond p u w rn rt rm
    | ARM_ls_i (op, cond, p, u, w, rn, rt, imm12) ->
      arm_assemble_ls_i op cond p u w rn rt imm12
    | ARM_ls_r (op, cond, p, u, w, rn, rt, imm5, type0, rm) ->
      arm_assemble_ls_r op cond p u w rn rt imm5 type0 rm
    | ARM_bfx (is_signed, cond, msb_widthm1, rd, lsb, rn) ->
      arm_assemble_bfx is_signed cond msb_widthm1 rd lsb rn
    | ARM_lsm (op, cond, w, rn, register_list) ->
      arm_assemble_lsm op cond w rn register_list
    | ARM_B (cond, imm24) -> arm_assemble_B cond imm24
    | ARM_BL (cond, imm24) -> arm_assemble_BL cond imm24
    | ARM_BLX_i (h, imm24) -> arm_assemble_BLX_i h imm24
    | ARM_vls (is_load, is_single, cond, u, d, rn, vd, imm8) ->
      arm_assemble_vls is_load is_single cond u d rn vd imm8
    | _ -> 0
  in
  if arm_inst_beq (arm_decode z) i then Some z else None

(** val arm_assemble_all : arm_inst list -> int list option **)

let rec arm_assemble_all = function
| [] -> Some []
| a::t ->
  (match arm_assemble a with
   | Some z ->
     (match arm_assemble_all t with
      | Some zs -> Some (z::zs)
      | None -> None)
   | None -> None)

(** val arm_lsm_op_start : arm_memm_op -> int -> int **)

let arm_lsm_op_start op bc =
  match op with
  | ARM_STMDA -> (+) ((~-) bc) 4
  | ARM_LDMDA -> (+) ((~-) bc) 4
  | ARM_STMDB -> (~-) bc
  | ARM_LDMDB -> (~-) bc
  | ARM_STMIA -> 0
  | ARM_LDMIA -> 0
  | _ -> 4
