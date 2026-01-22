
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

val zxbits : int -> int -> int -> int

val bitb : int -> int -> int

val arm_decode_data_r : arm_data_op -> int -> arm_inst

val arm_decode_data_rsr : arm_data_op -> int -> arm_inst

val arm_decode_data_i : arm_data_op -> int -> arm_inst

val arm_decode_data_rd0 :
  (arm_data_op -> int -> arm_inst) -> arm_data_op -> int -> arm_inst

val arm_decode_data_rn0 :
  (arm_data_op -> int -> arm_inst) -> arm_data_op -> int -> arm_inst

val arm_decode_data_processing :
  (arm_data_op -> int -> arm_inst) -> int -> arm_inst

val arm_decode_sat : arm_sat_op -> int -> arm_inst

val arm_decode_saturating_add_sub : int -> arm_inst

val arm_decode_mov_wt : bool -> int -> arm_inst

val arm_decode_bx : int -> arm_inst

val arm_decode_clz : int -> arm_inst

val arm_decode_bxj : int -> arm_inst

val arm_decode_blx_r : int -> arm_inst

val arm_decode_bkpt : int -> arm_inst

val arm_decode_b : int -> arm_inst

val arm_decode_bl : int -> arm_inst

val arm_decode_blx_i : int -> arm_inst

val arm_decode_misc : int -> arm_inst

val arm_decode_hmul : arm_hmul_op -> int -> arm_inst

val arm_decode_halfword_multiply : int -> arm_inst

val arm_decode_mul : arm_mul_op -> int -> arm_inst

val arm_decode_multiply : int -> arm_inst

val arm_decode_sync_s : arm_sync_size -> int -> arm_inst

val arm_decode_sync_l : arm_sync_size -> int -> arm_inst

val arm_decode_sync_primitives : int -> arm_inst

val arm_decode_extra_ls_i : arm_xmem_op -> int -> arm_inst

val arm_decode_extra_ls_r : arm_xmem_op -> int -> arm_inst

val arm_decode_extra_load_store : int -> arm_inst

val arm_decode_hint : int -> arm_inst

val arm_decode_msr_hints : int -> arm_inst

val arm_decode_data_misc : int -> arm_inst

val arm_decode_ls_r : arm_mem_op -> int -> arm_inst

val arm_decode_ls_i : arm_mem_op -> int -> arm_inst

val arm_decode_load_store : int -> arm_inst

val arm_decode_pas : bool -> arm_pas_type -> arm_pas_op -> int -> arm_inst

val arm_decode_parallel_add_sub : int -> arm_inst

val arm_decode_rev : arm_rev_op -> int -> arm_inst

val arm_decode_extend : bool -> arm_extend_op -> int -> arm_inst

val arm_decode_packing : int -> arm_inst

val arm_decode_signed_multiply : int -> arm_inst

val arm_decode_bfx : bool -> int -> arm_inst

val arm_decode_media : int -> arm_inst

val arm_decode_lsm : arm_memm_op -> int -> arm_inst

val arm_decode_branch_block_transfer : int -> arm_inst

val arm_decode_svc : int -> arm_inst

val arm_decode_coproc_m : bool -> int -> arm_inst

val arm_decode_vls : bool -> int -> arm_inst

val arm_decode_vlsm : bool -> int -> arm_inst

val arm_decode_vreg_ls : int -> arm_inst

val arm_decode_vmov_i : int -> arm_inst

val arm_decode_vmov_r2 : bool -> int -> arm_inst

val arm_decode_vmov_r1 : int -> arm_inst

val arm_decode_vcmp : int -> arm_inst

val arm_decode_vfp : arm_vfp_op -> int -> arm_inst

val arm_decode_vcvt_ds : int -> arm_inst

val arm_decode_vcvt_fpi : int -> arm_inst

val arm_decode_vcvt_fpf : int -> arm_inst

val arm_decode_vfp_other : arm_vfp_other_op -> int -> arm_inst

val arm_decode_floating_data_processing : int -> arm_inst

val arm_decode_vmrs : int -> arm_inst

val arm_decode_8_16_32bit_transfer : int -> arm_inst

val arm_decode_64bit_transfer : int -> arm_inst

val arm_decode_coprocessor : int -> arm_inst

val arm_decode_simd : int -> arm_inst

val arm_decode_pld_r : int -> arm_inst

val arm_decode_pld_i : int -> arm_inst

val arm_decode_mem_hint_simd : int -> arm_inst

val arm_decode_unconditional : int -> arm_inst

val arm_decode : int -> arm_inst

val internal_arm_vfp_other_op_beq :
  arm_vfp_other_op -> arm_vfp_other_op -> bool

val internal_arm_vfp_op_beq : arm_vfp_op -> arm_vfp_op -> bool

val internal_bool_beq : bool -> bool -> bool

val internal_arm_memm_op_beq : arm_memm_op -> arm_memm_op -> bool

val internal_arm_extend_op_beq : arm_extend_op -> arm_extend_op -> bool

val internal_arm_rev_op_beq : arm_rev_op -> arm_rev_op -> bool

val internal_arm_pas_op_beq : arm_pas_op -> arm_pas_op -> bool

val internal_arm_pas_type_beq : arm_pas_type -> arm_pas_type -> bool

val internal_arm_mem_op_beq : arm_mem_op -> arm_mem_op -> bool

val internal_arm_xmem_op_beq : arm_xmem_op -> arm_xmem_op -> bool

val internal_arm_sat_op_beq : arm_sat_op -> arm_sat_op -> bool

val internal_arm_sync_size_beq : arm_sync_size -> arm_sync_size -> bool

val internal_arm_hmul_op_beq : arm_hmul_op -> arm_hmul_op -> bool

val internal_arm_mul_op_beq : arm_mul_op -> arm_mul_op -> bool

val internal_arm_data_op_beq : arm_data_op -> arm_data_op -> bool

val arm_inst_beq : arm_inst -> arm_inst -> bool

val arm_data_opcode : arm_data_op -> int

val arm_assemble_data_r :
  arm_data_op -> int -> int -> int -> int -> int -> int -> int -> int

val arm_assemble_data_rsr :
  arm_data_op -> int -> int -> int -> int -> int -> int -> int -> int

val arm_assemble_data_i :
  arm_data_op -> int -> int -> int -> int -> int -> int

val arm_assemble_MOV_WT : bool -> int -> int -> int -> int -> int

val arm_mul_opcode : arm_mul_op -> int

val arm_assemble_mul :
  arm_mul_op -> int -> int -> int -> int -> int -> int -> int

val arm_sync_size_opcode : arm_sync_size -> int

val arm_assemble_sync_l : arm_sync_size -> int -> int -> int -> int

val arm_assemble_sync_s : arm_sync_size -> int -> int -> int -> int -> int

val arm_assemble_BX : int -> int -> int

val arm_assemble_BLX_r : int -> int -> int

val arm_assemble_BXJ : int -> int -> int

val arm_assemble_CLZ : int -> int -> int -> int

val arm_assemble_BKPT : int -> int -> int -> int

val arm_sat_opcode : arm_sat_op -> int

val arm_assemble_sat : arm_sat_op -> int -> int -> int -> int -> int

val arm_assemble_hint : int -> int -> int

val arm_xmem_opcode : arm_xmem_op -> int

val arm_assemble_extra_ls_i :
  arm_xmem_op -> int -> int -> int -> int -> int -> int -> int -> int -> int

val arm_assemble_extra_ls_r :
  arm_xmem_op -> int -> int -> int -> int -> int -> int -> int -> int

val arm_mem_opcode : arm_mem_op -> int

val arm_assemble_ls_i :
  arm_mem_op -> int -> int -> int -> int -> int -> int -> int -> int

val arm_assemble_ls_r :
  arm_mem_op -> int -> int -> int -> int -> int -> int -> int -> int -> int
  -> int

val arm_memm_opcode : arm_memm_op -> int

val arm_assemble_lsm : arm_memm_op -> int -> int -> int -> int -> int

val arm_assemble_B : int -> int -> int

val arm_assemble_BL : int -> int -> int

val arm_assemble_BLX_i : int -> int -> int

val arm_assemble_vls :
  bool -> bool -> int -> int -> int -> int -> int -> int -> int

val arm_assemble_bfx : bool -> int -> int -> int -> int -> int -> int

val arm_assemble : arm_inst -> int option

val arm_assemble_all : arm_inst list -> int list option

val arm_lsm_op_start : arm_memm_op -> int -> int
