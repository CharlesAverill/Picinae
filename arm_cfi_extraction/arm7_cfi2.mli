open BinNums
open Picinae_armv7_lifter

val unique_except_pairs : int list -> int list -> bool

val apply_hash : int -> int -> int -> int

val valid_hash : int list -> int list -> int -> int -> bool

val find_sr : int list -> int list -> int -> int -> int option

val find_hash : int list -> int list -> int -> (int * int) option

val make_jump_table_map :
  int list -> int list -> int -> int -> (int -> int) -> int -> int

val map2list : (int -> int) -> int -> int list

val make_jump_table :
  int list -> int list -> int -> int -> int -> int -> int list

val coq_PC : int

val coq_LR : int

val coq_SP : int

val coq_STR : int -> int -> int -> arm_inst

val coq_LDR : int -> int -> int -> arm_inst

val coq_MOVW : int -> int -> arm_inst

val coq_MOVT : int -> int -> arm_inst

val coq_MOV : int -> int -> arm_inst

val coq_LSL : int -> int -> int -> arm_inst

val coq_STMDB2 : int -> int -> int -> arm_inst

val coq_LDMDB2 : int -> int -> int -> arm_inst

val coq_STMDB3 : int -> int -> int -> int -> arm_inst

val coq_LDMDB3 : int -> int -> int -> int -> arm_inst

val coq_UBFX : int -> int -> int -> int -> arm_inst

val coq_GOTO : bool -> int -> int -> int -> arm_inst option

val coq_GOTOz : bool -> int -> int -> int -> int option

val arm_add : int -> int -> arm_inst list

val arm_table_lookup : int -> int -> int -> int -> arm_inst list

type coq_IRM = int -> int -> int -> int -> int -> int list option

type coq_TableCache = int list -> ((int * int) * int) option

type coq_NewInst = ((int list * int list) * coq_TableCache) option

val wo_table : int list option -> coq_TableCache -> coq_NewInst

val invert_cond : int -> int

val arm_assemble_all_cond : arm_inst list -> int -> int list option

val list_eqb : int list -> int list -> bool

val rewrite_w_table :
  coq_IRM -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int
  -> int -> coq_NewInst

val bx_irm : int -> coq_IRM

val rewrite_bx :
  int -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int ->
  int -> coq_NewInst

val blx_irm : int -> coq_IRM

val rewrite_blx :
  int -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int ->
  int -> coq_NewInst

val ldm_pc_irm : arm_memm_op -> int -> int -> int -> arm_inst -> coq_IRM

val rewrite_ldm_pc :
  arm_memm_op -> int -> int -> int -> arm_inst -> coq_TableCache -> int list
  -> (int -> int) -> int -> int -> int -> int -> coq_NewInst

val pc_irm : arm_inst -> int -> coq_IRM

val pc_sp_irm : arm_inst -> int -> int -> coq_IRM

val rewrite_pc :
  arm_inst -> int -> coq_TableCache -> int list -> (int -> int) -> int -> int
  -> int -> int -> coq_NewInst

val rewrite_pc_sp :
  arm_inst -> int -> int -> coq_TableCache -> int list -> (int -> int) -> int
  -> int -> int -> int -> coq_NewInst

val rewrite_pc_no_jump :
  arm_inst -> int -> int -> int -> coq_TableCache -> coq_NewInst

val rewrite_pc_sp_no_jump :
  arm_inst -> int -> int -> int -> int -> coq_TableCache -> coq_NewInst

val canonical_z : int -> int -> int

val rewrite_b_bl :
  bool -> int -> int -> int -> int list -> (int -> int) -> int ->
  coq_TableCache -> coq_NewInst

val rewrite_b :
  int -> int -> int -> int list -> (int -> int) -> int -> coq_TableCache ->
  coq_NewInst

val rewrite_bl :
  int -> int -> int -> int list -> (int -> int) -> int -> coq_TableCache ->
  coq_NewInst

val rewrite_mov_lr_pc :
  int -> int -> (int -> int) -> coq_TableCache -> coq_NewInst

val _unused_reg : int -> int -> int -> int -> int

val unused_reg : int -> int -> int -> int

val unused_reg_high : int -> int -> int -> int

val goto_abort : int -> int -> coq_TableCache -> coq_NewInst

val rewrite_inst :
  coq_TableCache -> (int -> int) -> int -> int list -> int -> int -> int ->
  int -> int list -> coq_NewInst

val _rewrite :
  int list -> coq_TableCache -> (int -> int list) -> (int -> int) -> int ->
  int -> int -> int -> int list -> ((int list list * int list
  list) * coq_TableCache) option

val make_i's : int list list -> int -> int list

val make_i2i' : int list -> int -> int -> int

val rewrite :
  (int -> int list) -> int list -> int -> int -> int -> int -> ((int list
  list * int list list) * coq_TableCache) option
