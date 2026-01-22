open BinNums
open Picinae_armv7_lifter

(** val unique_except_pairs : int list -> int list -> bool **)

let rec unique_except_pairs l l' =
  match l with
  | [] -> true
  | a::t ->
    (match l' with
     | [] -> true
     | a'::t' ->
       if if (List.mem) a (List.append t t')
          then true
          else (List.mem) a' (List.append t t')
       then false
       else unique_except_pairs t t')

(** val apply_hash : int -> int -> int -> int **)

let apply_hash sl sr z =
  (lsr) ((fun x y -> ((x mod y) + y) mod y) ((lsl) z sl) 4294967296) sr

(** val valid_hash : int list -> int list -> int -> int -> bool **)

let valid_hash dis dis' sl sr =
  unique_except_pairs (List.map (apply_hash sl sr) dis)
    (List.map (apply_hash sl sr) dis')

(** val find_sr : int list -> int list -> int -> int -> int option **)

let rec find_sr dis dis' sl sr =
  if (<=) sr 0
  then None
  else if valid_hash dis dis' sl sr
       then Some sr
       else find_sr dis dis' sl ((-) sr 1)

(** val find_hash : int list -> int list -> int -> (int * int) option **)

let rec find_hash dis dis' sl =
  if (<=) sl 2
  then None
  else (match find_sr dis dis' sl 31 with
        | Some z -> Some (sl,z)
        | None -> find_hash dis dis' ((-) sl 1))

(** val make_jump_table_map :
    int list -> int list -> int -> int -> (int -> int) -> int -> int **)

let rec make_jump_table_map dis dis' sl sr f =
  match dis with
  | [] -> f
  | di::t ->
    (match dis' with
     | [] -> f
     | di'::t' ->
       let j = apply_hash sl sr di in
       let k = apply_hash sl sr di' in
       let f' = make_jump_table_map t t' sl sr f in
       (fun x ->
       if if (=) x j then true else (=) x k then ( * ) 4 di' else f' x))

(** val map2list : (int -> int) -> int -> int list **)

let rec map2list m n =
  if (>) n 0 then (m ((-) n 1))::(map2list m ((-) n 1)) else []

(** val make_jump_table :
    int list -> int list -> int -> int -> int -> int -> int list **)

let make_jump_table dis dis' ai sl sr n =
  let m = make_jump_table_map dis dis' sl sr (fun _ -> ( * ) 4 ai) in
  List.rev (map2list m n)

(** val coq_PC : int **)

let coq_PC =
  15

(** val coq_LR : int **)

let coq_LR =
  14

(** val coq_SP : int **)

let coq_SP =
  13

(** val coq_STR : int -> int -> int -> arm_inst **)

let coq_STR rt rn offset =
  let u = if (<) offset 0 then 0 else 1 in
  ARM_ls_i (ARM_STR, 14, 1, u, 0, rn, rt, ((abs) offset))

(** val coq_LDR : int -> int -> int -> arm_inst **)

let coq_LDR rt rn offset =
  let u = if (<) offset 0 then 0 else 1 in
  ARM_ls_i (ARM_LDR, 14, 1, u, 0, rn, rt, ((abs) offset))

(** val coq_MOVW : int -> int -> arm_inst **)

let coq_MOVW rd imm =
  ARM_MOV_WT (true, 14, ((land) ((lsr) imm 12) 15), rd, ((land) imm 4095))

(** val coq_MOVT : int -> int -> arm_inst **)

let coq_MOVT rd imm =
  ARM_MOV_WT (false, 14, ((land) ((lsr) imm 12) 15), rd, ((land) imm 4095))

(** val coq_MOV : int -> int -> arm_inst **)

let coq_MOV rd rm =
  ARM_data_r (ARM_MOV, 14, 0, 0, rd, 0, 0, rm)

(** val coq_LSL : int -> int -> int -> arm_inst **)

let coq_LSL rd rm imm =
  ARM_data_r (ARM_MOV, 14, 0, 0, rd, imm, 0, rm)

(** val coq_STMDB2 : int -> int -> int -> arm_inst **)

let coq_STMDB2 rn r0 r1 =
  ARM_lsm (ARM_STMDB, 14, 0, rn, ((lor) ((lsl) 1 r0) ((lsl) 1 r1)))

(** val coq_LDMDB2 : int -> int -> int -> arm_inst **)

let coq_LDMDB2 rn r0 r1 =
  ARM_lsm (ARM_LDMDB, 14, 0, rn, ((lor) ((lsl) 1 r0) ((lsl) 1 r1)))

(** val coq_STMDB3 : int -> int -> int -> int -> arm_inst **)

let coq_STMDB3 rn r0 r1 r2 =
  ARM_lsm (ARM_STMDB, 14, 0, rn,
    ((lor) ((lor) ((lsl) 1 r0) ((lsl) 1 r1)) ((lsl) 1 r2)))

(** val coq_LDMDB3 : int -> int -> int -> int -> arm_inst **)

let coq_LDMDB3 rn r0 r1 r2 =
  ARM_lsm (ARM_LDMDB, 14, 0, rn,
    ((lor) ((lor) ((lsl) 1 r0) ((lsl) 1 r1)) ((lsl) 1 r2)))

(** val coq_UBFX : int -> int -> int -> int -> arm_inst **)

let coq_UBFX rd rn sl sr =
  ARM_bfx (false, 14, ((-) 31 sr), rd, ((-) sr sl), rn)

(** val coq_GOTO : bool -> int -> int -> int -> arm_inst option **)

let coq_GOTO l cond src dest =
  let offset = (-) ((-) dest src) 2 in
  if if (<) offset ((~-) (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
          (Coq_xO Coq_xH))))))))))))))))))))))))
     then true
     else (>) offset (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
            (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
            (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI (Coq_xI
            Coq_xH))))))))))))))))))))))
  then None
  else let imm = (fun x y -> ((x mod y) + y) mod y) offset ((lsl) 1 24) in
       Some (if l then ARM_BL (cond, imm) else ARM_B (cond, imm))

(** val coq_GOTOz : bool -> int -> int -> int -> int option **)

let coq_GOTOz l cond src dest =
  match coq_GOTO l cond src dest with
  | Some a -> arm_assemble a
  | None -> None

(** val arm_add : int -> int -> arm_inst list **)

let arm_add reg imm =
  let a = fun x -> ARM_data_i (ARM_ADD, 14, 0, reg, reg, x) in
  (a ((lor) ((lsl) 4 8) ((land) ((lsr) imm 24) 0xff)))::((a
                                                           ((lor) ((lsl) 8 8)
                                                             ((land)
                                                               ((lsr) imm 16)
                                                               0xff)))::(
  (a ((lor) ((lsl) 12 8) ((land) ((lsr) imm 8) 0xff)))::((a ((land) imm 0xff))::[])))

(** val arm_table_lookup : int -> int -> int -> int -> arm_inst list **)

let arm_table_lookup ti sl sr reg =
  List.append ((coq_UBFX reg reg ((-) sl 2) sr)::((coq_LSL reg reg 2)::[]))
    (List.append (arm_add reg (( * ) 4 ti)) ((coq_LDR reg reg 0)::[]))

type coq_IRM = int -> int -> int -> int -> int -> int list option

type coq_TableCache = int list -> ((int * int) * int) option

type coq_NewInst = ((int list * int list) * coq_TableCache) option

(** val wo_table : int list option -> coq_TableCache -> coq_NewInst **)

let wo_table z' tc =
  match z' with
  | Some z'0 -> Some ((z'0,[]),tc)
  | None -> None

(** val invert_cond : int -> int **)

let invert_cond cond =
  if (=) ((fun x y -> ((x mod y) + y) mod y) cond 2) 0
  then (+) cond 1
  else (-) cond 1

(** val arm_assemble_all_cond : arm_inst list -> int -> int list option **)

let arm_assemble_all_cond insts cond =
  let jump_after = ARM_B ((invert_cond cond), ((-) ( (List.length insts)) 1))
  in
  if (<) cond 14
  then arm_assemble_all (jump_after::insts)
  else arm_assemble_all insts

(** val list_eqb : int list -> int list -> bool **)

let rec list_eqb l1 l2 =
  match l1 with
  | [] -> (match l2 with
           | [] -> true
           | _::_ -> false)
  | a::b ->
    (match l2 with
     | [] -> false
     | c::d -> if (=) a c then list_eqb b d else false)

(** val rewrite_w_table :
    coq_IRM -> coq_TableCache -> int list -> (int -> int) -> int -> int ->
    int -> int -> coq_NewInst **)

let rewrite_w_table irm tc dis i2i' cond i ti ai =
  match tc dis with
  | Some p ->
    let p0,sr = p in
    let ti0,sl = p0 in
    (match irm cond i ti0 sl sr with
     | Some irm0 -> Some ((irm0,[]),tc)
     | None -> None)
  | None ->
    let dis' = List.map i2i' dis in
    (match find_hash dis dis' 31 with
     | Some p ->
       let sl,sr = p in
       (match irm cond i ti sl sr with
        | Some irm0 ->
          let table = make_jump_table dis dis' ai sl sr ((lsl) 1 ((-) 32 sr))
          in
          let tc' = fun x ->
            if list_eqb x dis then Some ((ti,sl),sr) else tc x
          in
          Some ((irm0,table),tc')
        | None -> None)
     | None -> None)

(** val bx_irm : int -> coq_IRM **)

let bx_irm reg cond _ ti sl sr =
  arm_assemble_all_cond
    (List.append (arm_table_lookup ti sl sr reg) ((ARM_BX (14, reg))::[]))
    cond

(** val rewrite_bx :
    int -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int ->
    int -> coq_NewInst **)

let rewrite_bx reg =
  rewrite_w_table (bx_irm reg)

(** val blx_irm : int -> coq_IRM **)

let blx_irm reg cond _ ti sl sr =
  arm_assemble_all_cond
    (List.append (arm_table_lookup ti sl sr reg) ((ARM_BLX_r (14, reg))::[]))
    cond

(** val rewrite_blx :
    int -> coq_TableCache -> int list -> (int -> int) -> int -> int -> int ->
    int -> coq_NewInst **)

let rewrite_blx reg =
  rewrite_w_table (blx_irm reg)

(** val ldm_pc_irm :
    arm_memm_op -> int -> int -> int -> arm_inst -> coq_IRM **)

let ldm_pc_irm op rn register_list reg orig_inst cond _ ti sl sr =
  let bc =
    ( * ) 4
      ((fun z -> bitb z 0 + bitb z 1 + bitb z 2 + bitb z 3 + bitb z 4 + bitb z 5 + bitb z 6 + bitb z 7 + bitb z 8 + bitb z 9 + bitb z 10 + bitb z 11 + bitb z 12 + bitb z 13 + bitb z 14 + bitb z 15 + bitb z 16 + bitb z 17 + bitb z 18 + bitb z 19 + bitb z 20 + bitb z 21 + bitb z 22 + bitb z 23 + bitb z 24 + bitb z 25 + bitb z 26 + bitb z 27 + bitb z 28 + bitb z 29 + bitb z 30 + bitb z 31)
        register_list)
  in
  let offset = (-) ((+) (arm_lsm_op_start op bc) bc) 4 in
  arm_assemble_all_cond
    (List.append ((coq_STR reg coq_SP (-4))::((coq_LDR reg rn offset)::[]))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_STR reg rn offset)::((coq_LDR reg coq_SP (-4))::(orig_inst::[])))))
    cond

(** val rewrite_ldm_pc :
    arm_memm_op -> int -> int -> int -> arm_inst -> coq_TableCache -> int
    list -> (int -> int) -> int -> int -> int -> int -> coq_NewInst **)

let rewrite_ldm_pc op rn register_list reg orig_inst =
  rewrite_w_table (ldm_pc_irm op rn register_list reg orig_inst)

(** val pc_irm : arm_inst -> int -> coq_IRM **)

let pc_irm sanitized_inst reg cond i ti sl sr =
  let a = (+) (( * ) 4 i) 8 in
  arm_assemble_all_cond
    (List.append
      ((coq_STR reg coq_SP (-4))::((coq_MOVW reg ((land) a 0xffff))::(
      (coq_MOVT reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::[]))))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_STR reg coq_SP (-8))::((coq_LDR reg coq_SP (-4))::((coq_LDR
                                                                   coq_PC
                                                                   coq_SP
                                                                   (-8))::[])))))
    cond

(** val pc_sp_irm : arm_inst -> int -> int -> coq_IRM **)

let pc_sp_irm sanitized_inst reg reg2 cond i ti sl sr =
  let a = (+) (( * ) 4 i) 8 in
  arm_assemble_all_cond
    (List.append
      ((coq_STMDB3 coq_SP reg reg2 coq_PC)::((coq_MOV reg2 coq_SP)::(
      (coq_MOVW reg ((land) a 0xffff))::((coq_MOVT reg
                                           ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::[])))))
      (List.append (arm_table_lookup ti sl sr reg)
        ((coq_STR reg reg2 (-4))::((coq_LDMDB3 reg2 reg reg2 coq_PC)::[]))))
    cond

(** val rewrite_pc :
    arm_inst -> int -> coq_TableCache -> int list -> (int -> int) -> int ->
    int -> int -> int -> coq_NewInst **)

let rewrite_pc sanitized_inst reg =
  rewrite_w_table (pc_irm sanitized_inst reg)

(** val rewrite_pc_sp :
    arm_inst -> int -> int -> coq_TableCache -> int list -> (int -> int) ->
    int -> int -> int -> int -> coq_NewInst **)

let rewrite_pc_sp sanitized_inst reg reg2 =
  rewrite_w_table (pc_sp_irm sanitized_inst reg reg2)

(** val rewrite_pc_no_jump :
    arm_inst -> int -> int -> int -> coq_TableCache -> coq_NewInst **)

let rewrite_pc_no_jump sanitized_inst cond i reg tc =
  let a = (+) (( * ) 4 i) 8 in
  wo_table
    (arm_assemble_all_cond
      ((coq_STR reg coq_SP (-4))::((coq_MOVW reg ((land) a 0xffff))::(
      (coq_MOVT reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::(
      (coq_LDR reg coq_SP (-4))::[]))))) cond) tc

(** val rewrite_pc_sp_no_jump :
    arm_inst -> int -> int -> int -> int -> coq_TableCache -> coq_NewInst **)

let rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc =
  let a = (+) (( * ) 4 i) 8 in
  wo_table
    (arm_assemble_all_cond
      ((coq_STMDB2 coq_SP reg reg2)::((coq_MOV reg2 coq_SP)::((coq_MOVW reg
                                                                ((land) a
                                                                  0xffff))::(
      (coq_MOVT reg ((land) ((lsr) a 16) 0xffff))::(sanitized_inst::(
      (coq_LDMDB2 reg2 reg reg2)::[])))))) cond) tc

(** val canonical_z : int -> int -> int **)

let canonical_z w z =
  (-)
    ((fun x y -> ((x mod y) + y) mod y) ((+) z ((lsl) 1 ((-) w 1)))
      ((lsl) 1 w)) ((lsl) 1 ((-) w 1))

(** val rewrite_b_bl :
    bool -> int -> int -> int -> int list -> (int -> int) -> int ->
    coq_TableCache -> coq_NewInst **)

let rewrite_b_bl l cond imm24 i dis i2i' ai tc =
  let j =
    (fun x y -> ((x mod y) + y) mod y) ((+) ((+) i 2) (canonical_z 24 imm24))
      ((lsl) 1 30)
  in
  let dst = if (List.mem) j dis then i2i' j else ai in
  (match coq_GOTOz l cond (i2i' i) dst with
   | Some z -> Some (((z::[]),[]),tc)
   | None ->
     (match coq_GOTOz l cond (i2i' i) ai with
      | Some z -> Some (((z::[]),[]),tc)
      | None -> None))

(** val rewrite_b :
    int -> int -> int -> int list -> (int -> int) -> int -> coq_TableCache ->
    coq_NewInst **)

let rewrite_b =
  rewrite_b_bl false

(** val rewrite_bl :
    int -> int -> int -> int list -> (int -> int) -> int -> coq_TableCache ->
    coq_NewInst **)

let rewrite_bl =
  rewrite_b_bl true

(** val rewrite_mov_lr_pc :
    int -> int -> (int -> int) -> coq_TableCache -> coq_NewInst **)

let rewrite_mov_lr_pc cond i i2i' tc =
  let pc' = ( * ) 4 (i2i' ((+) i 2)) in
  wo_table
    (arm_assemble_all_cond
      ((coq_MOVW coq_LR ((land) pc' 0xffff))::((coq_MOVT coq_LR
                                                 ((land) ((lsr) pc' 16)
                                                   0xffff))::[])) cond) tc

(** val _unused_reg : int -> int -> int -> int -> int **)

let _unused_reg base r0 r1 r2 =
  if if if (=) r0 base then true else (=) r1 base then true else (=) r2 base
  then if if if (=) r0 ((+) base 1) then true else (=) r1 ((+) base 1)
          then true
          else (=) r2 ((+) base 1)
       then if if if (=) r0 ((+) base 2) then true else (=) r1 ((+) base 2)
               then true
               else (=) r2 ((+) base 2)
            then (+) base 3
            else (+) base 2
       else (+) base 1
  else base

(** val unused_reg : int -> int -> int -> int **)

let unused_reg =
  _unused_reg 0

(** val unused_reg_high : int -> int -> int -> int **)

let unused_reg_high =
  _unused_reg 4

(** val goto_abort : int -> int -> coq_TableCache -> coq_NewInst **)

let goto_abort i' ai tc =
  match coq_GOTOz true 14 i' ai with
  | Some z -> Some (((z::[]),[]),tc)
  | None -> None

(** val rewrite_inst :
    coq_TableCache -> (int -> int) -> int -> int list -> int -> int -> int ->
    int -> int list -> coq_NewInst **)

let rewrite_inst tc i2i' z dis i ti ai bi txt =
  let unchanged = Some (((z::[]),[]),tc) in
  let abort = goto_abort (i2i' i) ai tc in
  let decoded = arm_decode z in
  if (not) ((List.mem) ((+) i 1) dis)
  then None
  else (match decoded with
        | ARM_UNDEFINED -> abort
        | ARM_UNPREDICTABLE -> abort
        | Coq_idk -> abort
        | ARM_data_r (op, cond, s, rn, rd, imm5, type0, rm) ->
          let reg = unused_reg rn rd rm in
          let reg2 = unused_reg_high rn rd rm in
          let rn' = if (=) rn coq_PC then reg else rn in
          let rd' = if (=) rd coq_PC then reg else rd in
          let rm' = if (=) rm coq_PC then reg else rm in
          let sanitized_inst = ARM_data_r (op, 14, s, rn', rd', imm5, type0,
            rm')
          in
          if (=) rd coq_PC
          then rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
          else if if (=) rn coq_PC then true else (=) rm coq_PC
               then if match op with
                       | ARM_MOV -> (=) rd coq_LR
                       | _ -> false
                    then rewrite_mov_lr_pc cond i i2i' tc
                    else if (=) rd coq_SP
                         then rewrite_pc_sp_no_jump sanitized_inst cond i reg
                                reg2 tc
                         else rewrite_pc_no_jump sanitized_inst cond i reg tc
               else unchanged
        | ARM_data_rsr (_, _, _, _, _, _, _, _) -> abort
        | ARM_data_i (op, cond, s, rn, rd, imm12) ->
          let reg = unused_reg rn rd 0 in
          let reg2 = unused_reg_high rn rd 0 in
          let rn' = if (=) rn coq_PC then reg else rn in
          let rd' = if (=) rd coq_PC then reg else rd in
          let sanitized_inst = ARM_data_i (op, 14, s, rn', rd', imm12) in
          if (=) rd coq_PC
          then rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
          else if (=) rn coq_PC
               then if (=) rd coq_SP
                    then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2
                           tc
                    else rewrite_pc_no_jump sanitized_inst cond i reg tc
               else unchanged
        | ARM_BX (cond, reg) -> rewrite_bx reg tc dis i2i' cond i ti ai
        | ARM_BLX_r (cond, reg) -> rewrite_blx reg tc dis i2i' cond i ti ai
        | ARM_BXJ (_, _) -> abort
        | ARM_BKPT (_, _, _) -> abort
        | ARM_extra_ls_i (op, cond, p, u, w, rn, rt, imm4H, imm4L) ->
          let reg = if (=) rt 0 then 1 else 0 in
          let reg2 = if (=) rt 2 then 3 else 2 in
          let sanitized_inst = ARM_extra_ls_i (op, cond, p, u, w, reg, rt,
            imm4H, imm4L)
          in
          if (=) rn coq_PC
          then if match op with
                  | ARM_STRH -> false
                  | ARM_STRD -> false
                  | _ -> (=) rt coq_SP
               then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
               else rewrite_pc_no_jump sanitized_inst cond i reg tc
          else unchanged
        | ARM_extra_ls_r (op, cond, p, u, w, rn, rt, rm) ->
          let reg = if (=) rt 0 then 1 else 0 in
          let reg2 = if (=) rt 2 then 3 else 2 in
          let sanitized_inst = ARM_extra_ls_r (op, cond, p, u, w, reg, rt, rm)
          in
          if (=) rn coq_PC
          then if match op with
                  | ARM_STRH -> false
                  | ARM_STRD -> false
                  | _ -> (=) rt coq_SP
               then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
               else rewrite_pc_no_jump sanitized_inst cond i reg tc
          else unchanged
        | ARM_ls_i (op, cond, p, u, w, rn, rt, imm12) ->
          (match op with
           | ARM_LDR ->
             let reg = unused_reg rn rt 0 in
             let reg2 = unused_reg_high rn rt 0 in
             let rn' = if (=) rn coq_PC then reg else rn in
             let rt' = if (=) rt coq_PC then reg else rt in
             let sanitized_inst = ARM_ls_i (ARM_LDR, cond, p, u, w, rn', rt',
               imm12)
             in
             if (=) rt coq_PC
             then if if (=) rn coq_SP
                     then if (=) p 0 then true else (=) w 1
                     else false
                  then rewrite_pc_sp sanitized_inst reg reg2 tc dis i2i' cond
                         i ti ai
                  else rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
             else if (=) rn coq_PC
                  then let li =
                         (-) bi
                           ((fun x y -> ((x mod y) + y) mod y)
                             (if (=) u 1
                              then (+) ((+) i 2) imm12
                              else (-) ((+) i 2) imm12) ((lsl) 1 32))
                       in
                       if (>) li 0
                       then (match (List.nth_opt) txt ( ((-) bi li)) with
                             | Some lv ->
                               wo_table
                                 (arm_assemble_all_cond
                                   ((coq_MOVW rt ((land) lv 0xffff))::(
                                   (coq_MOVT rt ((land) ((lsr) lv 16) 0xffff))::[]))
                                   cond) tc
                             | None ->
                               if (=) rt coq_SP
                               then rewrite_pc_sp_no_jump sanitized_inst cond
                                      i reg reg2 tc
                               else rewrite_pc_no_jump sanitized_inst cond i
                                      reg tc)
                       else if (=) rt coq_SP
                            then rewrite_pc_sp_no_jump sanitized_inst cond i
                                   reg reg2 tc
                            else rewrite_pc_no_jump sanitized_inst cond i reg
                                   tc
                  else unchanged
           | _ -> unchanged)
        | ARM_ls_r (op, cond, p, u, w, rn, rt, imm5, type0, rm) ->
          (match op with
           | ARM_LDR ->
             let reg = unused_reg rn rt rm in
             let reg2 = unused_reg_high rn rt rm in
             let rn' = if (=) rn coq_PC then reg else rn in
             let rt' = if (=) rt coq_PC then reg else rt in
             let rm' = if (=) rm coq_PC then reg else rm in
             let sanitized_inst = ARM_ls_r (ARM_LDR, cond, p, u, w, rn', rt',
               imm5, type0, rm')
             in
             if (=) rt coq_PC
             then if if (=) rn coq_SP
                     then if (=) p 0 then true else (=) w 1
                     else false
                  then rewrite_pc_sp sanitized_inst reg reg2 tc dis i2i' cond
                         i ti ai
                  else rewrite_pc sanitized_inst reg tc dis i2i' cond i ti ai
             else if if (=) rn coq_PC then true else (=) rm coq_PC
                  then if (=) rt coq_SP
                       then rewrite_pc_sp_no_jump sanitized_inst cond i reg
                              reg2 tc
                       else rewrite_pc_no_jump sanitized_inst cond i reg tc
                  else unchanged
           | _ -> unchanged)
        | ARM_bfx (_, _, _, _, _, _) -> abort
        | ARM_lsm (op, cond, _, rn, register_list) ->
          if (<) register_list ((lsl) 1 15)
          then unchanged
          else let reg = if (=) rn 0 then 1 else 0 in
               rewrite_ldm_pc op rn register_list reg decoded tc dis i2i'
                 cond i ti ai
        | ARM_B (cond, imm24) -> rewrite_b cond imm24 i dis i2i' ai tc
        | ARM_BL (cond, imm24) -> rewrite_bl cond imm24 i dis i2i' ai tc
        | ARM_BLX_i (_, _) -> abort
        | ARM_vls (is_load, is_single, cond, u, d, rn, vd, imm8) ->
          if (=) rn coq_PC
          then let sanitized_inst = ARM_vls (is_load, is_single, cond, u, d,
                 0, vd, imm8)
               in
               rewrite_pc_no_jump sanitized_inst cond i 0 tc
          else unchanged
        | _ -> unchanged)

(** val _rewrite :
    int list -> coq_TableCache -> (int -> int list) -> (int -> int) -> int ->
    int -> int -> int -> int list -> ((int list list * int list
    list) * coq_TableCache) option **)

let rec _rewrite zs tc pol i2i' i ti ai bi txt =
  match zs with
  | [] -> Some (([],[]),tc)
  | z::zs0 ->
    (match rewrite_inst tc i2i' z (pol i) i ti ai bi txt with
     | Some p ->
       let p0,tc' = p in
       let z',table = p0 in
       let ti' = (+) ti ( (List.length table)) in
       (match _rewrite zs0 tc' pol i2i' ((+) i 1) ti' ai bi txt with
        | Some p1 ->
          let p2,tc_t = p1 in
          let z_t,table_t = p2 in Some (((z'::z_t),(table::table_t)),tc_t)
        | None -> None)
     | None -> None)

(** val make_i's : int list list -> int -> int list **)

let make_i's z's i' =
  let lens = List.map (fun x ->  (List.length x)) z's in
  List.rev
    (snd
      ((fun f l a -> List.fold_left f a l) (fun a b ->
        let sum = (+) (fst a) b in sum,(((+) i' (fst a))::(snd a))) lens
        (0,[])))

(** val make_i2i' : int list -> int -> int -> int **)

let make_i2i' i's i =
  let ie = (+) i ( (List.length i's)) in
  let arr = Array.of_list i's in
  (fun x ->
  if if (<) x i then true else (>=) x ie then x else Array.get arr ((-) x i))

(** val rewrite :
    (int -> int list) -> int list -> int -> int -> int -> int -> ((int list
    list * int list list) * coq_TableCache) option **)

let rewrite pol zs i i' ti ai =
  let tc = fun _ -> None in
  (match _rewrite zs tc pol (Obj.magic Fun.id) i ti ai i zs with
   | Some p ->
     let p0,_ = p in
     let z's,_ = p0 in
     let i's = make_i's z's i' in
     let i2i' = make_i2i' i's i in _rewrite zs tc pol i2i' i ti ai i zs
   | None -> None)
