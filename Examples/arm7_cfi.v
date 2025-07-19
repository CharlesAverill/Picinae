Require Export Picinae_armv7_lifter.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
From Coq Require Recdef.
Require Import Lia.
Import ListNotations.
Open Scope Z.

Definition Z_4 := -4.
Definition Z_8 := -8.
Definition Z_32 := -32.
Definition Z0xff := 0xff.
Definition Z0xffff := 0xffff.
Definition Z0xffff_0000 := 0xfff0_0000.
Definition Z32767 := 32767.
Definition Z1245169 := 1245169.
Definition Z1245171 := 1245171.
Definition Z33554428 := 33554428.
Definition Z_33554432 := -33554432.
Definition Z4294967296 := 4294967296.

Definition Z_popcount z := match z with Z0 => Z0 | Z.pos p => Z.pos (Pos_popcount p) | _ => Z0 end.

(* checks if l contains z *)
Definition contains (z: Z) (l: list Z) : bool :=
  match find (Z.eqb z) l with
  | Some _ => true
  | None => false
  end.

(* checks if all elements in the two lists are unique, but allows the two elements at the same index in l and l' to be the same *)
Fixpoint unique_except_pairs (l l': list Z) : bool :=
  match l, l' with
  | a::t, a'::t'=> if contains a (t++t') || contains a' (t++t') then false else unique_except_pairs t t'
  | _, _ => true
  end.

(* H(x) = (x LSL sl) LSR sr *)
Definition apply_hash (sl sr: Z) (z: Z) : Z :=
  Z.shiftr ((Z.shiftl z sl) mod (Z4294967296)) sr.

(* checks if the hash produces no unacceptable collisions
   a - list of old addresses
   o - offset from new code to old code
   sl sr - hash parameters *)
Definition valid_hash (a: list Z) (o sl sr: Z) : bool :=
  unique_except_pairs (map (apply_hash sl sr) a) (map (apply_hash sl sr) (map (Z.add o) a)).

Function find_sr (a: list Z) (o sl sr: Z) {measure Z.to_nat sr}: option Z :=
  match Z.to_nat sr with
  | O => None
  | _ => if valid_hash a o sl sr then Some sr else find_sr a o sl (sr-Z1)
  end.
Proof. unfold Z1 in *. lia. Qed.

(* find hash parameters, returns (sl, sr)
   a - list of old addresses
   o - offset from new code to old code *)
Function find_hash (a: list Z) (o sl: Z) {measure Z.to_nat sl}: option (Z * Z) :=
  match Z.to_nat sl with
  | O => None
  | _ => match find_sr a o sl Z31 with
         | Some sr => Some (sl, sr)
         | None => find_hash a o (sl-Z1)
         end
  end.
Proof. unfold Z1 in *. lia. Qed.

(* make a function that maps table index to the value in the table at that index
   addrs - list of old addresses
   o - offset from new code to old code
   sl, sr - from find_hash
   f - default value (fun _ -> aabort) *)
Fixpoint make_jump_table_map (addrs: list Z) (o sl sr: Z) (f: Z -> Z) : Z -> Z :=
  match addrs with
  | nil => f
  | a::t =>
      let j := apply_hash sl sr a in
      let k := apply_hash sl sr (a+o) in
      (* quick hack *)
      if a >=? Z0xffff_0000 then make_jump_table_map t o sl sr (fun i => if (i =? j) then a else f i)
      else make_jump_table_map t o sl sr (fun i => if (i =? j) || (i =? k) then a + o else f i)
  end.


Function _make_jump_table (m: Z -> Z) (n i: Z) {measure (fun i => Z.to_nat (n - i)) i} :=
  match Z.to_nat (n - i - Z1) with
  | O => m i::nil
  | _ => m i::_make_jump_table m n (i+Z1)
  end.
Proof. intros. unfold Z1 in *. lia. Qed.
Fixpoint all_div_4 l :=
  match l with
  | nil => true
  | a::t => if a mod Z4 =? Z0 then all_div_4 t else false
  end.
Definition make_jump_table (addrs: list Z) (aabort o sl sr n: Z) : option (list Z) :=
  if (all_div_4 (o::aabort::addrs)) then
    let m := make_jump_table_map addrs o sl sr (fun _ => aabort) in
    Some (_make_jump_table m n Z0)
  else
    None.
Definition id := Z.

Definition PC := Z15.
Definition LR := Z14.
Definition SP := Z13.
Definition STR rt rn offset :=
  let U := if offset <? Z0 then Z0 else Z1 in
  ARM_ls_i ARM_STR Z14 Z1 U Z0 rn rt (Z.abs offset).
Definition LDR rt rn offset :=
  let U := if offset <? Z0 then Z0 else Z1 in
  ARM_ls_i ARM_LDR Z14 Z1 U Z0 rn rt (Z.abs offset).
Definition MOVW rd imm :=
  ARM_MOV_WT true Z14 ((imm >> Z12) & Z15) rd (imm & Z4095).
Definition MOVT rd imm :=
  ARM_MOV_WT false Z14 ((imm >> Z12) & Z15) rd (imm & Z4095).
Definition LSL rd rm imm :=
  ARM_data_r ARM_MOV Z14 Z0 Z0 rd imm Z0 rm.
Definition LSR rd rm imm :=
  ARM_data_r ARM_MOV Z14 Z0 Z0 rd imm Z1 rm.
(* branch to a specific address
   l - link when branching
   cond - branch condition
   src - address where the branch will be placed
   dest - destination address *)
Definition GOTO (l: bool) (cond src dest: Z) :=
  let offset := dest - src - Z8 in
  let imm := offset mod (Z1 << Z26) in
  if (offset <? Z_33554432) || (offset >? Z33554428) || negb (offset mod Z4 =? Z0) then ARM_UNPREDICTABLE
  else ((if l then ARM_BL else ARM_B) cond (imm >> Z2)).

(* add an arbitrary immediate value to a register

   arm's add instruction can only add an immediate that is single byte with a rotation applied to it,
   so adding an arbitrary constant can take up to 4 add instructions *)
Definition arm_add (reg imm: Z) : list arm_inst :=
  let i := ARM_data_i ARM_ADD Z14 Z0 reg reg in
  let a := if (imm >> Z24) & Z0xff =? Z0 then nil else
    i ((Z4 << Z8) .| ((imm >> Z24) & Z0xff))::nil in
  let b := if (imm >> Z16) & Z0xff =? Z0 then a else
    i ((Z8 << Z8) .| ((imm >> Z16) & Z0xff))::a in
  let c := if (imm >> Z8) & Z0xff =? Z0 then b else
    i ((Z12 << Z8) .| ((imm >> Z8) & Z0xff))::b in
  if imm & Z0xff =? Z0 then c else
    i (imm & Z0xff)::c.
(* reg = table[H(reg)] *)
Definition arm_table_lookup atable sl sr reg :=
  [ LSL reg reg sl;        (* lsl reg, reg, #sl *)
    LSR reg reg sr;        (* lsr reg, reg, #sr *)
    LSL reg reg Z2         (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[ (* add reg, reg, #atable *)
    LDR reg reg Z0         (* ldr reg, [reg] *)
  ].


(* rewrite a dynamic jump, returns (new inst encoding, code to put in .dyn, table to put in .table, new table cache function)
   dyn_code - function that takes (n a atable sl sr) and returns the code to be placed in .dyn
   l - link when branching to .dyn
   cond - condition to use for the branch to .dyn
   oid - id of the valid destination addresses
   label - maps ids to lists of addresses
   n - instruction encoding
   a - address of the instruction in the old code
   a' - address of the instruction in the new code
   adyn - address of the next free spot in .dyn
   atable - address of the next free spot in .table
   aabort - address of the abort handler
   table_cache - used to check if an id already has a table *)
Definition rewrite_dyn (dyn_code: Z -> Z -> Z -> Z -> Z -> option (list Z)) (l: bool) (cond: Z) (n: Z) (oid: Z) (label: id -> list Z) (a a' adyn atable aabort: Z) (table_cache: id -> option (Z * Z * Z)) :=
  match arm_assemble (GOTO l cond a' adyn) with
  | None => None
  | Some n' =>
      match table_cache oid with
      | None =>
          match find_hash (label oid) (a' - a) Z31 with
          | None => None
          | Some (sl, sr) =>
              match dyn_code n a atable sl sr with
              | None => None
              | Some dyn =>
                  match make_jump_table (label oid) aabort (a' - a) sl sr (Z.shiftl Z1 (Z32 - sr)) with
                  | None => None
                  | Some table =>
                      let table_cache' := fun x => if x =? oid then Some (atable, sl, sr) else table_cache x in
                      Some (n', dyn, table, table_cache')
                  end
              end
          end
      | Some (cached_table, sl, sr) =>
          match dyn_code n a cached_table sl sr with
          | None => None
          | Some dyn => Some (n', dyn, nil, table_cache)
          end
      end
  end.

(* check a blx reg or a bx reg
   reg - register that holds the destination address *)
Definition checked_b_reg (reg _ _ atable sl sr: Z) : option (list Z) :=
  arm_assemble_all (
    STR PC SP Z_32::                  (* DEBUG: str pc, [sp, #-32] *)
    arm_table_lookup atable sl sr reg++  (* reg = table[H(reg)] *)
    ARM_BX Z14 reg::nil                  (* bx reg *)
  ).
Definition rewrite_b_reg (l: bool) (reg: Z) := rewrite_dyn (checked_b_reg reg) l.

Definition checked_ldm_pc op (Rn register_list reg n _ atable sl sr: Z) :=
  let bc := Z4 * Z_popcount register_list in
  let offset := arm_lsm_op_start op bc + bc - Z4 in
  arm_assemble_all ([
    STR PC SP Z_32;                         (* DEBUG: str pc, [sp, #-32] *)
    STR reg SP Z_4;                         (* str reg, [sp, #-4] *)
    LDR reg Rn offset                       (* ldr reg, [Rn, #pc_offset] *)
  ]++arm_table_lookup atable sl sr reg++[   (* reg = table[H(reg)] *)
    STR reg Rn offset;                      (* str reg, [Rn, #pc_offset] *)
    LDR reg SP Z_4;                         (* ldr reg, [sp, #-4] *)
    arm_decode n                            (* original inst *)
  ]).
Definition rewrite_ldm_pc op Rn register_list reg := rewrite_dyn (checked_ldm_pc op Rn register_list reg) false.

(* pick a register that is different than the given ones *)
Definition pick_good_reg (r0 r1 r2: Z) :=
  if (r0 =? Z0) || (r1 =? Z0) || (r2 =? Z0) then
    if (r0 =? Z1) || (r1 =? Z1) || (r2 =? Z1) then
      if (r0 =? Z2) || (r1 =? Z2) || (r2 =? Z2) then Z3
      else Z2
    else Z1
  else Z0.
(* check a pc data inst
   reg - register to use as a scratch register *)
Definition checked_pc_data sanitized_inst (reg stack_offset n a atable sl sr: Z) : option (list Z) :=
  let a := a + Z8 in
  arm_assemble_all ([
    STR   PC  SP Z_32;                     (* DEBUG: str pc, [sp, #-32] *)
    STR   reg SP Z_4;                      (* str reg, [sp, #-4] *)
    MOVW  reg (a & Z0xffff);               (* movw reg, #a[16:0] *)
    MOVT  reg ((a >> Z16) & Z0xffff);      (* movt reg, #a[32:16] *)
    sanitized_inst                         (* sanitized_inst *)
  ]++arm_table_lookup atable sl sr reg++[  (* reg = table[H(reg)] *)
    STR   reg SP (Z_8-stack_offset);       (* str reg, [sp, #-8 - stack offset] *)
    LDR   reg SP (Z_4-stack_offset);       (* ldr reg, [sp, #-4 - stack offset] *)
    LDR   PC  SP (Z_8-stack_offset)        (* ldr pc, [sp, #-8 - stack offset] *)
  ]).

Definition rewrite_pc_data sanitized_inst (reg stack_offset: Z) := rewrite_dyn (checked_pc_data sanitized_inst reg stack_offset) false.
(* rewrite a pc data inst that does not affect control flow *)
Definition rewrite_pc_data_no_jump sanitized_inst (reg stack_offset: Z) (cond: Z) (n: Z) (a a' adyn atable aabort: Z) (table_cache: id -> option (Z * Z * Z)) : option (Z * list Z * list Z * (id -> option (Z * Z * Z))) :=
  let a := a + Z8 in
  match arm_assemble (GOTO false cond a' adyn) with
  | Some n' =>
      match arm_assemble_all ([
        STR reg SP Z_4;                    (* str reg, [sp, #-4] *)
        MOVW reg (a & Z0xffff);            (* movw reg, #a[16:0] *)
        MOVT reg ((a >> Z16) & Z0xffff);   (* movt reg, #a[32:16] *)
        sanitized_inst;                    (* santitized_inst *)
        LDR reg SP (Z_4-stack_offset);     (* ldr reg, [sp, #-4 - stack offset] *)
        GOTO false Z14 (adyn+Z20) (a'+Z4)  (* b a'+4 *)
      ]) with
      | Some dyn => Some (n', dyn, nil, table_cache)
      | None => None
      end
  | None => None
  end.

Definition goto_abort a' aabort table_cache : option (Z * list Z * list Z * (id -> option (Z * Z * Z))):=
  match arm_assemble (GOTO true Z14 a' (aabort+Z0xffff+Z1)) with (* DEBUG: use a separate abort handler for this case *)
  | None => None
  | Some n' => Some (n', nil, nil, table_cache)
  end.

(* rewrite a single instruction, see rewrite_dyn for signature *)
Definition rewrite_inst (n: Z) (oid: id) (label: id -> list Z) (a a' adyn atable aabort: Z) (table_cache: id -> option (Z * Z * Z)): option (Z * list Z * list Z * (id -> option (Z * Z * Z))) :=
  let unchanged := Some (n, nil, nil, table_cache) in
  let abort := goto_abort a' aabort table_cache in
  match arm_decode n with
  | ARM_BLX_r cond reg => rewrite_b_reg true reg cond n oid label a a' adyn atable aabort table_cache
  | ARM_BX cond reg => rewrite_b_reg false reg cond n oid label a a' adyn atable aabort table_cache

  | ARM_B cond imm24
  | ARM_BL cond imm24 =>
      unchanged

  | ARM_BLX_i _ _ => abort (* thumb mode not supported *)
  | ARM_data_r op cond s Rn Rd imm5 type Rm =>
      let reg := pick_good_reg Rn Rd Rm in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rd' := if (Rd =? PC) then reg else Rd in
      let Rm' := if (Rm =? PC) then reg else Rm in
      let sanitized_inst := ARM_data_r op Z14 s Rn' Rd' imm5 type Rm' in
      if (Rd =? PC) then
        rewrite_pc_data sanitized_inst reg Z0 cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? PC) || (Rm =? PC) then
        if (match op with ARM_MOV => Rd =? LR | _ => false end) then
          unchanged (* "mov lr, pc" should use new pc, not old pc *)
          (* it's possible that the old pc should be used, if lr is later used as a data memory address,
             but a compiler would most likely pick a general register instead of lr if that was the case

             although any rewritten jump would be able to handle the old pc value correctly, this inst
             is sometimes used when calling a kernel user helper function, which we cannot rewrite *)
        else
          rewrite_pc_data_no_jump sanitized_inst reg Z0 cond n a a' adyn atable aabort table_cache
      else unchanged
  | ARM_data_rsr _ _ _ _ _ _ _ _ => unchanged
  | ARM_data_i op cond s Rn Rd imm12 =>
      let reg := pick_good_reg Rn Rd Z0 in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rd' := if (Rd =? PC) then reg else Rd in
      let sanitized_inst := ARM_data_i op Z14 s Rn' Rd' imm12 in
      if (Rd =? PC) then
        rewrite_pc_data sanitized_inst reg Z0 cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? PC) then
        rewrite_pc_data_no_jump sanitized_inst reg Z0 cond n a a' adyn atable aabort table_cache
      else unchanged
  | ARM_ls_i ARM_LDR cond P U W Rn Rt imm12 =>
      let reg := pick_good_reg Rn Rt Z0 in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rt' := if (Rt =? PC) then reg else Rt in
      let sanitized_inst := ARM_ls_i ARM_LDR cond P U W Rn' Rt' imm12 in
      let stack_offset := if (Rn =? SP) && ((P =? Z0) || (W =? Z1)) then if (U =? Z1) then imm12 else -imm12 else Z0 in
      if (Rt =? PC) then
        rewrite_pc_data sanitized_inst reg stack_offset cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? PC) then
        rewrite_pc_data_no_jump sanitized_inst reg stack_offset cond n a a' adyn atable aabort table_cache
      else unchanged
  | ARM_ls_i _ _ _ _ _ _ _ _ => unchanged
  | ARM_ls_r ARM_LDR cond P U W Rn Rt imm5 type Rm =>
      let reg := pick_good_reg Rn Rt Rm in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rt' := if (Rt =? PC) then reg else Rt in
      let Rm' := if (Rm =? PC) then reg else Rm in
      let sanitized_inst := ARM_ls_r ARM_LDR cond P U W Rn' Rt' imm5 type Rm' in
      let stack_offset := Z0 in (*?*)
      if (Rt =? PC) then
        rewrite_pc_data sanitized_inst reg stack_offset cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? PC) || (Rm =? PC) then
        rewrite_pc_data_no_jump sanitized_inst reg stack_offset cond n a a' adyn atable aabort table_cache
      else unchanged
  | ARM_ls_r _ _ _ _ _ _ _ _ _ _ => unchanged

  | ARM_lsm op cond W Rn register_list =>
      if (register_list <=? Z32767) then unchanged (* pc is not in reg list *)
      else
        let reg := if (Rn =? Z0) then Z1 else Z0 in
        rewrite_ldm_pc op Rn register_list reg cond n oid label a a' adyn atable aabort table_cache

  | ARM_vls is_load is_single cond U D Rn Vd imm8 =>
      if (Rn =? PC) then
        let reg := Z0 in
        let sanitized_inst := ARM_vls is_load is_single cond U D reg Vd imm8 in
        rewrite_pc_data_no_jump sanitized_inst reg Z0 cond n a a' adyn atable aabort table_cache
      else unchanged

  | ARM_sync_l _ _ _ _
  | ARM_sync_s _ _ _ _ _
  | ARM_extra_ls_i _ _ _ _ _ _ _ _ _
  | ARM_extra_ls_r _ _ _ _ _ _ _ _
  | ARM_hint _ _
  | ARM_sat _ _ _ _ _
  | ARM_mul _ _ _ _ _ _ _
  | ARM_MOV_WT _ _ _ _ _
  | ARM_CLZ _ _ _
  | ARM_SVC _ _
  | ARM_PLD_r _ _ _ _ _ _
  | ARM_PLD_i _ _ _ _
  | ARM_coproc_m _ _ _ _ _ _ _ _
  | ARM_pas _ _ _ _ _ _ _
  | ARM_rev _ _ _ _
  | ARM_extend _ _ _ _ _ _ _
  | ARM_vlsm _ _ _ _ _ _ _ _ _ _
  | ARM_VMOV_i _ _ _ _ _ _
  | ARM_VMOV_r2 _ _ _ _ _ _ _
  | ARM_VMOV_r1 _ _ _ _ _
  | ARM_VCMP _ _ _ _ _ _ _
  | ARM_VMRS _ _
  | ARM_vfp _ _ _ _ _ _ _ _ _ _
  | ARM_VCVT_ds _ _ _ _ _ _
  | ARM_VCVT_fpi _ _ _ _ _ _ _ _
  | ARM_VCVT_fpf _ _ _ _ _ _ _ _ _
  | ARM_vfp_other _ _ _ _ _ _ _
      => unchanged

  (* don't allow any other instructions *)
  | _ => goto_abort a' aabort table_cache
  end.

(* rewrite a program, returns (.newtext, .dyn, .jtable) or None if rewrite failed
   table_cache - maps ids to table addresses so tables can be shared across multiple jumps
   pol - maps original addresses to the id of valid destination addresses
   label - maps ids to lists of addresses
   ns - list of instruction encodings of the program
   a - address of the first instruction in ns
   a' - address where the first rewritten instruction should be placed
   adyn - address to place the dynamic jump implementations
   atable - address to place the jump tables
   aabort - address where the abort handler is located *)
Fixpoint _rewrite (table_cache: id -> option (Z * Z * Z)) (pol: Z -> id) (label: id -> list Z) (ns: list Z) (a a' adyn atable aabort: Z) : option (list Z * list (list Z) * list (list Z)) :=
  match ns with
  | nil => Some (nil, nil, nil)
  | n::tail =>
      match rewrite_inst n (pol a) label a a' adyn atable aabort table_cache with
      | None => None
      | Some (n', dyn, table, table_cache') =>
          match _rewrite table_cache' pol label tail (a+Z4) (a'+Z4) (adyn + Z4 * Z.of_nat (length dyn)) (atable + Z4 * Z.of_nat (length table)) aabort with
          | None => None
          | Some (n_t, dyn_t, table_t) => Some (n'::n_t, dyn::dyn_t, table::table_t) end end end.
Definition rewrite := _rewrite (fun _ => None).


Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory "arm_cfi_extraction".
Extract Inductive Z => int [ "0" "" "(~-)" ].
Extract Inductive nat => int [ "0" "" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant id => "int".
Extract Inlined Constant Z0xff => "0xff".
Extract Inlined Constant Z4095 => "4095".
Extract Inlined Constant Z0xffff_0000 => "0xffff_0000".
Extract Inlined Constant Z1 => "1".
Extract Inlined Constant Z2 => "2".
Extract Inlined Constant Z3 => "3".
Extract Inlined Constant Z4 => "4".
Extract Inlined Constant Z5 => "5".
Extract Inlined Constant Z6 => "6".
Extract Inlined Constant Z7 => "7".
Extract Inlined Constant Z8 => "8".
Extract Inlined Constant Z9 => "9".
Extract Inlined Constant Z10 => "10".
Extract Inlined Constant Z11 => "11".
Extract Inlined Constant Z12 => "12".
Extract Inlined Constant Z13 => "13".
Extract Inlined Constant Z14 => "14".
Extract Inlined Constant Z15 => "15".
Extract Inlined Constant Z16 => "16".
Extract Inlined Constant Z17 => "17".
Extract Inlined Constant Z18 => "18".
Extract Inlined Constant Z19 => "19".
Extract Inlined Constant Z20 => "20".
Extract Inlined Constant Z21 => "21".
Extract Inlined Constant Z22 => "22".
Extract Inlined Constant Z23 => "23".
Extract Inlined Constant Z24 => "24".
Extract Inlined Constant Z25 => "25".
Extract Inlined Constant Z26 => "26".
Extract Inlined Constant Z27 => "27".
Extract Inlined Constant Z28 => "28".
Extract Inlined Constant Z29 => "29".
Extract Inlined Constant Z30 => "30".
Extract Inlined Constant Z31 => "31".
Extract Inlined Constant Z32 => "32".
Extract Inlined Constant Z_32 => "(-32)".
Extract Inlined Constant Z_4 => "(-4)".
Extract Inlined Constant Z_8 => "(-8)".
Extract Inlined Constant Z0xffff => "0xffff".
Extract Inlined Constant Z32767 => "32767".
Extract Inlined Constant Z1245169 => "1245169".
Extract Inlined Constant Z1245171 => "1245171".
Extract Inlined Constant Z33554428 => "33554428".
Extract Inlined Constant Z_33554432 => "(-33554432)".
Extract Inlined Constant Z4294967296 => "4294967296".
Extract Inlined Constant Z.opp => "(~-)".
Extract Inlined Constant Z.ltb => "(<)".
(* maybe use library that has popcount instrinsic? *)
Extract Inlined Constant Z_popcount => "(fun z -> bitb z 0 + bitb z 1 + bitb z 2 + bitb z 3 + bitb z 4 + bitb z 5 + bitb z 6 + bitb z 7 + bitb z 8 + bitb z 9 + bitb z 10 + bitb z 11 + bitb z 12 + bitb z 13 + bitb z 14 + bitb z 15 + bitb z 16 + bitb z 17 + bitb z 18 + bitb z 19 + bitb z 20 + bitb z 21 + bitb z 22 + bitb z 23 + bitb z 24 + bitb z 25 + bitb z 26 + bitb z 27 + bitb z 28 + bitb z 29 + bitb z 30 + bitb z 31)".
Extract Inlined Constant Z.abs => "(abs)".
Extract Inlined Constant internal_Z_beq => "(=)".
Extract Inlined Constant Z.gtb => "(>)".
Extract Inlined Constant Z.geb => "(>=)".
Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Nat.sub => "(-)".
Extract Inlined Constant Z.mul => "( * )".
Extract Inlined Constant Z.modulo => "(fun x y -> ((x mod y) + y) mod y)".
Extract Inlined Constant Z.shiftl => "(lsl)".
Extract Inlined Constant Z.shiftr => "(lsr)".
Extract Inlined Constant Z.land => "(land)".
Extract Inlined Constant Z.lor => "(lor)".
Extract Inlined Constant Z.max => "(max)".
Extract Inlined Constant Z.lxor => "(lxor)".
Extract Inlined Constant Z.eqb => "(=)".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant contains => "(List.mem)".
Extract Inlined Constant negb => "(not)".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant combine => "List.combine".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extract Inductive sigT => "( * )"  [ "(,)" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".
Separate Extraction rewrite.


Definition div_4 x := x mod 4 = 0.
Lemma Forall_all_div_4:
  forall l,
    Forall div_4 l <-> all_div_4 l = true.
Proof.
  intros. induction l.
    split; intro.
      reflexivity.
      apply Forall_nil.
    split; intro.
      inversion H; subst. simpl. destruct Z.eqb eqn:e.
        now rewrite <- IHl.
        unfold div_4 in H2. rewrite <- Z.eqb_eq in H2. unfold Z4 in e. now rewrite e in H2.
      unfold all_div_4 in H. destruct Z.eqb eqn:e.
        apply Forall_cons.
          unfold div_4. now rewrite <- Z.eqb_eq.
          now apply IHl.
        discriminate.
Qed.
Lemma make_jump_table_map_div_4:
  forall addrs o sl sr f,
    div_4 o ->
    Forall div_4 addrs ->
    (forall i, div_4 (f i)) ->
    forall i, div_4 (make_jump_table_map addrs o sl sr f i).
Proof.
  induction addrs.
    intros. now simpl.
    intros. simpl. inversion H0. destruct Z.geb.
      apply (IHaddrs _ _ _ _ H H5). intros. now destruct Z.eqb.
      apply (IHaddrs _ _ _ _ H H5). intros. destruct orb.
        unfold div_4. now rewrite <- Zplus_mod_idemp_r, H, Z.add_0_r.
        apply H1.
Qed.
Lemma make_jump_table_div_4:
  forall addrs aabort o sl sr n table,
    make_jump_table addrs aabort o sl sr n = Some table ->
    Forall div_4 table.
Proof.
  intros. unfold make_jump_table in H. destruct all_div_4 eqn:e in H.
    assert (forall i, div_4 (make_jump_table_map addrs o sl sr (fun _ => aabort) i)).
      apply Forall_all_div_4 in e. inversion e. apply make_jump_table_map_div_4; now inversion H3.
    inversion H. apply _make_jump_table_ind.
      intros. apply Forall_forall. intros. inversion H1; now subst.
      intros. now apply Forall_cons.
    discriminate.
Qed.
