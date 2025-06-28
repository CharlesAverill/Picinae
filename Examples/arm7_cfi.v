Require Export Picinae_armv7_lifter.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
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

Program Fixpoint find_sr (a: list Z) (o sl sr: Z) {measure (Z.to_nat sr)}: option Z :=
  match Z.to_nat sr with
  | O => None
  | _ => if valid_hash a o sl sr then Some sr else find_sr a o sl (sr-Z1)
  end.
Next Obligation. unfold Z1 in *. lia. Qed.

(* find hash parameters, returns (sl, sr)
   a - list of old addresses
   o - offset from new code to old code *)
Program Fixpoint find_hash (a: list Z) (o sl: Z) {measure (Z.to_nat sl)}: option (Z * Z) :=
  match Z.to_nat sl with
  | O => None
  | _ => match find_sr a o sl Z31 with
         | Some sr => Some (sl, sr)
         | None => find_hash a o (sl-Z1)
         end
  end.
Next Obligation. unfold Z1 in *. lia. Qed.

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
Program Fixpoint _make_jump_table (m: Z -> Z) (n i: Z) {measure (Z.to_nat (n - i))} :=
  match Z.to_nat (n - i - Z1) with
  | O => m i::nil
  | _ => m i::_make_jump_table m n (i+Z1)
  end.
Next Obligation. unfold Z1 in *. lia. Qed.
Definition make_jump_table (addrs: list Z) (aabort o sl sr n: Z) : list Z :=
  let m := make_jump_table_map addrs o sl sr (fun _ => aabort) in
  _make_jump_table m n 0.

Definition id := Z.

Definition PC := Z15.
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
Definition arm_add (reg imm: Z) : list arm7_asm :=
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
                  let table := make_jump_table (label oid) aabort (a' - a) sl sr (Z.shiftl Z1 (Z32 - sr)) in
                  let table_cache' := fun x => if x =? oid then Some (atable, sl, sr) else table_cache x in
                  Some (n', dyn, table, table_cache')
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

(*TODO*)
(* (* check a pop {..., pc} *)
(*    regs - 16 bit value from the instrution encoding *)
(*    reg - register to use as a scratch register *) *)
(* Definition checked_pop_pc (regs reg _ _ atable sl sr: Z) : option (list Z) := *)
(*   let pc_offset := Z4 * (Z_popcount regs - Z1) in *)
(*   Some ([ *)
(*     Z0xe50d0000 .| Z32 .| (Z15 << Z12); (* DEBUG: str pc, [sp, #-32] *) *)
(*     Z0xe50d0004 .| (reg << Z12); (* str reg, [sp, #-4] *) *)
(*     Z0xe5900000 .| (reg << Z12) .| (Z13 << Z16) .| pc_offset; (* ldr reg, [sp, #pc_offset] *) *)
(*     Z0xe1a00000 .| (reg << Z12) .| (sl << Z7) .| reg; (* lsl reg, reg, #sl *) *)
(*     Z0xe1a00020 .| (reg << Z12) .| (sr << Z7) .| reg; (* lsr reg, reg, #sr *) *)
(*     Z0xe1a00000 .| (reg << Z12) .| (Z2 << Z7) .| reg (* lsl reg, reg, #2 *) *)
(*   ]++arm_add reg atable++[  (* add reg, reg, #atable *) *)
(*     Z0xe5900000 .| (reg << Z12) .| (reg << Z16); (* ldr reg, [reg] *) *)
(*     Z0xe58d0000 .| (reg << Z12) .| (Z13 << Z16) .| pc_offset; (* str reg, [sp, #pc_offset] *) *)
(*     Z0xe51d0004 .| (reg << Z12); (* ldr reg, [sp, #-4] *) *)
(*     Z0xe8bd0000 .| regs (* pop {regs} *) *)
(*   ]). *)
(* Definition rewrite_pop_pc (regs reg: Z) := rewrite_dyn (checked_pop_pc regs reg) false. *)

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
  match arm_assemble (GOTO true Z14 a' aabort) with
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
      if (Rd =? Z15) then
        rewrite_pc_data sanitized_inst reg Z0 cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? Z15) || (Rm =? Z15) then
        rewrite_pc_data_no_jump sanitized_inst reg Z0 cond n a a' adyn atable aabort table_cache
      else unchanged
  | ARM_data_rsr _ _ _ _ _ _ _ _ => unchanged
  | ARM_data_i op cond s Rn Rd imm12 =>
      let reg := pick_good_reg Rn Rd Z0 in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rd' := if (Rd =? PC) then reg else Rd in
      let sanitized_inst := ARM_data_i op Z14 s Rn' Rd' imm12 in
      if (Rd =? Z15) then
        rewrite_pc_data sanitized_inst reg Z0 cond n oid label a a' adyn atable aabort table_cache
      else if (Rn =? Z15) then
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
      else unchanged (*TODO*)

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
  | ARM_VMOV_fp _ _ _ _ _ _ _ _
  | ARM_VMOV_r2 _ _ _ _ _ _ _
  | ARM_VMOV_r1 _ _ _ _ _
  | ARM_VCMP _ _ _ _ _ _ _
  | ARM_VMRS _ _
  | ARM_vfp _ _ _ _ _ _ _ _ _ _
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
Extract Inlined Constant Z_popcount => "(fun z -> coq_bitb z 0 + coq_bitb z 1 + coq_bitb z 2 + coq_bitb z 3 + coq_bitb z 4 + coq_bitb z 5 + coq_bitb z 6 + coq_bitb z 7 + coq_bitb z 8 + coq_bitb z 9 + coq_bitb z 10 + coq_bitb z 11 + coq_bitb z 12 + coq_bitb z 13 + coq_bitb z 14 + coq_bitb z 15 + coq_bitb z 16 + coq_bitb z 17 + coq_bitb z 18 + coq_bitb z 19 + coq_bitb z 20 + coq_bitb z 21 + coq_bitb z 22 + coq_bitb z 23 + coq_bitb z 24 + coq_bitb z 25 + coq_bitb z 26 + coq_bitb z 27 + coq_bitb z 28 + coq_bitb z 29 + coq_bitb z 30 + coq_bitb z 31)".
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
