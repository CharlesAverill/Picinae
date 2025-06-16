Require Export Picinae_armv7_lifter.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z.

Definition Z0xa000000 := 0xa000000.
Definition Z0xb000000 := 0xb000000.
Definition Z0xe12fff10 := 0xe12fff10.
Definition Z0xe1a00000 := 0xe1a00000.
Definition Z0xe1a00020 := 0xe1a00020.
Definition Z0xe2800000 := 0xe2800000.
Definition Z0xe2800400 := 0xe2800400.
Definition Z0xe2800800 := 0xe2800800.
Definition Z0xe2800c00 := 0xe2800c00.
Definition Z0xe3000000 := 0xe3000000.
Definition Z0xe3400000 := 0xe3400000.
Definition Z0xe50d0000 := 0xe50d0000.
Definition Z0xe50d0004 := 0xe50d0004.
Definition Z0xe50d0008 := 0xe50d0008.
Definition Z0xe51d0000 := 0xe51d0000.
Definition Z0xe51df000 := 0xe51df000.
Definition Z0xe51d0004 := 0xe51d0004.
Definition Z0xe51df008 := 0xe51df008.
Definition Z0xe58d0000 := 0xe58d0000.
Definition Z0xe5900000 := 0xe5900000.
Definition Z0xe8bd0000 := 0xe8bd0000.
Definition Z0xf := 0xf.
Definition Z0xff := 0xff.
Definition Z0xfff := 0xfff.
Definition Z0xfff0_ffff := 0xfff0_ffff.
Definition Z0xffff_0000 := 0xfff0_0000.
Definition Z0xffff_0fff := 0xffff_0fff.
Definition Z0xffff_fff0 := 0xffff_fff0.
Definition Z0xffff_ffff := 0xffff_ffff.
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
Definition Z40 := 40.
Definition Z1024 := 1024.
Definition Z2237 := 2237.
Definition Z32767 := 32767.
Definition Z1245169 := 1245169.
Definition Z1245171 := 1245171.
Definition Z33554428 := 33554428.
Definition Z_33554432 := -33554432.
Definition Z4294967296 := 4294967296.

Definition Z_popcount z := match z with Z0 => Z0 | Z.pos p => Z.pos (Pos_popcount p) | _ => Z0 end.
Definition Z_xbits z i j := Z.shiftr z i mod Z.shiftl Z1 (Z.max Z0 (j - i)).
Definition Z_bitn n b := Z_xbits n b (b + Z1).

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

Require Import Coq.Program.Wf.
Require Import Lia.

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

Notation "x .| y" := (Z.lor x y) (at level 25, left associativity).
Notation "x << y" := (Z.shiftl x y) (at level 40, left associativity).
Notation "x >> y" := (Z.shiftr x y) (at level 40, left associativity).
Notation "x & y" := (Z.land x y) (at level 40, left associativity).

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
  let offset := adyn - a' - Z8 in
  let n' := (if l then Z0xb000000 else Z0xa000000) .| (Z.shiftr offset Z2) .| (cond << Z28) in (* b(l)(cond) adyn *)
  if (Z15 <? cond) || (offset <? (Z_33554432)) || (offset >? Z33554428) || negb (offset mod Z4 =? Z0) then None else
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
  end.

(* add an arbitrary immediate value to a register

   arm's add instruction can only add an immediate that is single byte with a rotation applied to it,
   so adding an arbitrary constant can take up to 4 add instructions *)
Definition arm_add (reg imm: Z) : list Z :=
  let a := if (imm >> Z24) & Z0xff =? Z0 then nil else
      Z0xe2800400 .| (reg << Z12) .| (reg << Z16) .| ((imm >> Z24) & Z0xff)::nil in
  let b := if (imm >> Z16) & Z0xff =? Z0 then a else
      Z0xe2800800 .| (reg << Z12) .| (reg << Z16) .| ((imm >> Z16) & Z0xff)::a in
  let c := if (imm >> Z8) & Z0xff =? Z0 then b else
      Z0xe2800c00 .| (reg << Z12) .| (reg << Z16) .| ((imm >> Z8) & Z0xff)::b in
  if imm & Z0xff =? Z0 then c else
      Z0xe2800000 .| (reg << Z12) .| (reg << Z16) .| (imm & Z0xff)::c.

(* check a blx reg or a bx reg
   reg - register that holds the destination address *)
Definition checked_b_reg (reg _ _ atable sl sr: Z) : option (list Z) :=
  Some ([
    Z0xe1a00000 .| (reg << Z12) .| (sl << Z7) .| reg; (* lsl reg, reg, #sl *)
    Z0xe1a00020 .| (reg << Z12) .| (sr << Z7) .| reg; (* lsr reg, reg, #sr *)
    Z0xe1a00000 .| (reg << Z12) .| (Z2 << Z7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    Z0xe5900000 .| (reg << Z12) .| (reg << Z16); (* ldr reg, [reg] *)
    Z0xe12fff10 .| reg (* bx reg *)
  ]).
Definition rewrite_b_reg (l: bool) (reg: Z) := rewrite_dyn (checked_b_reg reg) l.

(* check a pop {..., pc}
   regs - 16 bit value from the instrution encoding
   reg - register to use as a scratch register *)
Definition checked_pop_pc (regs reg _ _ atable sl sr: Z) : option (list Z) :=
  let pc_offset := Z4 * (Z_popcount regs - Z1) in
  Some ([
    Z0xe50d0004 .| (reg << Z12); (* str reg, [sp, #-4] *)
    Z0xe5900000 .| (reg << Z12) .| (Z13 << Z16) .| pc_offset; (* ldr reg, [sp, #pc_offset] *)
    Z0xe1a00000 .| (reg << Z12) .| (sl << Z7) .| reg; (* lsl reg, reg, #sl *)
    Z0xe1a00020 .| (reg << Z12) .| (sr << Z7) .| reg; (* lsr reg, reg, #sr *)
    Z0xe1a00000 .| (reg << Z12) .| (Z2 << Z7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    Z0xe5900000 .| (reg << Z12) .| (reg << Z16); (* ldr reg, [reg] *)
    Z0xe58d0000 .| (reg << Z12) .| (Z13 << Z16) .| pc_offset; (* str reg, [sp, #pc_offset] *)
    Z0xe51d0004 .| (reg << Z12); (* ldr reg, [sp, #-4] *)
    Z0xe8bd0000 .| regs (* pop {regs} *)
  ]).
Definition rewrite_pop_pc (regs reg: Z) := rewrite_dyn (checked_pop_pc regs reg) false.

Definition replace_pc_at_offset (o n reg: Z) : Z :=
  let mask := Z0xffff_ffff - (Z0xf << o) in
  if Z_xbits n o (o+Z4) =? Z15 then
    (n & mask) .| (reg << o)
  else
    n.
Definition replace_pc_rm := replace_pc_at_offset Z0.
Definition replace_pc_rd := replace_pc_at_offset Z12.
Definition replace_pc_rn := replace_pc_at_offset Z16.

Definition replace_pc_data (n reg: Z) : Z :=
  let rm := replace_pc_rm n reg in
  let rd := replace_pc_rd rm reg in
  replace_pc_rn rd reg.
Definition replace_pc_data_imm (n reg: Z) : Z :=
  let rd := replace_pc_rd n reg in
  replace_pc_rn rd reg.

Definition pick_good_reg (n: Z) : Z :=
  let rm := Z_xbits n Z0 Z4 in
  let rd := Z_xbits n Z12 Z16 in
  let rn := Z_xbits n Z16 Z20 in
  if (rm =? Z0) || (rd =? Z0) || (rn =? Z0) then
    if (rm =? Z1) || (rd =? Z1) || (rn =? Z1) then
      if (rm =? Z2) || (rd =? Z2) || (rn =? Z2) then
        Z3
      else
        Z2
    else
      Z1
  else
    Z0.

(* check a pc data inst
   reg - register to use as a scratch register *)
Definition checked_pc_data (replace: Z -> Z -> Z) (reg stack_offset n a atable sl sr: Z) : option (list Z) :=
  let a := a + Z8 in
  Some ([
    Z0xe50d0004 .| (reg << Z12); (* str reg, [sp, #-4] *)

    Z0xe3000000 .| (reg << Z12) .| (((a >> Z12) & Z0xf) << Z16) .| (a & Z0xfff); (* movw reg[16:0], #a[16:0] *)
    Z0xe3400000 .| (reg << Z12) .| (((a >> Z28) & Z0xf) << Z16) .| ((a >> Z16) & Z0xfff); (* movt reg[32:16], #a[32:16] *)
    replace n reg; (* replace pc with reg *)

    Z0xe1a00000 .| (reg << Z12) .| (sl << Z7) .| reg; (* lsl reg, reg, #sl *)
    Z0xe1a00020 .| (reg << Z12) .| (sr << Z7) .| reg; (* lsr reg, reg, #sr *)
    Z0xe1a00000 .| (reg << Z12) .| (Z2 << Z7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    Z0xe5900000 .| (reg << Z12) .| (reg << Z16); (* ldr reg, [reg] *)
    Z0xe50d0000 .| (reg << Z12) .| (stack_offset + Z8); (* str reg, [sp, #-8] *)
    Z0xe51d0000 .| (reg << Z12) .| (stack_offset + Z4); (* ldr reg, [sp, #-4] *)
    Z0xe51df000 .| (stack_offset + Z8) (* ldr pc, [sp, #-8] *)
  ]).

Definition rewrite_pc_data (replace: Z -> Z -> Z) (reg stack_offset: Z) := rewrite_dyn (checked_pc_data replace reg stack_offset) false.
(* rewrite a pc data inst that does not affect control flow *)
Definition rewrite_pc_data_no_jump (replace: Z -> Z -> Z) (reg stack_offset: Z) (cond: Z) (n: Z) (a a' adyn atable aabort: Z) (table_cache: id -> option (Z * Z * Z)) : option (Z * list Z * list Z * (id -> option (Z * Z * Z))) :=
  let a := a + Z8 in
  let offset := adyn - a' - Z8 in
  let n' := Z0xa000000 .| (Z.shiftr (offset mod (Z.shiftl Z1 Z26)) Z2) .| (cond << Z28) in (* b(cond) adyn *)
  let jump_back := Z0xa000000 .| (Z.shiftr ((-offset-Z32) mod (Z.shiftl Z1 Z26)) Z2) .| (Z14 << Z28) in (* b (a+4)  *)
  if (Z15 <? cond) || (offset <? (Z_33554432)) || (offset >? Z33554428) || negb (offset mod Z4 =? Z0) then None else
  let dyn := [
    Z0xe50d0004 .| (reg << Z12); (* str reg, [sp, #-4] *)
    Z0xe3000000 .| (reg << Z12) .| (((a >> Z12) & Z0xf) << Z16) .| (a & Z0xfff); (* movw reg[16:0], #a[16:0] *)
    Z0xe3400000 .| (reg << Z12) .| (((a >> Z28) & Z0xf) << Z16) .| ((a >> Z16) & Z0xfff); (* movt reg[32:16], #a[32:16] *)
    replace n reg; (* replace pc with reg *)
    Z0xe51d0000 .| (reg << Z12) .| (stack_offset + Z4); (* ldr reg, [sp, #-4] *)
    jump_back
  ] in
  Some (n', dyn, nil, table_cache).

(* rewrite a single instruction, see rewrite_dyn for signature *)
Definition rewrite_inst (n: Z) (oid: id) (label: id -> list Z) (a a' adyn atable aabort: Z) (table_cache: id -> option (Z * Z * Z)): option (Z * list Z * list Z * (id -> option (Z * Z * Z))) :=
  let cond := Z_xbits n Z28 Z32 in
  let unchanged := Some (n, nil, nil, table_cache) in
  if Z_xbits n Z4 Z28 =? Z1245171 then (* BLX reg *)
    let reg := Z_xbits n Z0 Z4 in
    rewrite_b_reg true reg cond n oid label a a' adyn atable aabort table_cache
  else if Z_xbits n Z4 Z28 =? Z1245169 then (* BX reg *)
    let reg := Z_xbits n Z0 Z4 in
    rewrite_b_reg false reg cond n oid label a a' adyn atable aabort table_cache
  else if Z_xbits n Z16 Z28 =? Z2237 then (* pop {regs} *)
    let regs := Z_xbits n Z0 Z16 in
    if Z32767 <? regs then rewrite_pop_pc regs Z5 cond n oid label a a' adyn atable aabort table_cache else unchanged
  else if Z_xbits n Z28 Z32 =? Z15 then
    unchanged
  else if Z_xbits n Z26 Z28 =? Z0 then (* data processing / misc *)
    if (Z_xbits n Z23 Z25 =? Z2) && (Z_bitn n Z20 =? Z0) then (* op1 == 10xx0 *)
      unchanged
    else if (Z_bitn n Z25 =? Z1) || (Z_bitn n Z4 =? Z0) || (Z_bitn n Z7 =? Z0) then (* data processing *)
      let replace := if (Z_bitn n Z25 =? Z0) then replace_pc_data else replace_pc_data_imm in
      let reg := pick_good_reg n in
      if Z_xbits n Z12 Z16 =? Z15 then (* pc data *)
        rewrite_pc_data replace reg Z0 cond n oid label a a' adyn atable aabort table_cache
      else if (Z_bitn n Z25 =? Z0) && (Z_xbits n Z0 Z4 =? Z15) || (Z_xbits n Z16 Z20 =? Z15) then
        rewrite_pc_data_no_jump replace reg Z0 cond n a a' adyn atable aabort table_cache
      else
        unchanged
    else
      unchanged
  else if (Z_xbits n Z26 Z28 =? Z1) && ((Z_bitn n Z4 =? Z0) || (Z_bitn n Z25 =? Z0)) then (* load store *)
    let replace := if (Z_bitn n Z25 =? Z0) then replace_pc_data else replace_pc_data_imm in
    let reg := pick_good_reg n in
    let stack_offset := if (Z_bitn n Z24 =? Z0) || (Z_bitn n Z21 =? Z1) then (Z_xbits n Z0 Z12) else Z0 in
    if (Z_bitn n Z20 =? Z1) && (Z_xbits n Z12 Z16 =? Z15) then
      rewrite_pc_data replace reg stack_offset cond n oid label a a' adyn atable aabort table_cache
    else if (Z_xbits n Z12 Z16 =? Z15) || (Z_xbits n Z16 Z20 =? Z15) then
      rewrite_pc_data_no_jump replace reg stack_offset cond n a a' adyn atable aabort table_cache
    else
      unchanged
  else
    unchanged.

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
Extract Inlined Constant Z0xa000000 => "0xa000000".
Extract Inlined Constant Z0xb000000 => "0xb000000".
Extract Inlined Constant Z0xe12fff10 => "0xe12fff10".
Extract Inlined Constant Z0xe1a00000 => "0xe1a00000".
Extract Inlined Constant Z0xe1a00020 => "0xe1a00020".
Extract Inlined Constant Z0xe2800000 => "0xe2800000".
Extract Inlined Constant Z0xe2800400 => "0xe2800400".
Extract Inlined Constant Z0xe2800800 => "0xe2800800".
Extract Inlined Constant Z0xe2800c00 => "0xe2800c00".
Extract Inlined Constant Z0xe3000000 => "0xe3000000".
Extract Inlined Constant Z0xe3400000 => "0xe3400000".
Extract Inlined Constant Z0xe50d0000 => "0xe50d0000".
Extract Inlined Constant Z0xe50d0004 => "0xe50d0004".
Extract Inlined Constant Z0xe50d0008 => "0xe50d0008".
Extract Inlined Constant Z0xe51d0000 => "0xe51d0000".
Extract Inlined Constant Z0xe51d0004 => "0xe51d0004".
Extract Inlined Constant Z0xe51df000 => "0xe51df000".
Extract Inlined Constant Z0xe51df008 => "0xe51df008".
Extract Inlined Constant Z0xe58d0000 => "0xe58d0000".
Extract Inlined Constant Z0xe5900000 => "0xe5900000".
Extract Inlined Constant Z0xe8bd0000 => "0xe8bd0000".
Extract Inlined Constant Z0xf => "0xf".
Extract Inlined Constant Z0xff => "0xff".
Extract Inlined Constant Z0xfff => "0xfff".
Extract Inlined Constant Z0xfff0_ffff => "0xfff0_ffff".
Extract Inlined Constant Z0xffff_0000 => "0xffff_0000".
Extract Inlined Constant Z0xffff_0fff => "0xffff_0fff".
Extract Inlined Constant Z0xffff_fff0 => "0xffff_fff0".
Extract Inlined Constant Z0xffff_ffff => "0xffff_ffff".
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
Extract Inlined Constant Z40 => "40".
Extract Inlined Constant Z1024 => "1024".
Extract Inlined Constant Z2237 => "2237".
Extract Inlined Constant Z32767 => "32767".
Extract Inlined Constant Z1245169 => "1245169".
Extract Inlined Constant Z1245171 => "1245171".
Extract Inlined Constant Z33554428 => "33554428".
Extract Inlined Constant Z_33554432 => "(-33554432)".
Extract Inlined Constant Z4294967296 => "4294967296".
Extract Inlined Constant Z.opp => "(~-)".
Extract Inlined Constant Z.ltb => "(<)".
(* maybe use library that has popcount instrinsic? *)
Extract Inlined Constant Z_popcount => "(fun z -> coq_Z_bitn z 0 + coq_Z_bitn z 1 + coq_Z_bitn z 2 + coq_Z_bitn z 3 + coq_Z_bitn z 4 + coq_Z_bitn z 5 + coq_Z_bitn z 6 + coq_Z_bitn z 7 + coq_Z_bitn z 8 + coq_Z_bitn z 9 + coq_Z_bitn z 10 + coq_Z_bitn z 11 + coq_Z_bitn z 12 + coq_Z_bitn z 13 + coq_Z_bitn z 14 + coq_Z_bitn z 15 + coq_Z_bitn z 16 + coq_Z_bitn z 17 + coq_Z_bitn z 18 + coq_Z_bitn z 19 + coq_Z_bitn z 20 + coq_Z_bitn z 21 + coq_Z_bitn z 22 + coq_Z_bitn z 23 + coq_Z_bitn z 24 + coq_Z_bitn z 25 + coq_Z_bitn z 26 + coq_Z_bitn z 27 + coq_Z_bitn z 28 + coq_Z_bitn z 29 + coq_Z_bitn z 30 + coq_Z_bitn z 31)".
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
