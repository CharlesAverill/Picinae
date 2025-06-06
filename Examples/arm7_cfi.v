Require Export Picinae_armv7_lifter.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z.

Definition Z_popcount z := match z with Z0 => Z0 | Z.pos p => Z.pos (Pos_popcount p) | _ => Z0 end.
Definition Z_bitn n b := Z_xbits n b (b + 1).

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
  Z.shiftr ((Z.shiftl z sl) mod (2^32)) sr.

(* checks if the hash produces no unacceptable collisions
   a - list of old addresses
   o - offset from new code to old code
   sl sr - hash parameters *)
Definition valid_hash (a: list Z) (o sl sr: Z) : bool :=
  unique_except_pairs (map (apply_hash sl sr) a) (map (apply_hash sl sr) (map (Z.add o) a)).

(* find hash parameters, returns (sl, sr)
   a - list of old addresses
   o - offset from new code to old code
   h - should start at 1024 *)
Fixpoint find_hash (a: list Z) (o: Z) (h: nat): option (Z * Z) :=
  match h with
  | O => None
  | S h' =>
    let sl := Z.of_nat (Nat.modulo h 32) in
    let sr := Z.of_nat (Nat.div h 32) in
    if valid_hash a o sl sr
    then Some (sl, sr)
    else find_hash a o h'
  end.

(* returns the address that should be in index n of a jump table *)
Fixpoint make_jump_table_entry (addrs: list Z) (aabort o sl sr: Z) (n: Z) : Z :=
  match addrs with
  | nil => aabort
  | a::t => if (apply_hash sl sr a =? n) || (apply_hash sl sr (a+o) =? n)
      then a + o
      else make_jump_table_entry t aabort o sl sr n
  end.

(* create a jump table of size n *)
Fixpoint make_jump_table (addrs: list Z) (aabort o sl sr: Z) (n: nat) : list Z :=
  match n with
  | O => nil
  | S n' => make_jump_table_entry addrs aabort o sl sr (2^(32-sr) - Z.of_nat n)::make_jump_table addrs aabort o sl sr n'
  end.

Definition id := Z.

Notation "x .| y" := (Z.lor x y) (at level 25, left associativity).
Notation "x << y" := (Z.shiftl x y) (at level 40, left associativity).
Notation "x >> y" := (Z.shiftr x y) (at level 40, left associativity).
Notation "x & y" := (Z.land x y) (at level 40, left associativity).

(* rewrite a dynamic jump, returns (new inst encoding, code to put in .dyn, table to put in .table, new table cache function)
   dyn_code - function that takes (atable sl sr) and returns the code to be placed in .dyn
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
Definition rewrite_dyn (dyn_code: Z -> Z -> Z -> Z -> Z -> option (list Z)) (l: bool) (cond: Z) (n: Z) (oid: Z) (label: id -> list Z) (a a' adyn atable aabort: Z) (table_cache: id -> option Z) :=
  let offset := adyn - a' + 8 in
  let n' := (if l then 0xb000000 else 0xa000000) .| (Z.shiftr offset 2) .| (cond << 28) in (* b(l)(cond) adyn *)
  if (15 <? cond) || (offset <? (-33554432)) || (offset >? 33554428) || negb (Z.modulo offset 4 =? 0) then None else
  match find_hash (label oid) (a' - a) 1024 with
  | None => None
  | Some (sl, sr) =>
      match table_cache oid with
      | None =>
          match dyn_code n a atable sl sr with
          | None => None
          | Some dyn =>
              let table := make_jump_table (label oid) aabort (a' - a) sl sr (Z.to_nat (2^(32-sr))) in
              let table_cache' := fun x => if x =? oid then Some atable else table_cache x in
              Some (n', dyn, table, table_cache')
          end
      | Some cached_table =>
          match dyn_code n a cached_table sl sr with
          | None => None
          | Some dyn => Some (n', dyn, nil, table_cache)
          end
      end
  end.

(* add an arbitrary immediate value to a register

   arm's add instruction can only add an immediate that is single byte with a rotation applied to it,
   so adding an arbitrary constant can take up to 4 add instructions *)
Definition arm_add (reg imm: Z) : list Z :=
  let a := if (imm >> 24) & 0xff =? 0 then nil else
      0xe2800400 .| (reg << 12) .| (reg << 16) .| ((imm >> 24) & 0xff)::nil in
  let b := if (imm >> 16) & 0xff =? 0 then a else
      0xe2800800 .| (reg << 12) .| (reg << 16) .| ((imm >> 16) & 0xff)::a in
  let c := if (imm >> 8) & 0xff =? 0 then b else
      0xe2800c00 .| (reg << 12) .| (reg << 16) .| ((imm >> 8) & 0xff)::b in
  if imm & 0xff =? 0 then c else
      0xe2800000 .| (reg << 12) .| (reg << 16) .| (imm & 0xff)::c.

(* check a blx reg or a bx reg
   reg - register that holds the destination address *)
Definition checked_b_reg (reg _ _ atable sl sr: Z) : option (list Z) :=
  Some ([
    0xe1a00000 .| (reg << 12) .| (sl << 7) .| reg; (* lsl reg, reg, #sl *)
    0xe1a00020 .| (reg << 12) .| (sr << 7) .| reg; (* lsr reg, reg, #sr *)
    0xe1a00000 .| (reg << 12) .| (2 << 7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    0xe5900000 .| (reg << 12) .| (reg << 16); (* ldr reg, [reg] *)
    0xe12fff10 .| reg (* bx reg *)
  ]).
Definition rewrite_b_reg (l: bool) (reg: Z) := rewrite_dyn (checked_b_reg reg) l.

(* check a pop {..., pc}
   regs - 16 bit value from the instrution encoding
   reg - register to use as a scratch register *)
Definition checked_pop_pc (regs reg _ _ atable sl sr: Z) : option (list Z) :=
  let pc_offset := 4 * (Z_popcount regs - 1) in
  Some ([
    0xe50d0004 .| (reg << 12); (* str reg, [sp, #-4] *)
    0xe5900000 .| (reg << 12) .| (13 << 16) .| pc_offset; (* ldr reg, [sp, #pc_offset] *)
    0xe1a00000 .| (reg << 12) .| (sl << 7) .| reg; (* lsl reg, reg, #sl *)
    0xe1a00020 .| (reg << 12) .| (sr << 7) .| reg; (* lsr reg, reg, #sr *)
    0xe1a00000 .| (reg << 12) .| (2 << 7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    0xe5900000 .| (reg << 12) .| (reg << 16); (* ldr reg, [reg] *)
    0xe58d0000 .| (reg << 12) .| (13 << 16) .| pc_offset; (* str reg, [sp, #pc_offset] *)
    0xe51d0004 .| (reg << 12); (* ldr reg, [sp, #-4] *)
    0xe8bd0000 .| regs (* pop {regs} *)
  ]).
Definition rewrite_pop_pc (regs reg: Z) := rewrite_dyn (checked_pop_pc regs reg) false.

(* replace the rm, rd and rn fields of a data instruction with reg if they are pc
   n - instruction encoding
   reg - reg to replace pc with *)
Definition replace_pc_data (n reg: Z) : Z :=
  let rm := if Z_xbits n 0 4 =? 15 then (n & 0xffff_fff0) .| reg else n in
  let rd := if Z_xbits rm 12 16 =? 15 then (rm & 0xffff_0fff) .| (reg << 12) else rm in
  if Z_xbits rd 16 20 =? 15 then (rd & 0xfff0_ffff) .| (reg << 16) else rd.

(* check a pc data inst
   reg - register to use as a scratch register *)
Definition checked_pc_data (reg n a atable sl sr: Z) : option (list Z) :=
  Some ([
    0xe50d0004 .| (reg << 12); (* str reg, [sp, #-4] *)

    0xe3000000 .| (reg << 12) .| (((a >> 12) & 0xf) << 16) .| (a & 0xfff); (* movw reg[16:0], #atable[16:0] *)
    0xe3400000 .| (reg << 12) .| (((a >> 28) & 0xf) << 16) .| ((a >> 16) & 0xfff); (* movt reg[32:16], #atable[32:16] *)
    replace_pc_data n reg; (* replace pc with reg *)

    0xe1a00000 .| (reg << 12) .| (sl << 7) .| reg; (* lsl reg, reg, #sl *)
    0xe1a00020 .| (reg << 12) .| (sr << 7) .| reg; (* lsr reg, reg, #sr *)
    0xe1a00000 .| (reg << 12) .| (2 << 7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    0xe5900000 .| (reg << 12) .| (reg << 16); (* ldr reg, [reg] *)
    0xe50d0008 .| (reg << 12); (* str reg, [sp, #-8] *)
    0xe51d0004 .| (reg << 12); (* ldr reg, [sp, #-4] *)
    0xe51df008 (* ldr pc, [sp, #-8] *)
  ]).
Definition rewrite_pc_data (reg: Z) := rewrite_dyn (checked_pc_data reg) false.

(* rewrite a single instruction, see rewrite_dyn for signature *)
Definition rewrite_inst (n: Z) (oid: id) (label: id -> list Z) (a a' adyn atable aabort: Z) (table_cache: id -> option Z): option (Z * list Z * list Z * (id -> option Z)) :=
  let cond := Z_xbits n 28 32 in
  let unchanged := Some (n, nil, nil, table_cache) in
  if Z_xbits n 4 28 =? 1245171 then (* BLX reg *)
    let reg := Z_xbits n 0 4 in
    rewrite_b_reg true reg cond n oid label a a' adyn atable aabort table_cache
  else if Z_xbits n 4 28 =? 1245169 then (* BX reg *)
    let reg := Z_xbits n 0 4 in
    rewrite_b_reg false reg cond n oid label a a' adyn atable aabort table_cache
  else if Z_xbits n 16 28 =? 2237 then (* pop {regs} *)
    let regs := Z_xbits n 0 16 in
    if 32767 <? regs then rewrite_pop_pc regs 5 cond n oid label a a' adyn atable aabort table_cache else Some (n, nil, nil, table_cache)
  else if Z_xbits n 26 28 =? 0 then (* data processing / misc *)
    if (Z_xbits n 23 25 =? 10) && (Z_bitn n 20 =? 0) then (* op1 == 10xx0 *)
      unchanged
    else if (Z_bitn n 25 =? 1) || (Z_bitn n 4 =? 0) || (Z_bitn n 7 =? 0) then (* data processing *)
      if Z_xbits n 12 16 =? 15 then (* pc data *)
        rewrite_pc_data 5 cond n oid label a a' adyn atable aabort table_cache
      else
        unchanged
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
Fixpoint _rewrite (table_cache: id -> option Z) (pol: Z -> id) (label: id -> list Z) (ns: list Z) (a a' adyn atable aabort: Z) : option (list Z * list (list Z) * list (list Z)) :=
  match ns with
  | nil => Some (nil, nil, nil)
  | n::tail =>
      match rewrite_inst n (pol a) label a a' adyn atable aabort table_cache with
      | None => None
      | Some (n', dyn, table, table_cache') =>
          match _rewrite table_cache' pol label tail (a+4) (a'+4) (adyn + 4 * Z.of_nat (length dyn)) (atable + 4 * Z.of_nat (length table)) aabort with
          | None => None
          | Some (n_t, dyn_t, table_t) => Some (n'::n_t, dyn::dyn_t, table::table_t) end end end.
Definition rewrite := _rewrite (fun _ => None).
