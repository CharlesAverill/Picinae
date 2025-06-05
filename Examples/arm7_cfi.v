Require Export Picinae_armv7_lifter.
Require Import NArith.
Require Import ZArith.
Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope N.

(* checks if l contains n *)
Definition contains (n: N) (l: list N) : bool :=
  match find (N.eqb n) l with
  | Some _ => true
  | None => false
  end.

(* checks if all elements in the two lists are unique, but allows the two elements at the same index in l and l' to be the same *)
Fixpoint unique_except_pairs (l l': list N) : bool :=
  match l, l' with
  | a::t, a'::t'=> if contains a (t++t') || contains a' (t++t') then false else unique_except_pairs t t'
  | _, _ => true
  end.

(* H(x) = (x LSL sl) LSR sr *)
Definition apply_hash (sl sr: N) (n: N) : N :=
  N.shiftr ((N.shiftl n sl) mod (2^32)) sr.

(* checks if the hash produces no unacceptable collisions
   a - list of old addresses
   o - offset from new code to old code
   sl sr - hash parameters *)
Definition valid_hash (a: list N) (o sl sr: N) : bool :=
  unique_except_pairs (map (apply_hash sl sr) a) (map (apply_hash sl sr) (map (N.add o) a)).

(* find hash parameters, returns (sl, sr)
   a - list of old addresses
   o - offset from new code to old code
   h - should start at 1024 *)
Fixpoint find_hash (a: list N) (o: N) (h: nat): option (N * N) :=
  match h with
  | O => None
  | S h' =>
    let sl := N.of_nat (Nat.modulo h 32) in
    let sr := N.of_nat (Nat.div h 32) in
    if valid_hash a o sl sr
    then Some (sl, sr)
    else find_hash a o h'
  end.

(* returns the address that should be in index n of a jump table *)
Fixpoint make_jump_table_entry (addrs: list N) (aabort o sl sr: N) (n: N) : N :=
  match addrs with
  | nil => aabort
  | a::t => if (apply_hash sl sr a =? n) || (apply_hash sl sr (a+o) =? n)
      then a + o
      else make_jump_table_entry t aabort o sl sr n
  end.

(* create a jump table of size n *)
Fixpoint make_jump_table (addrs: list N) (aabort o sl sr: N) (n: nat) : list N :=
  match n with
  | O => nil
  | S n' => make_jump_table_entry addrs aabort o sl sr (2^(32-sr) - N.of_nat n)::make_jump_table addrs aabort o sl sr n'
  end.

Definition id := N.

Notation "x .| y" := (N.lor x y) (at level 25, left associativity).
Notation "x << y" := (N.shiftl x y) (at level 40, left associativity).
Notation "x >> y" := (N.shiftr x y) (at level 40, left associativity).
Notation "x & y" := (N.land x y) (at level 40, left associativity).

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
Definition rewrite_dyn (dyn_code: N -> N -> N -> N -> N -> option (list N)) (l: bool) (cond: N) (n: N) (oid: N) (label: id -> list N) (a a' adyn atable aabort: N) (table_cache: id -> option N) :=
  let offset := Z.sub (Z.of_N adyn) (Z.of_N (a' + 8)) in
  let n' := (if l then 0xb000000 else 0xa000000) .| (ofZ 24 (Z.shiftr offset 2)) .| (cond << 28) in (* b(l)(cond) adyn *)
  if (15 <? cond) || Z.ltb offset (-33554432) || Z.gtb offset 33554428 || negb (Z.eqb (Z.modulo offset 4) 0) then None else
  match find_hash (label oid) (a' - a) 1024 with
  | None => None
  | Some (sl, sr) =>
      match table_cache oid with
      | None =>
          match dyn_code n a atable sl sr with
          | None => None
          | Some dyn =>
              let table := make_jump_table (label oid) aabort (a' - a) sl sr (N.to_nat (2^(32-sr))) in
              let table_cache' := fun x => if x == oid then Some atable else table_cache x in
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
Definition arm_add (reg imm: N) : list N :=
  let a := if (imm >> 24) & 0xff == 0 then nil else
      0xe2800400 .| (reg << 12) .| (reg << 16) .| ((imm >> 24) & 0xff)::nil in
  let b := if (imm >> 16) & 0xff == 0 then a else
      0xe2800800 .| (reg << 12) .| (reg << 16) .| ((imm >> 16) & 0xff)::a in
  let c := if (imm >> 8) & 0xff == 0 then b else
      0xe2800c00 .| (reg << 12) .| (reg << 16) .| ((imm >> 8) & 0xff)::b in
  if imm & 0xff == 0 then c else
      0xe2800000 .| (reg << 12) .| (reg << 16) .| (imm & 0xff)::c.

(* check a blx reg or a bx reg
   reg - register that holds the destination address *)
Definition checked_b_reg (reg _ _ atable sl sr: N) : option (list N) :=
  Some ([
    0xe1a00000 .| (reg << 12) .| (sl << 7) .| reg; (* lsl reg, reg, #sl *)
    0xe1a00020 .| (reg << 12) .| (sr << 7) .| reg; (* lsr reg, reg, #sr *)
    0xe1a00000 .| (reg << 12) .| (2 << 7) .| reg (* lsl reg, reg, #2 *)
  ]++arm_add reg atable++[  (* add reg, reg, #atable *)
    0xe5900000 .| (reg << 12) .| (reg << 16); (* ldr reg, [reg] *)
    0xe12fff10 .| reg (* bx reg *)
  ]).
Definition rewrite_b_reg (l: bool) (reg: N) := rewrite_dyn (checked_b_reg reg) l.

(* check a pop {..., pc}
   regs - 16 bit value from the instrution encoding
   reg - register to use as a scratch register *)
Definition checked_pop_pc (regs reg _ _ atable sl sr: N) : option (list N) :=
  let pc_offset := 4 * (popcount regs - 1) in
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
Definition rewrite_pop_pc (regs reg: N) := rewrite_dyn (checked_pop_pc regs reg) false.

(* replace the rm, rd and rn fields of a data instruction with reg if they are pc
   n - instruction encoding
   reg - reg to replace pc with *)
Definition replace_pc_data (n reg: N) : N :=
  let rm := if (xbits n 0 4) == 15 then (n & 0xffff_fff0) .| reg else n in
  let rd := if (xbits rm 12 16) == 15 then (rm & 0xffff_0fff) .| (reg << 12) else rm in
  if (xbits rd 16 20) == 15 then (rd & 0xfff0_ffff) .| (reg << 16) else rd.

(* check a pc data inst
   reg - register to use as a scratch register *)
Definition checked_pc_data (reg n a atable sl sr: N) : option (list N) :=
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
Definition rewrite_pc_data (reg: N) := rewrite_dyn (checked_pc_data reg) false.

(* rewrite a single instruction, see rewrite_dyn for signature *)
Definition rewrite_inst (n: N) (oid: id) (label: id -> list N) (a a' adyn atable aabort: N) (table_cache: id -> option N): option (N * list N * list N * (id -> option N)) :=
  match arm_decode n with
  | ARM_BLX cond reg => rewrite_b_reg true reg cond n oid label a a' adyn atable aabort table_cache
  | ARM_BX cond reg => rewrite_b_reg false reg cond n oid label a a' adyn atable aabort table_cache
  | ARM_POP cond regs => if 32767 <? regs then rewrite_pop_pc regs 5 cond n oid label a a' adyn atable aabort table_cache else Some (n, nil, nil, table_cache)

  | ARM_AND cond _ _ _ 15 _
  | ARM_EOR cond _ _ _ 15 _
  | ARM_SUB cond _ _ _ 15 _
  | ARM_RSB cond _ _ _ 15 _
  | ARM_ADD cond _ _ _ 15 _
  | ARM_ADC cond _ _ _ 15 _
  | ARM_SBC cond _ _ _ 15 _
  | ARM_RSC cond _ _ _ 15 _
  | ARM_ORR cond _ _ _ 15 _
  | ARM_MOV cond _ _   15 _
  | ARM_BIC cond _ _ _ 15 _
  | ARM_MVN cond _ _   15 _
      => rewrite_pc_data 5 cond n oid label a a' adyn atable aabort table_cache

(*| other_dynamic_jump => rewrite_dynamic ... *)
(*| static_jump => if valid then n else b_abort *)
(*| ARM_B cond imm24 => if contains (sbop1 Z.add 32 (a + 8) (scast 26 32 (N.shiftl imm24 2))) (label oid) then Some (n, nil, nil, table_cache) else Some (0 (* b(cond) aabort *), nil, nil, table_cache) *)
  | _ => Some (n, nil, nil, table_cache)
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
Fixpoint _rewrite (table_cache: id -> option N) (pol: N -> id) (label: id -> list N) (ns: list N) (a a' adyn atable aabort: N) : option (list N * list (list N) * list (list N)) :=
  match ns with
  | nil => Some (nil, nil, nil)
  | n::tail =>
      match rewrite_inst n (pol a) label a a' adyn atable aabort table_cache with
      | None => None
      | Some (n', dyn, table, table_cache') =>
          match _rewrite table_cache' pol label tail (a+4) (a'+4) (adyn + 4 * N.of_nat (length dyn)) (atable + 4 * N.of_nat (length table)) aabort with
          | None => None
          | Some (n_t, dyn_t, table_t) => Some (n'::n_t, dyn::dyn_t, table::table_t) end end end.
Definition rewrite := _rewrite (fun _ => None).
