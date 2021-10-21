open Core_extend

(* Obtains a chunk of bits *)
let bits_of inst ~bitoff ~bitlen =
  (inst lsr bitoff) land ((1 lsl bitlen) - 1)

(* Combine a set of bit offsets/bit lengths formed in the bitspec parameter *)
let bits_combine ?(initoff = 0) ?signbit inst ~bitspec =
  let res, reslen = List.fold_left bitspec ~init:(0, initoff)
    ~f:(fun (curval, dstoff) (bitoff, bitlen) ->
      (curval lor bits_of inst ~bitoff ~bitlen lsl dstoff, dstoff + bitlen)) in
  match signbit with
  | Some signbit ->
      (-1 * bits_of inst ~bitoff:signbit ~bitlen:1) lsl reslen lor res
  | None -> res

(* opcode: I[6:0] *)
let opcode = bits_of ~bitoff:0 ~bitlen:7
(* rd [R I U J insn]: I[11:7] *)
let rd = bits_of ~bitoff:7 ~bitlen:5
(* rs1 [R I S B insn]: I[19:15] *)
let rs1 = bits_of ~bitoff:15 ~bitlen:5
(* funct3 [R I S B insn]: I[14:12] *)
let funct3 = bits_of ~bitoff:12 ~bitlen:3
(* imm [I insn]: I[31:20] *)
let imm_of_itype = bits_of ~bitoff:20 ~bitlen:12
(* imm [U insn]: I[31:12] *)
let imm_of_utype = bits_of ~bitoff:12 ~bitlen:20
(* imm [J insn]: I[!31|19:12|20|30:21];
   see pages 16 and 130 of the RISC-V spec *)
let imm_of_jtype = bits_combine ~initoff:1 ~signbit:31
  ~bitspec:[ (21, 10); (20, 1); (12, 8) ]
(* imm [B insn]: I[!31|7|30:25|11:8]; *)
let imm_of_btype = bits_combine ~initoff:1 ~signbit:31
  ~bitspec:[ (8, 4); (25, 6); (7, 1) ]

(*
(* type to represent a RISC-V instruction that has been decoded *)
(* Not going to do S type or R type *)
type riscv_instr =
  | Itype of { (* register-immediate type *)
    imm: int;
    rs1: int;
    funct3: int;
    rd: int;
    opcode: int;
  }
  | Utype of {
    imm: int;
    rd: int;
    opcode: int;
  }

(* decode an instruction and return its representation as a type, or None if it
  is not an instruction, or is an encoding we don't support *)
let decode_instr (encoded:int32) :(riscv_instr option) =
  let dec_opcode = (opcode_of_int32 encoded) in
  match dec_opcode with
  (* U-type *)
  | 0b0110111l (* LUI *)
  | 0b0010111l (* AUPIC *)
    -> Some (Utype {
      imm = Stdlib.Int32.to_int @@ imm_of_utype encoded;
      rd = Stdlib.Int32.to_int @@ rd_of_int32 encoded;
      opcode = Stdlib.Int32.to_int dec_opcode;
    })
  (* I-type, register-immediate. *)
  | 0b1100111l (* JALR *)
  | 0b0000011l (* LB LH LW LBU LHU LWU LD*)
  | 0b0010011l (* ADDI SLTI SLTIU XORI ORI ANDI *)
  | 0b0011011l (* ADDIW *)
    -> Some (Itype {
      imm = Stdlib.Int32.to_int @@ imm_of_utype encoded;
      rs1 = Stdlib.Int32.to_int @@ rs1_of_int32 encoded;
      funct3 = Stdlib.Int32.to_int @@ funct3_of_int32 encoded;
      rd = Stdlib.Int32.to_int @@ rd_of_int32 encoded;
      opcode = Stdlib.Int32.to_int dec_opcode;
    })
  | _ -> None

(* given an decoded instruction (as struct), encode it as an int32 *)
let encode_instr (decoded:riscv_instr) :int32 =
  match decoded with
  | Utype {imm = _; rd = _; opcode = _} -> 0l
  | Itype {imm = _; rs1 = _; funct3 = _; rd = _; opcode = _} ->0l

  *)
