
(* logical-and out bits 6:0, which represents the opcode *)
let opcode_of_int32 (inst:int32) :int32 
  = Stdlib.Int32.logand inst 0x0000007fl

(* logical-and out bits 11:7. this represents rd of R I U J *)
let rd_of_int32 (inst:int32) :int32 
  = (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x00000f80l) 7)

(* logical-and out bits 19:15. this represents the rs1 of R, I, S, B types *)
let rs1_of_int32 (inst:int32) :int32 
  = (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x000f8000l) 15)

(* logical-and out bits 14:12. this represents funct3 of R, I, S, B types *)
let funct3_of_int32 (inst:int32) :int32 
  = (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x00003000l) 12)

(* logical-and out bits 31:25. this represents the imm of an I type *)
let imm_of_itype (inst:int32) :int32 
  = (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0xfff00000l) 25)

(* logical-and out bits 31:12. this represents immediate of a u type *)
let imm_of_utype (inst:int32) :int32 
  = (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0xfffff000l) 12)

(* see pages 16 and 130 of the RISC-V spec
  J-type instruction: intermediate is 
  imm[20|10:1|11|19:12] *)
let imm_of_jtype (inst:int32) :int32 = 
  (* logical-or all these numbers together *)
  let unsigned_imm = (Stdlib.List.fold_left
    Stdlib.Int32.logor 0l (* 0 to make the 0th bit 0 *)
    [ (* See page 17 of the RISC-V Spec for encoding *)
      (* move one bit 31 to pos 20 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x80000000l) 11); 
      (* eight bits 19:12 are the same in both inst and imm *)
      (Stdlib.Int32.logand inst 0x000ff000l);
      (* move one bit 20 to pos 11 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x00100000l) 9);
      (* move ten bits 30:21 to pos 10:1 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x7fe00000l) 20);
    ]
  ) in unsigned_imm
  (* signed-ed ness is handled by the fact that Stdlib.Int32.shift_right is arithmetic, and guaranteed the
    sign bit of the original instrucion is the MSB of the immediate *)

(* see pages 16 and 130 of the RISC-V spec
  B-type instruction: intermediate is
  imm[12|10:5|4:1|11 *)
let imm_of_btype (inst:int32) :int32 = 
  (* logical-or all these numbers together *)
  let unsigned_imm = (Stdlib.List.fold_left
    Stdlib.Int32.logor 0l  (* 0 to make the 0th bit 0 *)
    [ (* See page 17 of the RISC-V Spec for encoding *)
      (* move one bit 31 to pos 12 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x80000000l) 19); 
      (* move one bit 7 to pos 11 *)
      (Stdlib.Int32.shift_left (Stdlib.Int32.logand inst 0x00000080l) 4);
      (* move six bits 30:25 to pos 10:5 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x7e000000l) 20);
      (* move four bits 11:8 to pos 4:1 *)
      (Stdlib.Int32.shift_right (Stdlib.Int32.logand inst 0x00000f00l) 7);
    ]
  ) in unsigned_imm

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
  | Utype {imm, rd, opcode} -> 0l
  | Itype {imm, rs1, funct3, rd, opcode} ->0l

