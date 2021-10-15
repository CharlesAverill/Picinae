
(* print the policy *)
let pp_policy (int32_insns_list: int32 list) generated_policy =
  (* Print all the numbers in this segment *)
  (Stdlib.List.fold_left2
    (fun _ b (_, (_, rel_dests)) ->
      (Printf.eprintf "[0x%lx], policy is :" b);
      (Stdlib.List.fold_left (fun _ b -> Printf.eprintf "<%d> " b) () rel_dests);
      (Printf.eprintf "\n")
    )
    ()
    int32_insns_list
    generated_policy
  )

(* from `cfi_riscv_extraction.v`:
  "(2) an "output identifier", which identifies the equivalence class of targets
  to which this instruction is permitted to indirectly jump;" We have this as
  the magic number "13" in that, for simplicity, all jumps are given the same
  class targets that an instruction can jump. *)
let equiv_class_targets:int = 13

(* Given a policy, raise an exception if the policy violates the "simple" jump
   correctness: That is, make sure that every static jump will jump to somewhere
   inside the code segment.  We verify this by taking the instruction's position
   in the list (its offset from the first inst) and adding (one by one) all the
   relative targets associated with it in the policy, and verifying that the
   resulting inst offset is inside the code segment. *)
exception InvalidJump of string
let verify_policy_jump_ranges (policy : Extraction.policy) =
  (Stdlib.List.fold_left
    (* pull apart the policy entry *)
    (fun (current_inst_offset, _)  (_, (_, rel_dests)) ->
      (Stdlib.List.fold_left
        (fun _ rel_dest ->
          (* We now have the relative destination and the current inst offset, compute if that is
            inside the code segment and throw if it is not *)
          let target = rel_dest + current_inst_offset in
          (if target <= 0 then
            raise (InvalidJump ("Jump out of bounds, too low, inst "
                                  ^ (Stdlib.string_of_int current_inst_offset)
                                  ^ " and rel dest "
                                  ^ (Stdlib.string_of_int rel_dest))) else ()
          );
          (if target >= (Stdlib.List.length policy) then
            raise (InvalidJump ("Jump out of bounds, too high, inst"
                                  ^ (Stdlib.string_of_int current_inst_offset)
                                  ^ " and rel dest "
                                  ^ (Stdlib.string_of_int rel_dest))) else ()
          );
        )
        ()
        rel_dests
      );(current_inst_offset + 1, ())
    )
    (0, ())
    policy
  )
let generate_static_policy (int_list_mem : int32 list) :Extraction.policy =
  let to_return =
  (Stdlib.List.fold_left
    (fun accum inst ->
      match Disasm.opcode_of_int32 inst with
      (*  if the opcode is exactly the one for the JAL instruction:
        We add to the policy:
          -None for the input identifier
          -Global constant for the output identifier
          -the list of jump/fallthrough targets (relative distance), which is
            -1, aka fallthrough to the next instruction
            -the immediate of the jump instruction, integer div by 4 (for the instr offset, not addr)
      *)(*(Format.printf "JAL inst 0x%lx, rel jump is %d\n" inst (Stdlib.Int32.to_int (Stdlib.Int32.div (imm_of_jtype inst) 4l)));*)
      | 0b1101111l ->
      (None, (equiv_class_targets, [1; Stdlib.Int32.to_int (Stdlib.Int32.div (Disasm.imm_of_jtype inst) 4l)]))::accum
      (* if the opcode is any of the "branch" instructions, which is:
        BEQ BNE BLT BEG BLTU BGEU
        see page 130 of the RISC-V spec
        We add to the policy:
          -None for the input identifier
          -Global constant for the output identifier
          -the list of jump/fallthrough targets (relative distance), which is
            -1, aka fallthrough to the next instruction
            -the immediate of the jump instruction, integer div by 4 (for the instr offset, not addr)
      *)
      | 0b1100011l ->
      (None, (equiv_class_targets, [1; Stdlib.Int32.to_int (Stdlib.Int32.div (Disasm.imm_of_btype inst) 4l)]))::accum
      (* if the opcode isn't a branch instruction, we are only allowed to fallthrough *)
      | _ -> ((Some equiv_class_targets), (equiv_class_targets, [1]))::accum
    )
    [] (* initialize with empty list *)
    int_list_mem (* use the list of int32 numbers *)
  ) in
  pp_policy int_list_mem (List.rev to_return);
  (List.rev to_return)

  (* in ignore (verify_policy_jump_ranges to_return); to_return*)

