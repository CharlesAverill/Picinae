Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_riscv.
Require Import List.

Import RISCVNotations.

Open Scope Z_scope.
Notation "x #<< y" := (Z.shiftl x y) (at level 40, left associativity). (* logical shift-left *)
Notation "x #>> y" := (Z.shiftr x y) (at level 40, left associativity). (* logical shift-right *)
Notation "x #& y" := (Z.land x y) (at level 25, left associativity). (* logical and *)
Notation "x #^ y" := (Z.lxor x y) (at level 25, left associativity). (* logical xor *)
Notation "x #| y" := (Z.lor x y) (at level 25, left associativity). (* logical or *)


(* A CFI policy ascribes the following information to each original instruction:
   (1) an optional "input identifier", which uniquely labels the equivalence
       class of indirect jumps that may target the instruction;
   (2) an "output identifier", which identifies the equivalence class of targets
       to which this instruction is permitted to indirectly jump; and
   (3) a list of permissible "static destinations", which are the relative indexes
       of instructions to which the instruction may directly jump (or fall thru).
   Static destination sets are specified separately from dynamic destination sets
   because the former need not constitute equivalence classes, whereas the latter
   must (for this particular enforcement algorithm). *)
Definition policy := list (option Z * (Z * list Z)).

(* Our rewriter maintains data in the following data structure:
   iid = input identifier (see above), or None if no dynamic jumps may target
         this instruction
   oid = output identifier (see above), which is ignored if this instruction
         is not a dynamic jump
   sd = static destination list for this instruction
   n = original instruction's encoding
   sb = remembers whether we've selected a short (true) or long (false)
        encoding of this instruction after rewriting *)
Inductive instr_data := Data (iid:option Z) (oid:Z) (sd:list Z) (n:Z) (sb:bool).


(* Integer constants (named so they can be changed to int constants during extraction) *)
Definition Z1 := 1.
Definition Z2 := 2.
Definition Z7 := 7.
Definition Z8 := 8.
Definition Z9 := 9.
Definition Z11 := 11.
Definition Z12 := 12.
Definition Z13 := 13.
Definition Z15 := 15.
Definition Z19 := 19.
Definition Z20 := 20.
Definition Z21 := 21.
Definition Z22 := 22.
Definition Z23 := 23.
Definition Z29 := 29.
Definition Z30 := 30.
Definition Z31 := 31.
Definition Z51 := 51.
Definition Z55 := 55.
Definition Z99 := 99.
Definition Z103 := 103.
Definition Z111 := 111.
Definition Z127 := 127.
Definition Z256 := 256.
Definition Z504 := 504.
Definition Z511 := 511.
Definition Z512 := 512.
Definition Z1024 := 1024.
Definition Z_1024 := -1024.
Definition Z2048 := 2048.
Definition Z3968 := 3968.
Definition Z4095 := 4095.
Definition Z4096 := 4096.
Definition Z4195 := 4195.
Definition Z6243 := 6243.
Definition Z8195 := 8195.
Definition Z16435 := 16435.
Definition Z24595 := 24595.
Definition Z261120 := 261120.
Definition Z262144 := 262144.
Definition Z_262144 := -262144.
Definition Z524288 := 524288.
Definition Z1048576 := 1048576. (* 2^20 *)
Definition Z33550463 := 33550463.
Definition Z57696275 := 57696275.
Definition Z133197843 := 133197843.
Definition Z1073741824 := 1073741824. (* 2^30 *)
Definition Z1079005203 := 1079005203.
Definition Z4290801683 := 4290801683.
Definition Z4293918720 := 4293918720.
Definition Z4294963200 := 4294963200. (* 2^32 - 2^12 *)

(* Helper functions to encode/decode branch/jump instruction operands: *)

Definition encode_branch_offset o :=
  ((o #& Z7) #<< Z9) #| ((o #& Z504) #<< Z22) #| ((o #& Z512) #>> Z2) #| ((o #& Z1024) #<< Z21).

Definition decode_branch_offset n :=
  ((n #>> Z9) #& Z7) #| ((n #>> Z22) #& Z504) #| ((n #<< Z2) #& Z512) #| ((n #>> Z21) #& Z1024).

Definition encode_jump_offset o :=
  ((o #& Z511) #<< Z22) #| ((o #& Z512) #<< Z11) #| ((o #& Z261120) #<< Z2) #| ((o #& Z262144) #<< Z13).

Definition decode_jump_offset n :=
  ((n #>> Z22) #& Z511) #| ((n #>> Z11) #& Z512) #| ((n #>> Z2) #& Z261120) #| ((n #>> Z13) #& Z262144).

(* Convert a twos complement integer n to a signed integer, where modulus m is the min
   unrepresentable positive int (two's complement representations in [m,2m) are negative). *)
Definition twoscomp m n := if (n <? m) then n else (n - Z2*m).

(* Compute the size of the rewritten instruction block that will replace
   a given instruction during rewriting: *)
Definition newsize d :=
  match d with Data iid _ _ n sb =>
    match iid with None => Z0 | Some _ => Z1 end +
    let op := n #& Z127 in
      if op =? Z23 then (if n #& Z3968 =? Z0 then Z1 else Z2)
      else if op =? Z99 then Z1 + (if sb then Z0 else Z1)
      else if op =? Z103 then Z12 + (if sb then Z0 else Z1)
      else Z1
  end.

Definition sumsizes l := fold_left (fun c d => c + newsize d) l 0.

Fixpoint sum_n_sizes n l b :=
  match l with
  | nil => b
  | d::t => if Z0 <? n then sum_n_sizes (n-Z1) t (b + newsize d) else b
  end.

(* Compute the signed relative index for a rewritten branch/jump target.  Inputs are:
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for the instruction being rewritten
   c = count of instructions within rewritten code block d following the branch/jump
       instruction within the block whose target operand is being computed
   l2 = list of data for instructions following this one (in forward order)
   i = relative index of the original destination (to be converted) *)
Definition newoffset l1 d c l2 i :=
  (if (Z0 <=? i) then sum_n_sizes i (d::l2) Z0 else -(sum_n_sizes (-i) l1 Z0))
  + c - newsize d.

(* Initially we conservatively select a long-jump encoding of all rewritten jumps.
   The following function finds jumps whose destinations are near enough to permit
   a short encoding, and shortens them accordingly.  It can potentially be
   called multiple times on its own output to achieve more compression, though usually
   one call finds almost everything that can be shortened. *)
Fixpoint shrink l1 l2 :=
  match l2 with nil => List.rev l1 | ((Data iid oid sd n b) as d)::t => shrink ((Data iid oid sd n (orb b
    (let op := n #& Z127 in
     if orb (op =? Z99) (op =? Z103) then (* remapped branch or guarded jalr *)
       let o := if op =? Z99 then newoffset l1 d Z1 t (twoscomp Z1024 (decode_branch_offset n))
                             else newoffset l1 d Z2 t (Z.of_nat (length t))
       in andb (Z_1024 <=? o) (o <? Z1024)
     else true (* other instruction (unshrinkable) *)
    )))::l1) t
  end.

(* Generate the tag instruction that implements the "input identifier" in
   the rewritten version of an instruction. *)
Definition newtag d :=
  match d with Data None _ _ _ _ => nil
             | Data (Some iid) _ _ _ _ => (Z55 #| ((iid mod Z1048576) #<< Z12))::nil
  end.

(* Generate a rewritten static jump instruction.  Inputs are:
   rd = link destination register (may be 0)
   o' = desired destination offset (returned by newoffset) *)
Definition newjump rd o' :=
  if andb (Z_262144 <=? o') (o' <? Z262144) then
    Some ((Z111 #| (rd #<< Z7) #| encode_jump_offset (o' mod Z524288))::nil)
  else None.

(* Generate a rewritten static branch.  Inputs:

   l1 = list of data for instructions preceding this one, in reverse order
   d = data for instruction being rewritten
   c = count of instructions within rewritten code block d including and following
       the branch/jump instruction being generated
   l2 = list of data for original instructions following this one (in forward order)
   op = encoding of new branch instruction (target operand will be ignored)
   i = target relative block index of new branch

   If the target is "near" the source, this generates a short-form encoding.
   Otherwise it generates a long encoding that conditionally jumps over a
   long-jump to the target (where the condition is inverted from the original
   instruction being rewritten). *)
Definition newbranch l1 d c l2 op i :=
  match d with Data _ _ _ _ sb =>
    if sb then
      let o' := newoffset l1 d c l2 i in
      if andb (Z_1024 <=? o') (o' <? Z1024) then
        Some (((op #& Z33550463) #| encode_branch_offset (o' mod Z2048))::nil)
      else None
    else match newjump 0 (newoffset l1 d c l2 i) with None => None | Some j =>
      Some ((op #& Z33550463 #^ Z4096 #| Z1024)::j)
    end
  end.

(* Rewrite an indirect jump.  The guard code reads the code bytes at the impending
   target to see whether there is a tag instruction there that matches this
   instruction's "output identifier".  If not, it jumps to the end of the rewritten
   code segment (where there can be an abort handler or nothing, the latter causing
   a segmentation fault).  Otherwise it jumps to the target. *)
Definition newijump l1 d l2 :=
  match d with Data iid oid sd n sb =>
    let rs1 := (n #>> Z15) #& Z31 in
    let tmp1 := if rs1 <? Z31 then Z31 else Z29 in
    let tmp2 := if rs1 =? Z30 then Z29 else Z30 in
    let tmp3 := if Z29 <? rs1 then rs1 else Z29 in
    match newbranch l1 d Z2 l2 (Z4195 #| (tmp1 #<< Z15) #| (tmp2 #<< Z20)) (Z1 + Z.of_nat (List.length l2))
    with None => None | Some br => Some (
      (Z19 #| (tmp3 #<< Z7) #| (rs1 #<< Z15) #| (n #& Z4293918720)):: (* Addi tmp3, rs1, imm *)
      (Z4290801683 #| (tmp3 #<< Z7) #| (tmp3 #<< Z15))::              (* Andi tmp3, tmp3, -4 *)
      (Z8195 #| (tmp1 #<< Z7) #| (tmp3 #<< Z15))::                    (* Lw tmp1, tmp3, 0 *)
      (Z133197843 #| (tmp2 #<< Z7) #| (tmp1 #<< Z15))::               (* Andi tmp2, tmp1, 127 *)
      (Z6243 #| (tmp2 #<< Z15))::                                     (* Bne tmp2, x0, +16 *)
      (Z1079005203 #| (tmp1 #<< Z7) #| (tmp1 #<< Z15))::              (* Srai tmp1, tmp1, 5 *)
      (Z51 #| (tmp3 #<< Z7) #| (tmp3 #<< Z15) #| (tmp1 #<< Z20))::    (* Add tmp3, tmp3, tmp1 *)
      (Z8195 #| (tmp1 #<< Z7) #| (tmp3 #<< Z15))::                    (* Lw tmp1, tmp3, 0 *)
      (Z55 #| (tmp2 #<< Z7) #| ((oid mod Z1048576) #<< Z12))::        (* Lui tmp2, out_id *)
      (Z57696275 #| (tmp2 #<< Z7) #| (tmp2 #<< Z15))::                (* Ori tmp2, tmp2, 55 *)
      (br ++                                                          (* Bne tmp1, tmp2, abort *)
      ((n #& Z4095) #| (tmp3 #<< Z15))::nil))                         (* Jalr rd, tmp3, 0 *)
    end
  end.

(* Test membership of an integer (Z) in a list of numbers. *)
Definition mem z l := if (in_dec Z.eq_dec z l) then true else false.

(* Rewrite an AUIPC instruction, which computes destination addresses for position-
   independent code.  We replace these with a pair of instructions that compute the
   original address that the original code would have computed.  For now, these new
   instructions are not position-independent.  In future they could be made so as
   long as the relative positions of the original and rewritten code sections can
   be fixed and less than 2^32 bytes apart.  Inputs:
   base = original code base address / 4
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for the auipc instruction being rewriten *)
Definition new_auipc base (l1:list instr_data) d :=
  match d with Data _ _ sd n _ =>
    if ((Z0 <=? base) && (mem Z1 sd))%bool then
      if n #& Z3968 =? Z0 then Some (Z16435::nil) (* Xor r0, r0, r0 *)
      else let new_target' := (base + Z.of_nat (length l1)) #<< Z2 + (n #& Z4294963200) in
           (* If low 12-bits become negative, we must add 4096 to upper bytes
            * to compensate *)
           let new_target := if (Z2048 <=? new_target' #& Z4095)
                             then new_target' + Z4096 else new_target' in
           let rd := n #& Z3968 in Some (
        (Z55 #| rd #| (new_target #& Z4294963200))::                  (* Lui rd, new_target[31:12] *)
        (Z19 #| rd #| (rd #<< Z8) #| ((new_target #& Z4095) #<< Z20)) (* Addi rd, rd, new_target[11:0] *)
      ::nil)
    else None
  end.

(* Rewrite an old instruction to a new instruction block.  Inputs:
   base = original code base address / 4
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for instruction being rewritten
   l2 = list of data for instructions following this one (in forward order) *)
Definition newinstr base l1 d l2 :=
  match d with Data _ _ sd n _ =>
    if n <? Z0 then None
    else if n #& Z4095 =? Z55 then (* Lui r0, ... *)
      if mem Z1 sd then Some (Z16435::nil) else None (* Xor r0, r0, r0 *)
    else let op := n #& Z127 in
    if op =? Z23 then new_auipc base l1 d (* Auipc *)
    else if op =? Z99 then (* Bcc *)
      let i := twoscomp Z1024 (decode_branch_offset n) in
      if ((n #& Z256 =? 0) && (mem Z1 sd) && (mem i sd) &&
          (Z0 <=? Z.of_nat (length l1) + i) && (i <=? Z.of_nat (length l2)))%bool
        then newbranch l1 d Z1 l2 n i
      else None
    else if op =? Z103 then newijump l1 d l2 (* Jalr *)
    else if op =? Z111 then (* Jal *)
      let i := twoscomp Z262144 (decode_jump_offset n) in
      if ((mem i sd) && (0 <=? Z.of_nat (length l1) + i) && (i <=? Z.of_nat (length l2)))%bool
        then newjump ((n #>> Z7) #& Z31) (newoffset l1 d Z1 l2 i)
      else None
    else
      if mem Z1 sd then Some (n::nil) else None
  end.

(* Rewrite all instructions in a code section. Inputs:
   base = original code base address / 4
   l' = nil
   l1 = nil
   l2 = list of instruction data (returned by todata) for original code *)
Fixpoint newinstrs base l' l1 l2 {struct l2} :=
  match l2 with nil => Some (rev l') | d::t =>
    match newinstr base l1 d t with None => None | Some x =>
      newinstrs base ((newtag d ++ x)::l') (d::l1) t
    end
  end.

(* Create the jump table that replaces the old code segment. Inputs:
   base = original code base address / 4
   base' = rewritten code base address / 4
   i = 0
   acc = nil
   l2 = list of instruction data (returned by todata) for original code *)
Fixpoint newtable base base' acc i l2 :=
  match l2 with nil => rev acc | d::t =>
    newtable base base' ((base' - base + i) #<< Z7 :: acc) (i + newsize d - Z1) t
  end.

(* Rewrite a code section according to a policy. Inputs:
   pol = the policy specification
   l = the list of 32-bit numbers that comprises the original code
   base = original code base address / 4
   base' = desired base address / 4 of the new code section
   Returns pair: (jump table (replaces old code section), new code) *)
Definition todata x :=
  match x with ((iid,(oid,sd)),n) => Data iid oid sd n false end.
Definition newcode (pol:policy) l base base' :=
  let d := shrink nil (map todata (combine pol l)) in
  (newtable base base' nil 0 d, if sumsizes d <? Z1073741824 - base' then newinstrs base nil nil d else None).

(* need some proof for this *)
Definition mapaddr (pol:policy) l addr :=
  sum_n_sizes addr (shrink nil (map todata (combine pol l))) 0.


(* The following is an example extraction of the above CFI rewriter to OCaml.
   It has two main entry points:

   (1) Call "newcode" to generate new code bytes (which you must load into memory
       at address base') from a list of original code bytes previously located at base.
       New base address base' must NOT be within the original code section, and the
       address immediately after the new code section (i.e., address base' + length(
       newcode pol l base base')) must be either non-executable or contain a trusted
       security-abort subroutine.  (CFI violations get redirected to that address.)

   (2) Call "newtable" to generate the bytes that must replace the original code
       section.  (These implement a lookup table used by the new CFI-protected code
       to preserve good control-flows.)
*)
Require Extraction.
Extraction Language OCaml.
Extract Inductive Z => int [ "0" "" "(~-)" ].
Extract Inductive N => int [ "0" "((+)1)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive prod => "( * )"  [ "(,)" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant Z1 => "1".
Extract Inlined Constant Z2 => "2".
Extract Inlined Constant Z7 => "7".
Extract Inlined Constant Z8 => "8".
Extract Inlined Constant Z9 => "9".
Extract Inlined Constant Z11 => "11".
Extract Inlined Constant Z12 => "12".
Extract Inlined Constant Z13 => "13".
Extract Inlined Constant Z15 => "15".
Extract Inlined Constant Z19 => "19".
Extract Inlined Constant Z20 => "20".
Extract Inlined Constant Z21 => "21".
Extract Inlined Constant Z22 => "22".
Extract Inlined Constant Z23 => "23".
Extract Inlined Constant Z29 => "29".
Extract Inlined Constant Z30 => "30".
Extract Inlined Constant Z31 => "31".
Extract Inlined Constant Z51 => "51".
Extract Inlined Constant Z55 => "55".
Extract Inlined Constant Z99 => "99".
Extract Inlined Constant Z103 => "103".
Extract Inlined Constant Z111 => "111".
Extract Inlined Constant Z127 => "127".
Extract Inlined Constant Z256 => "256".
Extract Inlined Constant Z504 => "504".
Extract Inlined Constant Z511 => "511".
Extract Inlined Constant Z512 => "512".
Extract Inlined Constant Z1024 => "1024".
Extract Inlined Constant Z_1024 => "(-1024)".
Extract Inlined Constant Z2048 => "2048".
Extract Inlined Constant Z3968 => "3968".
Extract Inlined Constant Z4095 => "4095".
Extract Inlined Constant Z4096 => "4096".
Extract Inlined Constant Z4195 => "4195".
Extract Inlined Constant Z6243 => "6243".
Extract Inlined Constant Z8195 => "8195".
Extract Inlined Constant Z16435 => "16435".
Extract Inlined Constant Z24595 => "24595".
Extract Inlined Constant Z261120 => "261120".
Extract Inlined Constant Z262144 => "262144".
Extract Inlined Constant Z_262144 => "(-262144)".
Extract Inlined Constant Z524288 => "524288".
Extract Inlined Constant Z1048576 => "1048576".
Extract Inlined Constant Z33550463 => "33550463".
Extract Inlined Constant Z57696275 => "57696275".
Extract Inlined Constant Z133197843 => "133197843".
Extract Inlined Constant Z1073741824 => "1073741824".
Extract Inlined Constant Z1079005203 => "1079005203".
Extract Inlined Constant Z4290801683 => "4290801683".
Extract Inlined Constant Z4293918720 => "4293918720".
Extract Inlined Constant Z4294963200 => "4294963200".
Extract Inlined Constant Z.opp => "(~-)".
Extract Inlined Constant Z.ltb => "(<)".
Extract Inlined Constant Z.leb => "(<=)".
Extract Inlined Constant Z.add => "(+)".
Extract Inlined Constant Z.sub => "(-)".
Extract Inlined Constant Z.mul => "( * )".
Extract Inlined Constant Z.modulo => "(mod)".
Extract Inlined Constant Z.shiftl => "(lsl)".
Extract Inlined Constant Z.shiftr => "(lsr)".
Extract Inlined Constant Z.land => "(land)".
Extract Inlined Constant Z.lor => "(lor)".
Extract Inlined Constant Z.lxor => "(lxor)".
Extract Inlined Constant Z.eqb => "(=)".
Extract Inlined Constant length => "List.length".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant fold_left => "(fun f l a -> List.fold_left f a l)".
Extract Inlined Constant mem => "List.mem".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant combine => "List.combine".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extraction policy.
Extraction instr_data.
Extraction twoscomp.
Extraction newsize.
Extraction sumsizes.
Extraction sum_n_sizes.
Extraction newoffset.
Extraction decode_branch_offset.
Extraction decode_jump_offset.
Extraction shrink.
Extraction newtag.
Extraction encode_jump_offset.
Extraction newjump.
Extraction encode_branch_offset.
Extraction newbranch.
Extraction newijump.
Extraction new_auipc.
Extraction newinstr.
Extraction newinstrs.
Extraction newtable.
Extraction todata.
Extraction newcode.
Extraction mapaddr.
