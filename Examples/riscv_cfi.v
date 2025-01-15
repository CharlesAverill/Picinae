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

(* Now we define "soundness" of a CFI implementation.  Soundness is unavoidably
   parameterized by a (not necessarily one-to-one) mapping from the rewritten
   instructions to the original instructions, since the policy specifies which
   original instructions may flow to which, but the policy must be enforced on
   a different set of (rewritten) instructions.  For our CFI implementation, we
   specify this mapping as the "indexmap" function defined below: *)

Fixpoint indexmap' (l': list (list Z)) i' :=
  (match l' with nil => O | b::t =>
     if i' <? length b then O else S (indexmap' t (i' - length b))
   end)%nat.

Definition indexmap pol l bi bi' i' :=
  match newcode pol l (Z.of_nat bi) (Z.of_nat bi') with (_,None) => O | (_,Some l') => indexmap' l' i' end.


(* We define "safety" as a proposition on policies satisfied by an
   arbitrary indexmap and rewriter function r: *)

Definition blockboundary (l': list (list Z)) i' :=
  exists n, i' = length (concat (firstn n l')).

(* Policy pol permits the original instruction at index i to transfer control to the
   original instruction at index i' if:
   (a) relative index (i' - i) is in the list of static destinations for i, or
   (b) i' is labeled with the equivalence class of dynamic targets for i.  *)
Definition policytarget (pol:policy) i i' :=
  match nth_error pol i with
  | Some (_,(oid,sd)) =>
      In (Z.of_nat i' - Z.of_nat i) sd \/
      exists iid' x, nth_error pol i' = Some (Some iid',x) /\ eqm (2^20) oid iid'
  | None => False
  end.

Open Scope N. 
Definition safety (pol:policy) r im :=
  forall (l jmptbl: list Z) l' s0 m0 bi bi' j0 t s s' q j j' x

    (* Let l' be the rewritten code returned by rewriter r. *)
    (NC: r l (Z.of_nat bi) (Z.of_nat bi') = (jmptbl, Some l'))

    (* Let (4*j,s)::t be a trace that starts at index bi'+j0 in initial state s0. *)
    (ENTRY: startof t (Addr (4 * N.of_nat j), s) = (Addr (4 * N.of_nat (bi'+j0)), s0))
    (XP: exec_prog rv_prog ((Addr (4 * N.of_nat j),s)::t))

    (* Let m0 be the starting memory contents. *)
    (S0: s0 V_MEM32 = VaM m0 32)

    (* Assume m0 contains the rewritten code starting at instruction index i *)
    (CS: forall i n, nth_error (concat l') i = Some n ->
                     getmem 32 LittleE 4 m0 (4 * N.of_nat (bi'+i)) = Z.to_N n)

    (* Assume the code section remains non-writable. *)
    (NWC: forall t x s m w i, exec_prog rv_prog ((x,s)::t) ->
                              s V_MEM32 = VaM m w -> (i < length (concat l'))%nat ->
            getmem 32 LittleE 4 m (4 * N.of_nat i) = getmem 32 LittleE 4 m0 (4 * N.of_nat i))

    (* Assume memory outside the code section remains non-executable. *)
    (NXD: forall t x s e w i, exec_prog rv_prog ((x,s)::t) ->
                              s A_EXEC = VaM e w -> (i < bi' \/ bi' + length (concat l') <= i)%nat ->
            (e (4 * N.of_nat i) = 0)%N)

    (* Assume execution of the new code begins at index j0, which is a block boundary. *)
    (BB: blockboundary l' j0)

    (* Let q be the IL statement that encodes the instruction at index j. *)
    (LU: (rv_prog s (4 * N.of_nat j) = Some (4,q))%N)

    (* Let s' and x be the store and exit state after executing q. *)
    (XS: exec_stmt s q s' x)

    (* Let j' be the index of the instruction to which q transfers control next. *)
    (EX: exitof (4 * N.of_nat (S j)) x = Addr (4 * N.of_nat j')),

  (* Then either
      (a) j and j' are within a common rewritten block (i.e., an IRM-added branch),
      (b) edge (j,j') is explicitly permitted by the policy, or
      (c) j' is the security abort handler appended to the rewritten code. *)
  (im l bi bi' (j-bi') = im l bi bi' (j'-bi') \/
   (blockboundary l' (j'-bi') /\ policytarget pol (im l bi bi' (j-bi')) (im l bi bi' (j'-bi'))) \/
   j' < bi' \/ bi' + length (concat l') <= j')%nat.
Close Scope N.



Tactic Notation "ereplace" constr(t) :=
  lazymatch type of t with ?T => evar T;
    lazymatch goal with x := _ |- _ => let TMP := fresh in
      enough (TMP: t = x); [rewrite TMP; clear TMP |]; subst x
    end
  end.

Tactic Notation "ereplace" constr(t) "in" hyp(H) :=
  lazymatch type of t with ?T => evar T;
    lazymatch goal with x := _ |- _ => let TMP := fresh in
      enough (TMP: t = x); [rewrite TMP in H; clear TMP |]; subst x
    end
  end.

Ltac unfold_consts := unfold
  Z1, Z2, Z7, Z8, Z9, Z11, Z12, Z13, Z15, Z19, Z20, Z21, Z22, Z23, Z29, Z30, Z31, Z51, Z55, Z99,
  Z103, Z111, Z127, Z256, Z504, Z511, Z512, Z1024, Z_1024, Z2048, Z3968, Z4095, Z4096, Z4195,
  Z6243, Z8195, Z16435, Z24595, Z261120, Z262144, Z_262144, Z524288, Z33550463, Z57696275,
  Z133197843, Z1079005203, Z4290801683, Z4293918720, Z4294963200
.
Tactic Notation "unfold_consts" "in" hyp(H) := unfold
  Z1, Z2, Z7, Z8, Z9, Z11, Z12, Z13, Z15, Z19, Z20, Z21, Z22, Z23, Z29, Z30, Z31, Z51, Z55, Z99,
  Z103, Z111, Z127, Z256, Z504, Z511, Z512, Z1024, Z_1024, Z2048, Z3968, Z4095, Z4096, Z4195,
  Z6243, Z8195, Z16435, Z24595, Z261120, Z262144, Z_262144, Z524288, Z33550463, Z57696275,
  Z133197843, Z1079005203, Z4290801683, Z4293918720, Z4294963200
in H.

Lemma invSome: forall A (x y:A), Some x = Some y -> x = y.
Proof. intros. injection H. trivial. Qed.

Lemma invPair: forall A B (a a':A) (b b':B), (a,b)=(a',b') -> a=a' /\ b=b'.
Proof. intros. inversion H. split; reflexivity. Qed.

Lemma invAddr: forall x y, Addr x = Addr y -> x = y.
Proof. intros. injection H. trivial. Qed.

Lemma invCons:
  forall A (h1 h2:A) t1 t2, h1::t1 = h2::t2 -> h1 = h2 /\ t1 = t2.
Proof. intros. inversion H. split; reflexivity. Qed.

Lemma invVaN:
  forall (n1:N) w1 n2 w2, VaN n1 w1 = VaN n2 w2 -> n1=n2 /\ w1=w2.
Proof. intros. inversion H. split; reflexivity. Qed.

Lemma Nat_sub_sub_distr:
  forall m n p, (p <= n -> n - p <= m -> m - (n - p) = m + p - n)%nat.
Proof.
  intros.
  eapply (proj1 (Nat.add_cancel_r _ _ _)).
  rewrite Nat.sub_add by assumption.
  rewrite Nat.add_sub_assoc by assumption.
  rewrite Nat.sub_add by (apply Nat.le_sub_le_add_r; assumption).
  rewrite Nat.add_sub. reflexivity.
Qed.

Lemma Nat_sub_sub_cancel:
  forall m n, (m <= n -> n - (n - m) = m)%nat.
Proof.
  intros.
  rewrite Nat_sub_sub_distr, Nat.add_comm. apply Nat.add_sub. assumption. apply Nat.le_sub_l.
Qed.

Lemma N_shiftl_land_0:
  forall x y z, (z < (1 << y) -> ((x << y) .& z) = 0)%N.
Proof.
  intros. rewrite <- (N.mod_small _ _ H), !N.shiftl_mul_pow2, N.mul_1_l.
  rewrite <- N.land_ones, (N.land_comm z), N.land_assoc, N.land_ones, N.mod_mul.
    reflexivity. apply N.pow_nonzero. discriminate.
Qed.

Lemma shiftr_land_shiftl:
  forall a b c d, (b <= d -> ((a>>b) .& c) << d = (a .& (c << b)) << (d-b))%N.
Proof.
  intros.
  rewrite <- (N.lor_ldiff_and (a .& (c<<b)) (N.ones b)), <- N.land_assoc, N.land_ones.
  rewrite (N.shiftl_mul_pow2 c b) at 2.
  rewrite N.Div0.mod_mul by (apply N.pow_nonzero; discriminate).
  rewrite N.land_0_r, N.lor_0_r, N.ldiff_ones_r, N.shiftl_shiftl, N.add_comm, N.sub_add by assumption.
  rewrite (N.shiftr_land a), N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r; reflexivity.
Qed.

Lemma Z_lxor_land_distr_l:
  forall x y z, (x #^ y) #& z = (x #& z) #^ (y #& z).
Proof.
  intros. apply Z.bits_inj. intro n. rewrite Z.lxor_spec, !Z.land_spec, Z.lxor_spec.
  destruct (Z.testbit z n).
    rewrite !Bool.andb_true_r. reflexivity.
    rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma N_lxor_land_distr_l:
  forall x y z, (x .^ y) .& z = (x .& z) .^ (y .& z).
Proof.
  intros. apply N.bits_inj. intro n. rewrite N.lxor_spec, !N.land_spec, N.lxor_spec.
  destruct (N.testbit z n).
    rewrite !Bool.andb_true_r. reflexivity.
    rewrite !Bool.andb_false_r. reflexivity.
Qed.

Lemma Nat2Z2N:
  forall n, Z.to_N (Z.of_nat n) = N.of_nat n.
Proof.
  intro. rewrite <- nat_N_Z. apply N2Z.id.
Qed.

Lemma Z2N_lt:
  forall n m, 0 < m -> n < m -> (Z.to_N n < Z.to_N m)%N.
Proof.
  intros. destruct n.
    apply Z2N.inj_lt. reflexivity. apply Z.lt_le_incl. assumption. assumption.
    apply Z2N.inj_lt. discriminate. apply Z.lt_le_incl. assumption. assumption.
    destruct m. discriminate. reflexivity. discriminate.
Qed.

Lemma Z2Nat_le:
  forall n m, n <= m -> (Z.to_nat n <= Z.to_nat m)%nat.
Proof.
  intros. destruct n, m; try (reflexivity + contradiction + apply Nat.le_0_l).
  apply Z2Nat.inj_le. discriminate. discriminate. assumption.
Qed.

Lemma Nat2N_le:
  forall n m, (n <= m)%nat <-> (N.of_nat n <= N.of_nat m)%N.
Proof.
  split; intro H.

    apply N.leb_le. unfold N.leb. apply nat_compare_le in H. rewrite <- Nat2N.inj_compare.
    destruct (n ?= m)%nat; (reflexivity + contradiction).

    apply N.leb_le in H. unfold N.leb in H. rewrite <- Nat2N.inj_compare in H.
    apply nat_compare_le. destruct (n ?= m)%nat; (reflexivity + discriminate).
Qed.

Lemma N2Nat_le:
  forall n m, (n <= m)%N <-> (N.to_nat n <= N.to_nat m)%nat.
Proof.
  split; intro H.
    apply Nat2N_le. rewrite !N2Nat.id. assumption.
    apply Nat2N_le in H. rewrite !N2Nat.id in H. assumption.
Qed.

Lemma Nat2N_lt:
  forall n m, (n < m)%nat <-> (N.of_nat n < N.of_nat m)%N.
Proof.
  split; intro H.
    apply N.le_succ_l, N2Nat_le. rewrite N2Nat.inj_succ, !Nat2N.id. assumption.
    apply N.le_succ_l, N2Nat_le in H. rewrite N2Nat.inj_succ, !Nat2N.id in H. assumption.
Qed.

Lemma N2Nat_lt:
  forall n m, (n < m)%N <-> (N.to_nat n < N.to_nat m)%nat.
Proof.
  intros. split; intro H.
    apply N.le_succ_l, N2Nat_le in H. rewrite N2Nat.inj_succ in H. assumption.
    apply N.le_succ_l, N2Nat_le. rewrite N2Nat.inj_succ. assumption.
Qed.

Lemma Z2N_land_r:
  forall x y, 0 <= y -> Z.to_N (x #& y) = Z.to_N (x #& y) .& Z.to_N y.
Proof.
  intros. rewrite <- Z2N_inj_land.
    rewrite <- Z.land_assoc, Z.land_diag. reflexivity.
    apply Z.land_nonneg. right. assumption.
    assumption.
Qed.

Lemma N2Z_inj_sub_le:
  forall n m, (Z.of_N n - Z.of_N m <= Z.of_N (n - m))%Z.
Proof.
  intros. edestruct N.le_ge_cases.
    rewrite (proj2 (N.sub_0_le _ _) H). apply Z.le_sub_0, N2Z.inj_le, H.
    rewrite N2Z.inj_sub by apply H. reflexivity.
Qed.

Lemma Z_ones_nonneg:
  forall z, 0 <= z -> 0 <= Z.ones z.
Proof.
  intros. rewrite Z.ones_equiv. apply Zlt_0_le_0_pred, Z.pow_pos_nonneg. reflexivity. assumption.
Qed.

Lemma Nat_squeeze:
  forall n m (LO: (m <= n)%nat) (HI: (n < m+1)%nat),
  n = m.
Proof.
  intros. apply Nat.le_antisymm.
    apply Nat.lt_succ_r. rewrite <- Nat.add_1_r. exact HI.
    exact LO.
Qed.

Lemma le_lt_S: forall x y z, (x <= y < z -> S x <= S y < S z)%nat.
Proof. intros. split. apply le_n_S, H. apply -> Nat.succ_lt_mono. apply H. Qed.

Lemma le_pmr: forall n m, (n <= m -> n + (m - n) = m)%nat.
Proof. intros. rewrite Nat.add_comm. apply Nat.sub_add, H. Qed.

Lemma nth_error_cons:
  forall A (h:A) t n, nth_error (h::t) n = match n with O => Some h | S m => nth_error t m end.
Proof. destruct n; reflexivity. Qed.

Lemma nth_skipn:
  forall {A} i (l:list A), nth_error l i = hd_error (skipn i l).
Proof.
  induction i; intros; destruct l; (reflexivity + apply IHi).
Qed.

Lemma skipn_S:
  forall {A} i (l:list A), skipn (S i) l = tl (skipn i l).
Proof.
  induction i; intros.
    reflexivity.
    destruct l. reflexivity. apply IHi.
Qed.

Lemma nth_error_last:
  forall A (l:list A), hd_error (rev l) = nth_error l (pred (length l)).
Proof.
  intros. rewrite <- rev_length. rewrite <- (rev_involutive l) at 2.
  generalize (rev l). clear l. intro l. destruct l.
    reflexivity.
    simpl. rewrite nth_error_app2.
      rewrite rev_length, Nat.sub_diag. reflexivity.
      rewrite rev_length. reflexivity.
Qed.

Theorem firstn_last:
  forall A (l:list A) n,
  firstn (S n) l = firstn n l ++ match nth_error l n with None => nil | Some x => x::nil end.
Proof.
  induction l; intros.
    destruct n; reflexivity.
    simpl. destruct n.
      reflexivity.
      rewrite IHl. reflexivity.
Qed.

Corollary firstn_app_nth:
  forall A (l:list A) n x, nth_error l n = Some x ->
  firstn n l ++ (x::nil) = firstn (S n) l.
Proof.
  intros. ereplace (x::nil). symmetry. apply firstn_last. rewrite H. reflexivity.
Qed.

Theorem combine_app:
  forall {A} (l1 l2 l3 l4:list A) (LEN: length l1 = length l3),
  combine (l1++l2) (l3++l4) = (combine l1 l3) ++ (combine l2 l4).
Proof.
  induction l1; intros.
    destruct l3. reflexivity. discriminate.
    destruct l3.
      discriminate.
      simpl. rewrite IHl1.
        reflexivity.
        inversion LEN. reflexivity.
Qed.

Theorem combine_nth_error:
  forall {A} (x y:A) (l1 l2:list A) n
         (NTH1: nth_error l1 n = Some x) (NTH2: nth_error l2 n = Some y),
  In (x,y) (combine l1 l2).
Proof.
  induction l1; intros.
    destruct n; discriminate.
    destruct l2.
      destruct n; discriminate.
      destruct n.
        inversion NTH1. inversion NTH2. apply in_eq.
        right. eapply IHl1. apply NTH1. apply NTH2.
Qed.

Theorem rev_combine:
  forall {A} (l1 l2:list A) (LEN: length l1 = length l2),
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  induction l1; intros.
    reflexivity.
    destruct l2.
      destruct (rev (_::_)); reflexivity.
      simpl. inversion LEN. rewrite IHl1, combine_app by (rewrite ?rev_length; assumption). reflexivity.
Qed.

Lemma nth_error_map:
  forall {A B} (f:A->B) (l:list A) n,
  nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  induction l; intros; destruct n; try reflexivity. apply IHl.
Qed.

Lemma nth_error_combine:
  forall {A B} (l1:list A) (l2:list B) n,
  nth_error (combine l1 l2) n = match nth_error l1 n, nth_error l2 n with
                                | Some x, Some y => Some (x,y)
                                | _, _ => None
                                end.
Proof.
  induction l1; intros.
    destruct n; reflexivity.
    destruct l2.
      destruct n. reflexivity. simpl. destruct nth_error; reflexivity.
      destruct n.
        reflexivity.
        simpl. apply IHl1.
Qed.

Lemma length_cons: forall A (h:A) t, length (h::t) = S (length t).
Proof. reflexivity. Qed.

Theorem length_skipn_le_S:
  forall A (l: list A) n, (length (skipn (S n) l) <= length (skipn n l))%nat.
Proof.
  induction l; intro.
    apply Nat.le_0_l.
    simpl. destruct n. apply Nat.le_succ_diag_r. apply IHl.
Qed.

Lemma firstn_cons_skipn:
  forall A (x:A) (l:list A) n, nth_error l n = Some x -> firstn n l++x::skipn (S n) l = l.
Proof.
  intros.
  change (x::_) with (match Some x with Some x => x::nil | None => nil end++skipn (S n) l).
  rewrite <- H, app_assoc, <- firstn_last. apply firstn_skipn.
Qed.

Lemma rev_firstn:
  forall A n (l:list A), rev (firstn n l) = skipn (length l - n) (rev l).
Proof.
  intros.
  rewrite <- (rev_involutive l) at 1. rewrite <- rev_length. generalize (rev l). clear l. intro l.
  destruct (Nat.le_ge_cases (length l) n).

    rewrite firstn_all2, rev_involutive by (rewrite rev_length; assumption).
    rewrite (proj2 (Nat.sub_0_le _ _)) by assumption.
    reflexivity.

    replace n with (length l - (length l - n))%nat at 1 by apply Nat_sub_sub_cancel, H.
    generalize (length l - n)%nat. clear n H. intro n. revert l. induction n; intro.
      rewrite Nat.sub_0_r, <- rev_length, firstn_all. apply rev_involutive.
      destruct l.
        reflexivity.
        simpl. rewrite firstn_app, (proj2 (Nat.sub_0_le (_-_) _)), app_nil_r.
          apply IHn.
          rewrite rev_length. apply Nat.le_sub_l.
Qed.

Corollary skipn_all:
  forall A (l:list A), skipn (length l) l = nil.
Proof.
  intros.
  rewrite <- (rev_involutive l), rev_length, <- (Nat.sub_0_r (length _)), <- rev_firstn.
  reflexivity.
Qed.

Theorem skipn_all2:
  forall A n (l:list A), (length l <= n)%nat -> skipn n l = nil.
Proof.
  induction n; intros.
    destruct l. reflexivity. contradict H. apply Nat.nle_succ_0.
    destruct l. reflexivity. apply IHn, le_S_n, H.
Qed.

Theorem skipn_length:
  forall A (l:list A) n, length (skipn n l) = (length l - n)%nat.
Proof.
  intros. symmetry. destruct (Nat.le_ge_cases (length l) n).
    rewrite skipn_all2 by assumption. apply Nat.sub_0_le. assumption.
    rewrite <- (firstn_skipn n l) at 1. rewrite app_length, firstn_length_le by assumption.
      rewrite (Nat.add_comm n). apply Nat.add_sub.
Qed.

Lemma concat_last:
  forall A l (x:list A), concat l ++ x = concat (l++(x::nil)).
Proof.
  intros. rewrite concat_app, concat_cons, app_nil_r. reflexivity.
Qed.

Lemma Forall_tail:
  forall {A} P (h:A) t, Forall P (h::t) -> Forall P t.
Proof. intros. inversion H. assumption. Qed.

Lemma Forall_app:
  forall A P (l1 l2: list A), Forall P l1 -> Forall P l2 -> Forall P (l1 ++ l2).
Proof.
  intros. apply Forall_forall. intros. apply in_app_or in H1. destruct H1.
    revert H x H1. apply Forall_forall.
    revert H0 x H1. apply Forall_forall.
Qed.

Lemma Forall_concat:
  forall A (P: A -> Prop) l, Forall (Forall P) l -> Forall P (concat l).
Proof.
  induction l; intro.
    apply Forall_nil.
    rewrite concat_cons. apply Forall_app.
      eapply Forall_inv, H.
      eapply IHl, Forall_tail, H.
Qed.

Lemma Forall_rev:
  forall A (P: A -> Prop) l, Forall P l -> Forall P (rev l).
Proof.
  intros. apply Forall_forall. intros. apply in_rev in H0. exact (proj1 (Forall_forall _ l) H x H0).
Qed.

Theorem strong_induction:
  forall (P:nat->Prop) (IC: forall n1 (IH: forall n0 (DEC: (n0<n1)%nat), P n0), P n1),
  forall n, P n.
Proof.
  refine (well_founded_ind _).
  intro y. induction y; apply Acc_intro; intros x DEC; inversion DEC.
    subst x. assumption.
    apply (Acc_inv IHy). assumption.
Qed.

Lemma Z_hibits_zero:
  forall n w, 0 <= w ->
    (forall b, w<=b -> Z.testbit n b = false) ->
  0 <= n < 2^w.
Proof.
  intros. split.

    intro H1. apply Z.compare_gt_iff in H1. apply Z.bits_iff_neg_ex in H1. destruct H1.
    specialize (H1 (Z.max w (Z.succ x))).
    specialize (H0 (Z.max w (Z.succ x)) (Z.le_max_l _ _)). rewrite H1 in H0. discriminate.
    eapply Z.lt_le_trans. apply Z.lt_succ_diag_r. apply Z.le_max_r.

    destruct n.
      apply Z.pow_pos_nonneg. reflexivity. assumption.
      apply Z.log2_lt_pow2.
        reflexivity.

        assert (H1: Z.pos p = 0 \/ 0 < Z.pos p /\ Z.log2 (Z.pos p) < w).
          apply Z.shiftr_eq_0_iff, Z.bits_inj_0. intro n. destruct (Z.neg_nonneg_cases n).
            apply Z.testbit_neg_r. assumption.
            rewrite Z.shiftr_spec by assumption. apply H0. change w with (0+w) at 1. apply Z.add_le_mono_r. assumption.
        destruct H1. discriminate. apply H1.

      transitivity 0. reflexivity. apply Z.pow_pos_nonneg. reflexivity. assumption.
Qed.

Lemma Z_hibit_clear:
  forall w n b, 0 <= n < 2^w -> w<=b -> Z.testbit n b = false.
Proof.
  intros. destruct n.
    apply Z.bits_0.
    apply Z.bits_above_log2. apply H. apply Z.log2_lt_pow2.
      reflexivity.
      eapply Z.lt_le_trans. apply H. apply Z.pow_le_mono_r. reflexivity. assumption.
    destruct H. exfalso. apply H. reflexivity.
Qed.

Lemma Z_lop_hizero:
  forall w n1 n2 f (W: 0 <= w)
         (Z0: forall x y b (Z1: Z.testbit x b = false) (Z2: Z.testbit y b = false),
              Z.testbit (f x y) b = false)
         (W1: 0 <= n1 < 2^w) (W2: 0 <= n2 < 2^w),
  0 <= f n1 n2 < 2^w.
Proof.
  intros. apply Z_hibits_zero. exact W. intros.
  apply Z0; eapply Z_hibit_clear; eassumption.
Qed.

Lemma Z_lor_bound:
  forall w x y, 0 <= w -> 0 <= x < 2^w -> 0 <= y < 2^w -> 0 <= x #| y < 2^w.
Proof.
  intros. apply Z_lop_hizero; try assumption.
  intros ? ? ? H2 H3. rewrite Z.lor_spec, H2, H3. reflexivity.
Qed.

Lemma Z_land_bound:
  forall w x y, 0 <= w -> 0 <= y < 2^w -> 0 <= x #& y < 2^w.
Proof.
  intros. apply Z_hibits_zero. assumption. intros.
  rewrite Z.land_spec. apply Bool.andb_false_intro2. eapply Z_hibit_clear; eassumption.
Qed.

Ltac Z_nonneg :=
  repeat first [ reflexivity | discriminate 1 | assumption
  | apply Z.lor_nonneg; split
  | apply Z.shiftl_nonneg
  | apply Z.shiftr_nonneg
  | apply Z.land_nonneg; (right + left)
  | apply Z.mod_pos_bound
  | apply N2Z.is_nonneg
  | apply Nat2Z.is_nonneg
  | apply Z.add_nonneg_nonneg ].

Lemma xbits_land_cancel_r:
  forall m n i j, N.ones (j - i) .& m = N.ones (j - i) -> (xbits n i j) .& m = xbits n i j.
Proof.
  intros. unfold xbits. rewrite <- N.land_ones, <- N.land_assoc, H. reflexivity.
Qed.

Lemma xbits_excl_zero:
  forall m n i j, n .& m = 0%N -> xbits m i j = N.ones (j - i) -> xbits n i j = 0%N.
Proof.
  intros. unfold xbits. rewrite <- N.land_ones.
  rewrite <- (N.land_diag (N.ones _)), N.land_assoc. rewrite <- H0 at 2.
  rewrite N.land_ones. fold (xbits n i j). rewrite <- xbits_land, H. apply xbits_0_l.
Qed.

Lemma ebo_bitmask:
  forall o, encode_branch_offset o #& 33550463 = 0.
Proof.
  intro. unfold encode_branch_offset.
  rewrite 3!Z.land_lor_distr_l, 3!Z.shiftl_land, Z.shiftr_land, <- 4!Z.land_assoc, 4!Z.land_0_r.
  reflexivity.
Qed.

Lemma ebo_nonneg:
  forall o, 0 <= encode_branch_offset o.
Proof.
  intros. unfold encode_branch_offset.
  repeat (apply Z.lor_nonneg; split); apply Z.shiftl_nonneg, Z.land_nonneg; right; discriminate.
Qed.

Lemma ejo_nonneg:
  forall o, 0 <= encode_jump_offset o.
Proof.
  intro. unfold encode_jump_offset.
  repeat (apply Z.lor_nonneg; split); apply Z.shiftl_nonneg, Z.land_nonneg; right; discriminate.
Qed.

Lemma newtag_nonneg:
  forall d, Forall (Z.le 0) (newtag d).
Proof.
  unfold newtag. destruct d, iid.
    apply Forall_cons. Z_nonneg. apply Forall_nil.
    apply Forall_nil.
Qed.

Lemma newjump_nonneg:
  forall rd o' l' (NJ: newjump rd o' = Some l'), 0 <= rd -> Forall (Z.le 0) l'.
Proof.
  intros. unfold newjump in NJ. destruct andb; [|discriminate]. apply invSome in NJ. subst l'.
  apply Forall_cons. apply Z.lor_nonneg. split. apply Z.lor_nonneg. split.
    discriminate.
    apply Z.shiftl_nonneg, H.
    apply ejo_nonneg.
    apply Forall_nil.
Qed.

Lemma newbranch_nonneg:
  forall l1 d c l2 op i b (NB: newbranch l1 d c l2 op i = Some b),
  Forall (Z.le 0) b.
Proof.
  intros. destruct d as [iid oid sd n sb].
  unfold newbranch in NB. destruct sb.
    destruct andb; [|discriminate]. apply invSome in NB. subst b. apply Forall_cons.
      apply Z.lor_nonneg. split.
        apply Z.land_nonneg. right. discriminate.
        apply ebo_nonneg.
      apply Forall_nil.
    destruct newjump eqn:NJ; [|discriminate]. apply invSome in NB. subst b. apply Forall_cons.
      apply Z.lor_nonneg. split.
        apply Z.lxor_nonneg. split; intro. discriminate. apply Z.land_nonneg. right. discriminate.
        discriminate.
      eapply newjump_nonneg. exact NJ. reflexivity.
Qed.

Lemma newijump_nonneg:
  forall l1 d l2 b (NI: newijump l1 d l2 = Some b),
  Forall (Z.le 0) b.
Proof.
  intros. destruct d as [iid oid sd n sb].
  unfold newijump in NI.
  set (rs1 := (n #>> 15) #& 31) in NI.
  set (tmp1 := if rs1 <? 31 then 31 else 29) in NI.
  set (tmp2 := if rs1 =? 30 then 29 else 30) in NI.
  set (tmp3 := if 29 <? rs1 then rs1 else 29) in NI.
  assert (0 <= rs1). apply Z.land_nonneg. right. discriminate.
  assert (0 <= tmp1). destruct (rs1 <? 31); discriminate.
  assert (0 <= tmp2). destruct (rs1 =? 30); discriminate.
  assert (0 <= tmp3). destruct (29 <? rs1) eqn:H2.
    etransitivity; [| apply Z.lt_le_incl, Z.ltb_lt, H2 ]. discriminate. discriminate.
  destruct newbranch eqn:NB; [|discriminate].
  apply invSome in NI. subst b.
  repeat (apply Forall_cons + apply Forall_app); repeat (apply Z.lor_nonneg; split); first
  [ discriminate
  | apply Z.shiftl_nonneg; (assumption || apply Z.mod_pos_bound; reflexivity)
  | apply Z.land_nonneg; right; discriminate
  | idtac ].
  eapply newbranch_nonneg. exact NB.
  apply Forall_nil.
Qed.

Lemma newauipc_nonneg:
  forall base l1 d b (NI: new_auipc base l1 d = Some b), Forall (Z.le 0) b.
Proof.
  unfold new_auipc. intros. destruct d as [iid oid sd n sb].
  destruct (_ && _)%bool.
    destruct (_ =? 0).
      apply invSome in NI. subst b. apply Forall_cons. discriminate 1. apply Forall_nil.
      apply invSome in NI. subst b. do 2 (apply Forall_cons; Z_nonneg). apply Forall_nil.
    discriminate NI.
Qed.

Lemma newinstr_nonneg:
  forall base l1 d l2 b, newinstr base l1 d l2 = Some b -> Forall (Z.le 0) b.
Proof.
  unfold newinstr. unfold_consts. intros. destruct d as [iid oid sd z sb].
  destruct (z <? 0) eqn:H1; [discriminate|].
  destruct (_ =? 55).
    destruct mem; [|discriminate]. apply invSome in H. subst b.
    apply Forall_cons. discriminate 1. apply Forall_nil.
  destruct (_ =? 23). eapply newauipc_nonneg. exact H.
  destruct (_ =? 99).
    destruct andb; [|discriminate]. eapply newbranch_nonneg, H.
  destruct (_ =? 103). eapply newijump_nonneg, H.
  destruct (_ =? 111).
    destruct andb; [|discriminate]. eapply newjump_nonneg. exact H. apply Z.land_nonneg. right. discriminate.
  destruct mem; [|discriminate].
  apply invSome in H. subst b. apply Forall_cons.
    apply Z.ltb_ge, H1.
    apply Forall_nil.
Qed.

Lemma newinstrs_nonneg:
  forall base l1 l2 l', newinstrs base nil l1 l2 = Some l' -> Forall (Forall (Z.le 0)) l'.
Proof.
  intros base l1 l2 l'. assert (H:=Forall_nil (Forall (Z.le 0))). revert l1 l' H. generalize (@nil (list Z)) as acc.
  induction l2; intros.
    apply invSome in H0. subst l'. apply Forall_rev, H.

    unfold newinstrs in H0; fold newinstrs in H0. destruct newinstr eqn:NI; [|discriminate].
    apply IHl2 in H0. exact H0. apply Forall_cons.
      apply Forall_app. apply newtag_nonneg. eapply newinstr_nonneg, NI.
      exact H.
Qed.

Lemma newinstr_nonnil:
  forall base l1 d l2, newinstr base l1 d l2 <> Some nil.
Proof.
  intros. destruct d. unfold newinstr.
  destruct (_ <? 0). discriminate 1.
  destruct (_ =? _). destruct mem; discriminate.
  destruct (_ =? _). unfold new_auipc.
    destruct (_ && _)%bool.
      destruct (_ =? _); discriminate 1.
      discriminate 1.
  destruct (_ =? _). destruct andb; [|discriminate]. unfold newbranch. destruct sb.
    destruct andb; discriminate.
    destruct newjump; discriminate.
  destruct (_ =? _). unfold newijump.
    destruct newbranch; discriminate.
  destruct (_ =? _). destruct andb; [|discriminate]. unfold newjump. destruct andb; discriminate.
  destruct mem; discriminate.
Qed.

Lemma newsize_pos:
  forall d, 1 <= newsize d.
Proof.
  destruct d. unfold newsize.
  destruct iid; repeat destruct (_ =? _); try destruct sb; discriminate.
Qed.

Definition optcons {A} (oh: option A) ot :=
  match oh with None => None | Some h => option_map (cons h) ot end.

Definition optlist {A} := fold_right optcons (Some (@nil A)).

Fixpoint newinstrs' base l1 l2 {struct l2} :=
  match l2 with nil => nil | d::t =>
    (option_map (app (newtag d)) (newinstr base l1 d t)) :: newinstrs' base (d::l1) t
  end.

Lemma newinstrs_newinstrs':
  forall base l' l1 l2,
  newinstrs base l' l1 l2 = optlist (map Some (rev l') ++ newinstrs' base l1 l2).
Proof.
  intros. revert l' l1. induction l2; intros.
    rewrite app_nil_r. simpl. induction (rev l').
      reflexivity.
      simpl. rewrite <- IHl. reflexivity.
    simpl. destruct newinstr.
      rewrite IHl2. simpl. rewrite map_app, <- app_assoc. reflexivity.
      unfold optlist. rewrite fold_right_app. simpl. induction map.
        reflexivity.
        simpl. rewrite <- IHl. destruct a0; reflexivity.
Qed.

Lemma nth_newinstrs:
  forall base l1 l2 l' i (NIS: newinstrs base nil l1 l2 = Some l'),
  nth_error l' i = match nth_error l2 i with None => None | Some d =>
    option_map (app (newtag d))
               (newinstr base (rev (firstn i l2) ++ l1) d (skipn (S i) l2))
  end.
Proof.
  intros base l1 l2 l'. rewrite newinstrs_newinstrs', app_nil_l. revert base l1 l'. induction l2; intros.
    apply invSome in NIS. subst l'. destruct i; reflexivity.
    simpl. destruct i; simpl; simpl in NIS.
      destruct newinstr; [destruct optlist|]; [|discriminate..]. apply invSome in NIS. subst l'. reflexivity.
      destruct l'.
        destruct option_map; [destruct optlist|]; discriminate.
        erewrite IHl2.
          rewrite <- app_assoc. reflexivity.
          simpl. destruct optlist; [destruct newinstr|destruct option_map]; try discriminate NIS. apply invSome, invCons, proj2 in NIS. subst l'. reflexivity.
Qed.

Lemma newinstrs_nonnil:
  forall base l1 l2 l' n, newinstrs base nil l1 l2 = Some l' -> nth_error l' n <> Some nil.
Proof.
  intros.
  erewrite nth_newinstrs by exact H.
  destruct nth_error; [|discriminate].
  destruct newinstr eqn:H1; [|discriminate].
  simpl. intro H2. inversion H2. apply app_eq_nil, proj2 in H3. subst.
  revert H1. apply newinstr_nonnil.
Qed.

Lemma indexmap_0:
  forall l, hd_error l <> Some nil -> indexmap' l O = O.
Proof.
  intros. destruct l as [|h t].
    reflexivity.
    destruct h. contradiction. reflexivity.
Qed.

Lemma indexmap_sum:
  forall l n i (LEN: (n <= length l)%nat),
  (indexmap' l (length (concat (firstn n l)) + i) = n + indexmap' (skipn n l) i)%nat.
Proof.
  induction l; intros.
    apply Nat.le_0_r in LEN. subst. reflexivity.
    destruct n.
      reflexivity.

      rewrite Nat.add_succ_l, <- IHl by apply le_S_n, LEN.
      simpl. rewrite app_length, <- Nat.add_assoc.
      rewrite (proj2 (Nat.ltb_ge _ _)) by apply Nat.le_add_r.
      rewrite Nat.add_comm, Nat.add_sub. reflexivity.
Qed.

Lemma indexmap_inv:
  forall {base l1 l2 l'} n (NC: newinstrs base nil l1 l2 = Some l') (LEN: (n <= length l')%nat),
  (indexmap' l' (length (concat (firstn n l'))) = n)%nat.
Proof.
  intros.
  rewrite <- (Nat.add_0_r (length _)), indexmap_sum by exact LEN.
  rewrite indexmap_0. apply Nat.add_0_r.
  rewrite <- nth_skipn. eapply newinstrs_nonnil, NC.
Qed.

Lemma indexmap_length:
  forall l n i,
  (indexmap' l (length (concat (firstn n l)) + i) = Nat.min n (length l) + indexmap' (skipn n l) i)%nat.
Proof.
  intros. destruct (Nat.le_ge_cases n (length l)).
    rewrite Nat.min_l by apply H. apply indexmap_sum, H.
    replace (skipn n l) with (skipn (length l) l). replace (firstn n l) with (firstn (length l) l).
      rewrite Nat.min_r by exact H. apply indexmap_sum. reflexivity.
      symmetry. rewrite firstn_all. apply firstn_all2, H.
      symmetry. rewrite skipn_all. apply skipn_all2, H.
Qed.

Lemma firstn_indexmap_above:
  forall l n, (length (concat (firstn (indexmap' l n) l)) <= n)%nat.
Proof.
  induction l; intro.
    apply Nat.le_0_l.
    unfold indexmap'; fold indexmap'. destruct (_ <? _)%nat eqn:H.
      apply Nat.le_0_l.
      rewrite firstn_cons, concat_cons, app_length. etransitivity.
        apply Nat.add_le_mono_l, IHl.
        rewrite Nat.add_comm, Nat.sub_add by apply Nat.ltb_ge, H. reflexivity.
Qed.

Lemma firstn_indexmap_below:
  forall l n, (n < length (concat l) -> n < length (concat (firstn (S (indexmap' l n)) l)))%nat.
Proof.
  induction l; intros.
    contradict H. apply Nat.nlt_0_r.
    unfold indexmap'; fold indexmap'. destruct (_ <? _)%nat eqn:H1.
      simpl. rewrite app_nil_r. apply Nat.ltb_lt, H1.
      rewrite firstn_cons, concat_cons, app_length. eapply (Nat.le_lt_trans _ (_+(_-_))).
        rewrite Nat.add_comm, Nat.sub_add by apply Nat.ltb_ge, H1. reflexivity.
        apply Nat.add_lt_mono_l. apply IHl. apply -> Nat.le_succ_l.
          rewrite <- Nat.sub_succ_l by apply Nat.ltb_ge, H1. apply Nat.le_sub_le_add_l.
          apply -> Nat.le_succ_l. rewrite <- app_length, <- concat_cons. apply H.
Qed.

Lemma indexmap_inlist:
  forall l n, (indexmap' l n < length l -> n < length (concat l))%nat.
Proof.
  induction l; intros.
    contradict H. apply Nat.nlt_0_r.
    rewrite concat_cons, app_length. unfold indexmap' in H; fold indexmap' in H. destruct (_ <? _)%nat eqn:H1.
      apply Nat.lt_lt_add_r, Nat.ltb_lt, H1.
      apply -> Nat.le_succ_l. apply Nat.le_sub_le_add_l. rewrite Nat.sub_succ_l.
        apply Nat.le_succ_l, IHl, Nat.succ_lt_mono, H.
        apply Nat.ltb_ge, H1.
Qed.

Lemma find_block:
  forall l i (LT: (i < length (concat l))%nat),
  exists b, (nth_error l (indexmap' l i) = Some b /\
             length (concat (firstn (indexmap' l i) l)) <= i < length (concat (firstn (indexmap' l i) l)) + length b)%nat.
Proof.
  induction l as [|b l]; intros.
    contradict LT. apply Nat.nlt_0_r.
    destruct (Nat.lt_ge_cases i (length b)).
      exists b. simpl. rewrite (proj2 (Nat.ltb_lt _ _) H). repeat split.
        apply Nat.le_0_l.
        rewrite Nat.add_0_l. assumption.
      destruct (IHl (i - length b)%nat) as [b' [H1 [H2 H3]]].
        eapply Nat.add_lt_mono_l. rewrite Nat.add_comm, Nat.sub_add, <- app_length by assumption. exact LT.
        exists b'. simpl. rewrite (proj2 (Nat.ltb_ge _ _) H). rewrite <- (Nat.add_sub i (length b)) at 3 4. simpl. rewrite Nat.add_comm, app_length. repeat split.
          apply H1.
          rewrite <- Nat.add_sub_assoc by assumption. apply Nat.add_le_mono_l, H2.
          rewrite <- Nat.add_assoc, <- Nat.add_sub_assoc by assumption. apply Nat.add_lt_mono_l, H3.
Qed.

Lemma indexmap_app1:
  forall l1 l2 i (LT: (i < length (concat l1))%nat),
  indexmap' (l1++l2) i = indexmap' l1 i.
Proof.
  induction l1; intros.
    contradict LT. apply Nat.nlt_0_r.
    simpl. destruct (i <? _)%nat eqn:H.
      reflexivity.
      apply f_equal, IHl1. apply <- Nat.add_lt_mono_r. rewrite Nat.sub_add.
        rewrite Nat.add_comm, <- app_length. exact LT.
        apply Nat.ltb_ge, H.
Qed.

Lemma indexmap_app2:
  forall l1 l2 i (LE: (length (concat l1) <= i)%nat),
  (indexmap' (l1++l2) i = length l1 + indexmap' l2 (i - length (concat l1)))%nat.
Proof.
  induction l1; intros.
    rewrite Nat.sub_0_r. reflexivity.
    simpl (indexmap' (_++_) _). simpl length. rewrite (proj2 (Nat.ltb_ge _ _)).
      rewrite IHl1, Nat.add_succ_l, app_length, Nat.sub_add_distr.
        reflexivity.
        apply Nat.le_add_le_sub_l. rewrite <- app_length. exact LE.
      etransitivity. apply Nat.le_add_r. rewrite <- app_length. exact LE.
Qed.

Lemma indexmap_same:
  forall b n l i1 i2
         (BLK: nth_error l n = Some b)
         (LE1: (length (concat (firstn n l)) <= i1)%nat)
         (LE2: (i1 <= i2)%nat)
         (LE3: (i2 < length (concat (firstn n l)) + length b)%nat),
  indexmap' l i1 = indexmap' l i2.
Proof.
  intros.
  rewrite <- (Nat.sub_add (length (concat (firstn n l))) i1) by exact LE1.
  rewrite <- (Nat.sub_add (length (concat (firstn n l))) i2) by (etransitivity; eassumption).
  rewrite 2!(Nat.add_comm (_-_)).
  rewrite 2!indexmap_sum by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
  rewrite nth_skipn in BLK. destruct (skipn n l).
    discriminate.
    inversion BLK. subst l0. simpl. rewrite 2!(proj2 (Nat.ltb_lt _ _)).
      reflexivity.
      eapply Nat.add_lt_mono_l. rewrite Nat.add_comm, Nat.sub_add. exact LE3. etransitivity; eassumption.
      eapply Nat.add_lt_mono_l. rewrite Nat.add_comm, Nat.sub_add. eapply Nat.le_lt_trans; eassumption. exact LE1.
Qed.

Lemma indexmap_next:
  forall l n b (BLK1: nth_error l n = Some b) (NN1: b <> nil) (BLK2: nth_error l (S n) <> Some nil),
  (indexmap' l (length (concat (firstn (S n) l))) = indexmap' l (length (concat (firstn n l))) + 1)%nat.
Proof.
  intros. destruct b as [|bh bt]. contradiction.
  rewrite <- (firstn_skipn n l), 2!firstn_app, 2!firstn_firstn.
  rewrite Nat.min_r, Nat.min_id by apply Nat.le_succ_diag_r.
  rewrite firstn_length_le by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK1; discriminate).
  rewrite Nat.sub_succ_l, Nat.sub_diag, app_nil_r, concat_app, app_length by reflexivity.
  rewrite indexmap_app2, (Nat.add_comm _ (length _)), Nat.add_sub by apply Nat.le_add_r.
  rewrite indexmap_app2, Nat.sub_diag by reflexivity.
  rewrite nth_skipn in BLK1. rewrite nth_skipn, skipn_S in BLK2.
  destruct (skipn n l). discriminate. inversion BLK1.

  simpl. rewrite app_nil_r, Nat.sub_diag, Nat.ltb_irrefl, Nat.add_0_r, Nat.add_1_r, Nat.add_succ_r.
  destruct l1 as [|bh2 l2].
    rewrite Nat.add_0_r. reflexivity.
    destruct bh2. contradiction. rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma newinstrs_length:
  forall {base l2 l1 l'} (NC: newinstrs base nil l1 l2 = Some l'), length l' = length l2.
Proof.
  intros. rewrite newinstrs_newinstrs', app_nil_l in NC. transitivity (length (newinstrs' base l1 l2)).
    revert l' NC. induction (newinstrs' base l1 l2); intros.
      apply invSome in NC. subst l'. reflexivity.
      destruct l'; simpl in NC.
        destruct a; [destruct optlist|]; discriminate.
        simpl. erewrite <- IHl. reflexivity. destruct a; [destruct optlist|]; try discriminate NC.
          apply invSome, invCons, proj2 in NC. subst l'. reflexivity.
    clear l' NC. revert l1. induction l2; intro. reflexivity. simpl. rewrite IHl2. reflexivity.
Qed.

Lemma newcode_nonnil:
  forall ids l base base' jmptbl l' i b (NC: newcode ids l base base' = (jmptbl, Some l'))
         (LT: nth_error l' i = Some b),
  b <> nil.
Proof.
  unfold newcode. intros. intro H. subst b.
  destruct (_ <? _); [|discriminate].
  apply invPair in NC. destruct NC as [NT NC]. rewrite (nth_newinstrs _ _ _ _ i NC) in LT.
  destruct (nth_error _ _); [|discriminate].
  destruct (newinstr _ _ _) eqn:NI; [|discriminate].
  eapply newinstr_nonnil. rewrite NI. apply f_equal.
  inversion LT. rewrite H0. apply app_eq_nil in H0. apply H0.
Qed.

Lemma shrink_length:
  forall l2 l1, length (shrink l1 l2) = (length l1 + length l2)%nat.
Proof.
  induction l2; intros.
    rewrite Nat.add_0_r. apply rev_length.
    destruct a. cbv beta iota delta [ shrink length ]. rewrite IHl2, Nat.add_succ_r. reflexivity.
Qed.

Lemma newcode_length:
  forall ids l base base' jmptbl l',
    newcode ids l base base' = (jmptbl, Some l') ->
  length l' = min (length ids) (length l).
Proof.
  unfold newcode. intros. apply invPair in H. destruct H as [NT NC].
  destruct (_ <? _); [|discriminate].
  apply newinstrs_length in NC.
  rewrite NC, shrink_length, map_length.
  apply combine_length.
Qed.

Definition dateq dp :=
  match dp with (Data iid1 oid1 sd1 n1 _, Data iid2 oid2 sd2 n2 _) =>
    Data iid1 oid1 sd1 n1 true = Data iid2 oid2 sd2 n2 true
  end.

Theorem shrink_preserves:
  forall l2 l1 l1' (LEN: length l1' = length l1)
         (FA: Forall dateq (combine l1' l1)),
  Forall dateq (combine (rev l1' ++ l2) (shrink l1 l2)).
Proof.
  induction l2; intros.

    rewrite app_nil_r. simpl. rewrite <- rev_combine by exact LEN.
    apply Forall_forall. intros dp IN. eapply Forall_forall. exact FA. apply in_rev. exact IN.

    rewrite <- (rev_involutive (a::l2)) at 1. rewrite <- rev_app_distr. simpl (rev (a::l2)).
    rewrite <- app_assoc. change ((a::nil)++l1') with (a::l1'). rewrite rev_app_distr, rev_involutive.
    destruct a. cbv beta iota delta [ shrink ]. apply IHl2.
      simpl. rewrite LEN. reflexivity.
      apply Forall_cons. reflexivity. exact FA.
Qed.

Corollary nth_shrink_preserves:
  forall ie sb pol l n iid oid sd,
    nth_error (shrink nil (map todata (combine pol l))) n = Some (Data iid oid sd ie sb) ->
  nth_error pol n = Some (iid, (oid, sd)).
Proof.
  intros. destruct (nth_error (combine pol l) n) as [[[iid0 [oid0 sd0]] ie0]|] eqn:H0.

    rewrite nth_error_combine in H0.
    destruct (nth_error pol n) as [x|] eqn:POL, (nth_error l n) as [y|] eqn:IE; try discriminate.
    inversion H0; clear H0; subst x y.
    enough (DEQ: dateq (todata (iid0, (oid0, sd0), ie0), Data iid oid sd ie sb)). inversion DEQ. reflexivity.
    eapply Forall_forall.
      apply (shrink_preserves (map todata (combine pol l)) nil nil). reflexivity. apply Forall_nil.
      eapply nth_error_In. rewrite nth_error_combine, H, app_nil_l, nth_error_map, nth_error_combine, POL, IE. reflexivity.

    contradict H0. apply nth_error_Some.
    erewrite <- map_length, <- Nat.add_0_l, <- (shrink_length _ nil).
    apply nth_error_Some. rewrite H. discriminate 1.
Qed.

Lemma reencode_branch:
  forall o, 0 <= o -> let n := Z.to_N (encode_branch_offset o) in
  (xbits n 8 12 << 1) .| ((xbits n 25 31 << 5) .| ((xbits n 7 8 << 11) .| (xbits n 31 32 << 12))) = (Z.to_N o .& N.ones 11) << 2.
Proof.
  intros. subst n. unfold encode_branch_offset.
  rewrite !Z2N_inj_lor, !Z2N_inj_shiftl, !Z2N_inj_shiftr, !Z2N_inj_land
    by repeat first [ apply Z.lor_nonneg; split | apply Z.shiftl_nonneg | apply Z.land_nonneg; right | discriminate | assumption ].
  rewrite !xbits_lor, !xbits_shiftl, !xbits_shiftr, !xbits_land.
  rewrite !N.land_0_r, !N.lor_0_r, !N.lor_0_l, !N.shiftl_0_r, N.shiftl_shiftl.
  unfold xbits. rewrite <- !N.land_ones, <- !N.land_assoc, !N.land_diag.
  rewrite !shiftr_land_shiftl by discriminate.
  rewrite <- !N.shiftl_lor, <- !N.land_lor_distr_r.
  reflexivity.
Qed.

Lemma decode_branch_lo:
  forall ie, 0 <= decode_branch_offset ie < 2^11.
Proof.
  intro. unfold decode_branch_offset.
  repeat apply Z_lor_bound; try discriminate; apply Z_land_bound; try split; (reflexivity + discriminate).
Qed.

Lemma exec_stmt_r5branch:
  forall s e a off s' x
         (XS: exec_stmt s (r5branch e a off) s' (Some x)),
  x = Addr ((Z.to_N (Z.of_N a + off)) mod 2^32)%N.
Proof.
  unfold r5branch. intros. inversion XS; subst. destruct c.
    inversion XS0.
    inversion XS0; inversion E0; subst. reflexivity.
Qed.

Lemma exec_branch_taken:
  forall s a n r1 r2 o' s' a'
         (XS: exec_stmt s (rv2il a (rv_decode_branch n r1 r2 o')) s' (Some (Addr a'))),
  a' = N.modulo (Z.to_N (Z.of_N a + o')) (2^32).
Proof.
  unfold rv_decode_branch. intros.
  destruct n; [|repeat (destruct p; try solve [ inversion XS ])];
  inversion XS; destruct c; inversion XS0; inversion E0; reflexivity.
Qed.

Lemma ofZ_wide_shiftl:
  forall w s z, ofZ (w+s)%N (Z.shiftl z (Z.of_N s)) = (ofZ w z) << s.
Proof.
  intros.
  rewrite ofZ_shiftl, N.shiftl_mul_pow2, N.pow_add_r.
  rewrite N.Div0.mul_mod_distr_r by (apply N.pow_nonzero; discriminate).
  rewrite <- N.shiftl_mul_pow2, <- (N2Z.id (2^w)).
  unfold ofZ. rewrite <- Z2N.inj_mod, <- Znumtheory.Zmod_div_mod.
    rewrite N2Z.inj_pow. reflexivity.
    apply N2Z_pow2_pos.
    apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    rewrite N2Z.inj_pow, N2Z.inj_add, Z.pow_add_r by apply N2Z.is_nonneg. apply Z.divide_factor_l.
    apply Z.mod_pos_bound. apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
    apply N2Z.is_nonneg.
Qed.

Lemma Zcmp_signed_range:
  forall w z, andb (-2^Z.of_N (N.pred (N.pos w)) <=? z)%Z (z <? 2^Z.of_N (N.pred (N.pos w)))%Z = true -> signed_range (N.pos w) z.
Proof.
  intros. apply Bool.andb_true_iff in H. destruct H as [H1 H2]. split.
    apply Zle_bool_imp_le. rewrite <- N2Z.inj_pred by reflexivity. apply H1.
    apply Z.ltb_lt, H2.
Qed.

Lemma signed_range_shiftl:
  forall w s z, signed_range w z -> signed_range (w+s) (Z.shiftl z (Z.of_N s)).
Proof.
  intros. destruct w.
    apply signed_range_0_l in H. subst z. rewrite Z.shiftl_0_l. apply signed_range_0_r.
    destruct s.
      rewrite N.add_0_r, Z.shiftl_0_r. assumption.

      unfold signed_range.
      rewrite Z.shiftl_mul_pow2 by discriminate.
      rewrite <- N2Z.inj_pred by reflexivity.
      rewrite <- N.add_pred_l by discriminate.
      rewrite !N2Z.inj_add, Z.pow_add_r by apply N2Z.is_nonneg.
      rewrite <- Z.mul_opp_l by discriminate.
      split.
        apply Zmult_le_compat_r.
          rewrite N2Z.inj_pred by reflexivity. apply H.
          apply Z.pow_nonneg. discriminate.
        apply Zmult_lt_compat_r.
          apply Z.pow_pos_nonneg. reflexivity. apply N2Z.is_nonneg.
          apply H.
Qed.

Lemma sumsizes_app:
  forall l1 l2, sumsizes (l1++l2) = sumsizes l1 + sumsizes l2.
Proof.
  intros.
  transitivity (fold_left (fun c d => c + newsize d) l2 (sumsizes l1)).
    unfold sumsizes at 1. rewrite fold_left_app. reflexivity.
    generalize (sumsizes l1). induction l2; intro b.
      symmetry. apply Z.add_0_r.
      unfold sumsizes. simpl. rewrite !IHl2. symmetry. apply Z.add_assoc.
Qed.

Corollary sumsizes_cons:
  forall d l, sumsizes (d::l) = newsize d + sumsizes l.
Proof.
  intros. change (d::l) with ((d::nil)++l). apply sumsizes_app.
Qed.

Lemma sumsizes_rev:
  forall l, sumsizes (rev l) = sumsizes l.
Proof.
  induction l.
    reflexivity.
    simpl. rewrite sumsizes_app, IHl, Z.add_comm, <- sumsizes_app. reflexivity.
Qed.

Lemma sumnsizes_sumsizes:
  forall l n b,
  sum_n_sizes n l b = b + sumsizes (firstn (Z.to_nat n) l).
Proof.
  induction l; intros; symmetry.
    rewrite firstn_nil. apply Z.add_0_r.
    destruct n; try solve [ apply Z.add_0_r ].
      simpl firstn. unfold sum_n_sizes; fold sum_n_sizes.
      rewrite (proj2 (Z.ltb_lt 0 _)), IHl, <- Z.add_assoc by apply Pos2Z.is_pos.
      rewrite Z.sub_1_r, Z2Nat.inj_pred, Z2Nat.inj_pos.
      destruct (Pos2Nat.is_succ p) as [n H]. rewrite H, Nat.pred_succ.
      simpl. rewrite sumsizes_cons. reflexivity.
Qed.

Lemma newoffset_index:
  forall l1 d c l2 i,
    newoffset l1 d c l2 i =
    sumsizes (firstn (Z.to_nat (Z.of_nat (length l1) + i)) (rev l1++d::l2)) + c - sumsizes (d::l1).
Proof.
  intros. unfold newoffset. rewrite sumnsizes_sumsizes.
  rewrite sumsizes_cons, (Z.add_comm (newsize d)), Z.sub_add_distr. apply Z.sub_cancel_r.
  rewrite Z.add_sub_swap. apply Z.add_cancel_r.
  destruct (0 <=? i) eqn:SGN.

    rewrite <- (Z2Nat.id i) at 2 by apply Z.leb_le, SGN.
    rewrite <- Nat2Z.inj_add, Nat2Z.id, <- rev_length, firstn_app_2.
    rewrite sumsizes_app, sumsizes_rev, Z.add_simpl_l. reflexivity.

    apply Z.leb_gt, Z.opp_pos_neg, Z.lt_le_incl in SGN. rewrite <- Z.sub_opp_r.
    rewrite firstn_app, rev_length, (proj2 (Nat.sub_0_le _ _)) by
    ( rewrite Z2Nat.inj_sub, Nat2Z.id by exact SGN; apply Nat.le_sub_l ).
    rewrite app_nil_r, <- (sumsizes_rev l1).
    erewrite <- (firstn_skipn _ (rev l1)) at 2.
    rewrite sumsizes_app, Z.sub_add_distr, Z.sub_diag.
    rewrite Z2Nat.inj_sub, Nat2Z.id, <- rev_firstn, sumsizes_rev by exact SGN.
    rewrite sumnsizes_sumsizes. symmetry. apply Z.sub_0_l.
Qed.

Lemma sumsizes_nonneg:
  forall l, 0 <= sumsizes l.
Proof.
  induction l.
    reflexivity.
    rewrite sumsizes_cons. apply Z.add_nonneg_nonneg.
      transitivity 1. discriminate. apply newsize_pos.
      apply IHl.
Qed.

Corollary sumsizes_firstn_le:
  forall n l, sumsizes (firstn n l) <= sumsizes l.
Proof.
  intros.
  rewrite <- (firstn_skipn n l) at 2.
  rewrite sumsizes_app.
  rewrite <- (Z.add_0_r (sumsizes _)) at 1.
  apply Z.add_le_mono_l, sumsizes_nonneg.
Qed.

Lemma newoffset_bounds:
  forall l1 d c l2 i,
  - (newsize d - c + sumsizes l1) <= newoffset l1 d c l2 i <= c + sumsizes l2.
Proof.
  intros. unfold newoffset. split.
    rewrite Z.opp_add_distr, Z.opp_sub_distr, (Z.add_comm _ c), (Z.add_opp_r c), Z.add_comm,
            <- Z.add_sub_assoc, !sumnsizes_sumsizes, !Z.add_0_l. apply Z.add_le_mono_r. destruct (_ <=? _).
      transitivity 0. apply Z.opp_nonpos_nonneg, sumsizes_nonneg. apply sumsizes_nonneg.
      apply -> Z.opp_le_mono. apply sumsizes_firstn_le.
    rewrite Z.add_sub_swap, (Z.add_comm c), !sumnsizes_sumsizes, !Z.add_0_l. apply Z.add_le_mono_r. destruct (_ <=? _).
      apply Z.le_sub_le_add_l. rewrite <- sumsizes_cons. apply sumsizes_firstn_le.
      rewrite <- Z.add_opp_r, <- Z.opp_add_distr, Z.add_comm, <- sumsizes_cons. transitivity 0.
        apply Z.opp_nonpos_nonneg, sumsizes_nonneg.
        apply sumsizes_nonneg.
Qed.

Theorem newsize_newinstr:
  forall {base l1 d l2 l} (NI: newinstr base l1 d l2 = Some l),
  newsize d = Z.of_nat (length (newtag d) + length l).
Proof.
  unfold newinstr, newsize. unfold_consts. intros. destruct d. rewrite Nat2Z.inj_add. apply f_equal2.
    destruct iid; reflexivity.

    destruct (_ <? 0). discriminate.
    destruct (n #& 4095 =? 55) eqn:N55.
    destruct mem; [|discriminate]. apply invSome in NI. subst l.
    apply Z.eqb_eq, (f_equal (Z.land 127)) in N55. rewrite Z.land_comm, <- Z.land_assoc in N55. simpl in N55. rewrite N55.
    rewrite !(proj2 (Z.eqb_neq _ _)) by discriminate. reflexivity.

    destruct (n #& 127 =? 23) eqn:OP23; [|clear OP23]. unfold new_auipc in NI.
      destruct (_ && _)%bool.
        destruct (_ =? 0).
          apply invSome in NI. subst l. reflexivity.
          apply invSome in NI. subst l. reflexivity.
        discriminate NI.

    destruct (n #& 127 =? 99).
      destruct andb; [|discriminate]. unfold newbranch in NI. destruct sb.
        destruct andb; [|discriminate]. apply invSome in NI. subst l. reflexivity.
        unfold newjump in NI. destruct andb; [|discriminate]. apply invSome in NI. subst l. reflexivity.

    destruct (n #& 127 =? 103). unfold newijump, newbranch in NI. destruct sb.
      destruct andb; [|discriminate]. apply invSome in NI. subst l. reflexivity.
      unfold newjump in NI. destruct andb; [|discriminate]. apply invSome in NI. subst l. reflexivity.

    destruct (n #& 127 =? 111).
      destruct andb; [|discriminate].
      unfold newjump in NI. destruct andb; [|discriminate]. apply invSome in NI. subst l. reflexivity.

    destruct mem; [|discriminate]. apply invSome in NI. subst l. reflexivity.
Qed.

Lemma sumsizes_foldmap:
  forall l, sumsizes l = fold_left Z.add (map newsize l) 0.
Proof.
  intro. unfold sumsizes. generalize 0 as b. induction l; intro.
    reflexivity.
    apply IHl.
Qed.

Theorem sumsizes_newinstrs:
  forall {base l2 l1 l'} n (NC:newinstrs base nil l1 l2 = Some l'),
  sumsizes (firstn n l2) = Z.of_nat (length (concat (firstn n l'))).
Proof.
  intros. rewrite newinstrs_newinstrs', app_nil_l in NC.
  unfold sumsizes. rewrite <- (Z.add_0_l (Z.of_nat _)). generalize 0. intro b.
  revert l1 l' b NC n. induction l2; intros.
    apply invSome in NC. subst l'. rewrite !firstn_nil. rewrite Z.add_0_r. reflexivity.

    simpl in NC. specialize (IHl2 (a::l1)). destruct newinstr eqn:NI; destruct optlist; try discriminate.
    apply invSome in NC. subst l'.
    destruct n. rewrite Z.add_0_r. reflexivity.
    simpl. rewrite !app_length. erewrite IHl2 by reflexivity.
    rewrite Nat2Z.inj_add, Z.add_assoc. apply Z.add_cancel_r, Z.add_cancel_l.
    eapply newsize_newinstr. exact NI.
Qed.

Corollary sumsizes_newinstrs_all:
  forall {base l2 l1 l'} (NC:newinstrs base nil l1 l2 = Some l'),
  sumsizes l2 = Z.of_nat (length (concat l')).
Proof.
  intros. rewrite <- (firstn_all l2), <- (firstn_all l'). erewrite newinstrs_length by eassumption.
  eapply sumsizes_newinstrs. eassumption.
Qed.

Lemma sumlist_le:
  forall l1 l2 n1 n2, (Forall2 Z.le l1 l2) -> n1 <= n2 ->
  fold_left Z.add l1 n1 <= fold_left Z.add l2 n2.
Proof.
  induction l1; intros; inversion H; subst.
    assumption.
    simpl. apply IHl1. assumption. apply Z.add_le_mono; assumption.
Qed.

Theorem sumsizes_shrink_le:
  forall l l1 l2
    (LEN: length l1 = length l2)
    (MONO: forall n, sumsizes (firstn n l1) <= sumsizes (firstn n l2)),
  (forall n, sumsizes (firstn n (shrink (rev l1) l)) <= sumsizes (firstn n (l2++l))).
Proof.
  induction l; intros.

    simpl. rewrite rev_involutive, app_nil_r. apply MONO.

    change (l2++a::l) with (l2++(a::nil)++l). rewrite app_assoc.
    destruct a. cbv beta iota delta [ shrink ]; fold shrink.
    match goal with |- context [ orb _ ?e ] => generalize e end. intro sb'.
    rewrite <- rev_unit. apply IHl. rewrite !app_length. apply Nat.add_cancel_r, LEN.
    clear n. intro n.
    rewrite !firstn_app, !sumsizes_app. apply Z.add_le_mono. apply MONO.
    rewrite LEN. destruct (n - _)%nat. reflexivity.
    simpl. rewrite firstn_nil. unfold sumsizes, fold_left, newsize.
    destruct sb. reflexivity.
    destruct sb'; [|reflexivity].
    do 2 apply Z.add_le_mono_l. repeat (reflexivity + discriminate + destruct (_ =? _)).
Qed.

Lemma tag_fallsthru:
  forall s a iid s' x,
  exec_stmt s (rv2il a (rv_decode (Z.to_N ((iid mod 2^20 #<< 12) #| 55)))) s' x -> x = None.
Proof.
  intros until x. unfold rv_decode. replace (_ .& _) with 55%N.
    unfold rv_decode_op. destruct xbits; intro H; inversion H; reflexivity.
    rewrite Z2N_inj_lor.
      rewrite N.land_lor_distr_l, N.land_ones, Z.shiftl_mul_pow2, Z2N.inj_mul; try discriminate.
        change (Z.to_N (2^12)) with (2^5 * 2^7)%N. rewrite N.mul_assoc, N.mod_mul by discriminate. reflexivity.
        apply Z_mod_lt. reflexivity.
      apply Z.shiftl_nonneg, Z_mod_lt. reflexivity.
      discriminate.
Qed.

Lemma sumsizes_firstn_S:
  forall l i d,
  nth_error l i = Some d -> sumsizes (firstn (S i) l) = sumsizes (firstn i l) + newsize d.
Proof.
  intros. symmetry.
  rewrite <- sumsizes_rev, Z.add_comm, <- sumsizes_cons, <- rev_unit, sumsizes_rev.
  ereplace (d::nil).
    rewrite <- firstn_last. reflexivity.
    rewrite H. reflexivity.
Qed.

Lemma twoscomp_toZ:
  forall w o, 0 < w -> 0 <= o < 2^Z.succ w -> twoscomp (2^w) o = toZ (N.succ (Z.to_N w)) (Z.to_N o).
Proof.
  intros w o H. destruct w as [|w|w]; try discriminate. clear H.
  rewrite <- Z2N.inj_succ by discriminate. rewrite <- (Z.pred_succ (Z.pos w)) at 2. rewrite <- Pos2Z.inj_succ.
  symmetry. destruct H as [H1 H2].
  rewrite <- (Z2N.id (2^_)) by (apply Z.pow_nonneg; discriminate).
  rewrite <- (Z2N.id o) at 2 by assumption.
  apply Z2N.inj_lt in H2; [|assumption|apply Z.pow_nonneg;discriminate].
  rewrite <- Pos2Z.inj_pred by (destruct w; discriminate).
  rewrite !Z2N.inj_pow, !Z2N.inj_pos, Pos.pred_succ in * by discriminate.
  unfold twoscomp. rewrite N2Z_inj_ltb. destruct (_ <? _)%N eqn:CMP.
    rewrite (proj1 (toZ_nonneg _ _)); rewrite N.mod_small by exact H2.
      reflexivity.
      simpl. rewrite Pos.pred_N_succ. apply N.ltb_lt, CMP.
    rewrite (proj1 (toZ_neg _ _)); rewrite N.mod_small by exact H2.
      rewrite N2Z.inj_pow, <- Z.pow_succ_r, Pplus_one_succ_r by apply N2Z.is_nonneg. reflexivity.
      apply N.ltb_ge. simpl. rewrite Pos.pred_N_succ. apply CMP.
Qed.

Theorem newsize_length:
  forall base l l' i d b (NC: newinstrs base nil nil l = Some l'),
    nth_error l i = Some d -> nth_error l' i = Some b -> newsize d = Z.of_nat (length b).
Proof.
  intros.
  erewrite nth_newinstrs, H in H0 by exact NC.
  destruct newinstr eqn:NI; [|discriminate].
  apply invSome in H0. subst b.
  erewrite newsize_newinstr, app_length by exact NI.
  reflexivity.
Qed.

Lemma indexmap_skipn_next:
  forall base l1 l2 l' i b (NC: newinstrs base nil l1 l2 = Some l'),
    nth_error l' i = Some b -> indexmap' (skipn i l') (length b) = 1%nat.
Proof.
  intros. rewrite nth_skipn in H. destruct skipn eqn:H1.
    discriminate.
    apply invSome in H. subst. simpl. rewrite Nat.ltb_irrefl, Nat.sub_diag, indexmap_0.
      reflexivity.
      replace l0 with (skipn (S i) l').
        rewrite <- nth_skipn. eapply newinstrs_nonnil, NC.
        rewrite skipn_S, H1. reflexivity.
Qed.

Lemma indexmap_newoffset:
  forall base l l' d i c o
    (NC: newinstrs base nil nil l = Some l') (DAT: nth_error l i = Some d),
  indexmap' l' (Z.to_nat (sumsizes (firstn (S i) l) - c
                          + newoffset (rev (firstn i l)) d c (skipn (S i) l) o))
  = Nat.min (Z.to_nat (Z.of_nat i + o)) (length l').
Proof.
  intros.
  rewrite newoffset_index.
  rewrite sumsizes_cons, sumsizes_rev, (Z.add_comm (newsize _)), <- sumsizes_firstn_S by assumption.
  rewrite Z.add_sub_swap, <- (Z.sub_sub_distr _ _ c), Zplus_minus.
  rewrite rev_involutive, firstn_cons_skipn, rev_length by exact DAT.
  rewrite firstn_length_le by (apply Nat.lt_le_incl, nth_error_Some; rewrite DAT; discriminate).
  rewrite (sumsizes_newinstrs _ NC), Nat2Z.id.
  rewrite <- (Nat.add_0_r (length _)), indexmap_length.
  rewrite indexmap_0 by (rewrite <- nth_skipn; apply (newinstrs_nonnil _ _ _ _ _ NC)).
  apply Nat.add_0_r.
Qed.

Lemma r5mov_fallthru:
  forall s r e s' x, exec_stmt s (r5mov r e) s' x -> x = None.
Proof.
  intros. destruct r; inversion H; reflexivity.
Qed.

Theorem rv_fallthru:
  forall ie s a s' x (IE: 0 <= ie)
    (OP99:  ie #& 127 =? 99 = false)
    (OP103: ie #& 127 =? 103 = false)
    (OP111: ie #& 127 =? 111 = false)
    (XS: exec_stmt s (rv2il a (rv_decode (Z.to_N ie))) s' x),
  x = None \/ x = Some (Raise 2).
Proof.
  intros until x. intro H.
  rewrite !Z.eqb_compare, <- !Z2N.inj_compare by (try (apply Z.land_nonneg; right); discriminate).
  rewrite Z2N_inj_land by (discriminate + assumption).
  simpl (Z.to_N (Zpos _)). rewrite <- !N.eqb_compare.
  unfold rv_decode. change (N.ones 7) with 127%N.
  generalize (Z.to_N ie). clear ie H. intro ie. intros.
  destruct rv_decode_op eqn:OP; first
  [ left; eapply r5mov_fallthru; exact XS
  | inversion XS; (left + right); reflexivity
  | clear XS; exfalso;
    unfold rv_decode_op, rv_decode_binop, rv_decode_op_imm, rv_decode_fence, rv_decode_store, rv_decode_load in OP;
    repeat match type of OP with (match ?x with _ => _ end = _) => destruct x; try discriminate
                               | (match ?x with _ => _ end _ _ _ = _) => destruct x; try discriminate end ].
Qed.

Lemma shiftl_landones_0:
  forall n x y, Z.of_N n <= y -> (x #<< y) #& Z.ones (Z.of_N n) = 0.
Proof.
  intros. rewrite Z.land_ones by apply N2Z.is_nonneg.
  rewrite Z.shiftl_mul_pow2 by (etransitivity; [apply N2Z.is_nonneg|exact H]).
  rewrite <- (Z.sub_add (Z.of_N n) y), Z.pow_add_r, Z.mul_assoc.
    apply Z_mod_mult.
    apply Z.le_0_sub, H.
    apply N2Z.is_nonneg.
Qed.

Lemma newijump_fallthrus:
  forall l1 d l2 b k ie' s a s' x (K4: (k <> 4)%nat) (K9: (k < 9)%nat)
    (NI: newijump l1 d l2 = Some b)
    (IE': nth_error b k = Some ie')
    (XS: exec_stmt s (rv2il a (rv_decode (Z.to_N ie'))) s' x),
  x = None \/ x = Some (Raise 2).
Proof.
  intros. destruct d as [iid oid sd n sb].
  assert (IE0: 0 <= ie'). eapply Forall_forall. eapply newijump_nonneg, NI. eapply nth_error_In, IE'.
  unfold newijump in NI.
  set (rs1 := (n #>> 15) #& 31) in NI.
  set (tmp1 := if rs1 =? 31 then 29 else 31) in NI.
  set (tmp2 := if rs1 =? 30 then 29 else 30) in NI.
  set (tmp3 := if 29 <? rs1 then rs1 else 29) in NI.
  destruct newbranch eqn:NB; [|discriminate].
  apply invSome in NI. subst b.
  do 10 try destruct k as [|k]; try solve [
    apply invSome in IE'; eassert (H: ie' #& 127 = _);
    [ rewrite <- IE'; rewrite !Z.land_lor_distr_l, !(shiftl_landones_0 7) by discriminate;
      try rewrite <- Z.land_assoc, Z.land_0_r;
      match goal with |- ?e = _ => simpl e end; reflexivity
    | eapply rv_fallthru; first [ eassumption | rewrite H; reflexivity ] ] ].

    contradiction.

    repeat apply <- Nat.succ_lt_mono in K9. contradict K9. apply Nat.nlt_0_r.
Qed.

Lemma newjump_size:
  forall rd o' b (NJ: newjump rd o' = Some b), length b = 1%nat.
Proof.
  intros. unfold newjump in NJ.
  destruct andb; [|discriminate]. apply invSome in NJ. subst b. reflexivity.
Qed.

Lemma newbranch_size:
  forall l1 iid oid sd n sb c l2 op i b (NB: newbranch l1 (Data iid oid sd n sb) c l2 op i = Some b),
  (length b = if sb then 1 else 2)%nat.
Proof.
  intros. unfold newbranch in NB. destruct sb.
    destruct andb; [|discriminate]. apply invSome in NB. subst b. reflexivity.
    destruct newjump eqn:NJ; [|discriminate]. apply invSome in NB. subst b.
      apply newjump_size in NJ. rewrite length_cons, <- NJ. reflexivity.
Qed.

Lemma newijump_size:
  forall l1 iid oid sd n sb l2 b (NI: newijump l1 (Data iid oid sd n sb) l2 = Some b),
  (length b = if sb then 12 else 13)%nat.
Proof.
  intros. unfold newijump in NI. destruct newbranch eqn:NB; [|discriminate].
  apply invSome in NI. subst b.
  rewrite !length_cons. rewrite app_length. erewrite newbranch_size by exact NB.
  destruct sb; reflexivity.
Qed.

Lemma ejo_bitfield:
  forall o, encode_jump_offset o #& 2101247 = 0.
Proof.
  intro. unfold encode_jump_offset.
  rewrite !Z.land_lor_distr_l, !Z.shiftl_land, <- !Z.land_assoc, !Z.land_0_r.
  reflexivity.
Qed.

Lemma ebo_bitfield:
  forall o, encode_branch_offset o #& 33550719 = 0.
Proof.
  intro. unfold encode_branch_offset.
  rewrite !Z.land_lor_distr_l, !Z.shiftl_land, Z.shiftr_land, <- !Z.land_assoc, !Z.land_0_r.
  reflexivity.
Qed.

Lemma xbits_land_clear_r:
  forall n i j m, (N.ones (j-i) .& m = 0 -> xbits n i j .& m = 0)%N.
Proof.
  intros. unfold xbits. rewrite <- N.land_ones, <- N.land_assoc, H. apply N.land_0_r.
Qed.

Lemma xbits_0_land:
  forall n j, xbits n 0 j = n .& N.ones j.
Proof. intros. unfold xbits. rewrite N.shiftr_0_r, N.sub_0_r, N.land_ones. reflexivity. Qed.

Theorem newtag_asm:
  forall d,
    map rv_decode (map Z.to_N (newtag d)) =
    match d with Data None _ _ _ _ => nil
               | Data (Some iid) _ _ _ _ => R5_Lui 0 (Z.to_N (iid mod 2^20)) :: nil end.
Proof.
  intro. unfold newtag. destruct d as [[iid|] oid sd z sb]; [|reflexivity].
  unfold map. rewrite Z2N_inj_lor, Z2N_inj_shiftl by Z_nonneg.
  unfold rv_decode. rewrite N.land_lor_distr_l, N_shiftl_land_0 by reflexivity. simpl (_ .| 0).
  unfold rv_decode_op.
  rewrite !xbits_lor, !xbits_shiftl, xbits_0_land, N.land_ones, N.mod_1_r, N.shiftl_0_r, xbits_0_i.
  change (2^(32-_))%N with (Z.to_N (2^20)). rewrite <- Z2N.inj_mod, Z.mod_mod by Z_nonneg.
  reflexivity.
Qed.

Theorem newjump_asm:
  forall rd o' b (NJ: newjump rd o' = Some b) (RDLO: 0 <= rd) (RDHI: rd < 32),
  map rv_decode (map Z.to_N b) = (R5_Jal (Z.to_N rd) (4 * o'))::nil.
Proof.
  unfold newjump. change Z262144 with (2^18). change (Z_262144) with (-2^18). change Z524288 with (2^19).
  intros.
  destruct andb eqn:BND; [|discriminate]. apply andb_prop in BND. destruct BND as [LO HI].
  apply Z.leb_le in LO. apply Z.ltb_lt in HI.
  apply invSome in NJ. subst b.
  unfold map. apply f_equal2; [|reflexivity].
  unfold rv_decode. change (N.ones 7) with (Z.to_N 127).
  rewrite <- Z2N_inj_land by Z_nonneg.
  rewrite Z.land_lor_distr_l. change 127 with (2101247 #& 127) at 2. rewrite Z.land_assoc, ejo_bitfield, Z.lor_0_r.
  rewrite Z.land_lor_distr_l. change 127 with (Z.ones (Z.of_N 7)) at 2. rewrite shiftl_landones_0, Z.lor_0_r by discriminate 1.
  simpl (Z.to_N (_ #& _)). unfold rv_decode_op.

  rewrite <- (Z.mod_small rd (2^5)) by (split; assumption). rewrite <- Z.land_ones by discriminate 1.
  rewrite !Z2N_inj_lor, !xbits_lor, Z2N_inj_shiftl, !xbits_shiftl, Z2N_inj_land, !xbits_land,
          !N.land_0_r, !N.lor_0_l, N.shiftl_0_r, !xbits_0_i by Z_nonneg.
  change (Z.to_N (Z.ones 5) mod _)%N with (N.ones 5). rewrite N.land_ones, N.mod_mod, <- N.land_ones by discriminate 1.
  unfold encode_jump_offset.
  rewrite !Z2N_inj_lor by repeat first [ apply Z.shiftl_nonneg | apply Z.land_nonneg; right; discriminate | apply Z.lor_nonneg; split ].
  rewrite !Z2N_inj_shiftl by (try (apply Z.land_nonneg; right); discriminate).
  rewrite !Z2N_inj_land by (discriminate + apply Z.mod_pos_bound; reflexivity).
  rewrite !xbits_lor, !xbits_shiftl, !xbits_land, !N.land_0_r, !N.shiftl_0_l.

  rewrite !N.shiftl_0_r, !N.lor_0_l, !N.lor_0_r.
  unfold xbits. rewrite <- !N.land_ones, <- !N.land_assoc, !N.land_diag.
  rewrite N.shiftl_shiftl, !shiftr_land_shiftl by discriminate.
  rewrite <- !N.shiftl_lor, <- !N.land_lor_distr_r, (N.land_ones _ 19).

  rewrite (N.shiftl_mul_pow2 _ 2).
  change (2^19)%N with (Z.to_N (2^19)). rewrite <- Z2N.inj_mod, Zmod_mod; [| apply Z.mod_pos_bound; reflexivity | discriminate 1 ].
  change (2^2)%N with (Z.to_N 4). rewrite <- Z2N.inj_mul by (discriminate + (apply Z.mod_pos_bound; reflexivity)).
  rewrite <- Zmult_mod_distr_r, Z.mul_comm.
  change (Z.to_N (_ mod _)) with (ofZ 21%N (4*o')). rewrite toZ_ofZ. reflexivity. split.
    change (-_) with (4*(-2^18)). apply Z.mul_le_mono_nonneg_l. discriminate. exact LO.
    change (2^Z.of_N _) with (4*2^18). apply Z.mul_lt_mono_pos_l. reflexivity. exact HI.
Qed.

Definition opposite_branch n :=
  (match n with 
   | 0 => R5_Bne | 1 => R5_Beq | 4 => R5_Bge | 5 => R5_Blt | 6 => R5_Bgeu | 7 => R5_Bltu
   | _ => (fun _ _ _ => R5_InvalidI)
   end)%N.

Theorem newbranch_asm:
  forall l1 d c l2 z i b (OP0: 0 <= z) (OP99: z #& 127 = 99) (OP256: z #& 256 = 0)
    (NB: newbranch l1 d c l2 z i = Some b),
  let n := Z.to_N z in
  map rv_decode (map Z.to_N b) =
  if match d with Data _ _ _ _ sb => sb end
  then (rv_decode_branch (N.lor (xbits n 12 15) (N.land n 256)) (xbits n 15 20) (xbits n 20 25) (4 * newoffset l1 d c l2 i))::nil
  else (opposite_branch (N.lor (xbits n 12 15) (N.land n 256)) (xbits n 15 20) (xbits n 20 25) 8)::(R5_Jal 0 (4 * newoffset l1 d c l2 i))::nil.
Proof.
  destruct d as [iid oid sd op sb]. unfold newbranch. unfold_consts.
  change (-1024) with (-2^10). change 1024 with (2^10). change 2048 with (2^11).
  intros until b. set (o := newoffset _ _ _ _ _). intros.
  change 256%N with (Z.to_N 256). rewrite <- Z2N_inj_land, OP256, N.lor_0_r by Z_nonneg.
  destruct sb.

    destruct andb eqn:BND; [|discriminate]. apply andb_prop in BND. destruct BND as [LO HI].
    apply Z.leb_le in LO. apply Z.ltb_lt in HI.
    apply invSome in NB. subst b.
    unfold map. apply f_equal2; [|reflexivity].
    unfold rv_decode. change (N.ones 7) with (Z.to_N 127).
    rewrite <- Z2N_inj_land by (try (apply Z.lor_nonneg; split; [apply Z.land_nonneg; right | apply ebo_nonneg]); discriminate).
    rewrite Z.land_lor_distr_l, <- Z.land_assoc. simpl (_ #& 127). rewrite OP99.
    change 127 with (33550719 #& 127). rewrite Z.land_assoc, ebo_bitfield, Z.lor_0_r. simpl (Z.to_N 99).
    unfold rv_decode_op.
    rewrite !Z2N_inj_lor, Z2N_inj_land by (exact OP0 + (try (apply Z.land_nonneg; right); discriminate) + apply ebo_nonneg).
    rewrite !xbits_lor, !xbits_land, !(xbits_land_cancel_r 31) by reflexivity.
    apply f_equal4.

      rewrite xbits_land_cancel_r by reflexivity.
      rewrite N.land_lor_distr_l, <- N.land_assoc, N.land_0_r.
      change 256%N with (Z.to_N 33550719 .& 256%N) at 1. rewrite N.land_assoc, <- Z2N_inj_land, ebo_bitfield by Z_nonneg.
      erewrite (xbits_excl_zero _ (Z.to_N (encode_branch_offset _))).
        rewrite !N.lor_0_r. reflexivity.
        rewrite <- Z2N_inj_land. rewrite ebo_bitfield. reflexivity. apply ebo_nonneg. discriminate.
        reflexivity.

      erewrite (xbits_excl_zero _ (Z.to_N (encode_branch_offset _))). apply N.lor_0_r.
        rewrite <- Z2N_inj_land. rewrite ebo_bitfield. reflexivity. apply ebo_nonneg. discriminate.
        reflexivity.
      erewrite (xbits_excl_zero _ (Z.to_N (encode_branch_offset _))). apply N.lor_0_r.
        rewrite <- Z2N_inj_land. rewrite ebo_bitfield. reflexivity. apply ebo_nonneg. discriminate.
        reflexivity.

      rewrite !N.land_0_r, !N.lor_0_l. unfold encode_branch_offset.
      rewrite !Z2N_inj_lor by (repeat (apply Z.lor_nonneg; split); apply Z.shiftl_nonneg, Z.land_nonneg; right; discriminate).
      rewrite !xbits_lor, !Z2N_inj_shiftl, !Z2N_inj_shiftr by (try (apply Z.land_nonneg; right); discriminate).
      rewrite !xbits_shiftl, !xbits_shiftr, !Z2N_inj_land by ((apply Z_mod_lt; reflexivity) + discriminate).
      rewrite !xbits_land, !N.land_0_r. rewrite !xbits_land_cancel_r by reflexivity.
      rewrite !N.lor_0_r, !N.shiftl_0_r, !N.lor_0_l.
      rewrite N.shiftl_shiftl.
      rewrite <- (N.shiftl_shiftl _ 3 2), <- (N.shiftl_shiftl _ 9 2), <- (N.shiftl_shiftl _ 10 2), <- !N.shiftl_lor.
      rewrite !N.lor_assoc, <- !xbits_split by discriminate.
      unfold xbits. rewrite N.shiftr_0_r.
      change (2^(_-_))%N with (Z.to_N (2^11)). change 2%N with (Z.to_N 2).
      rewrite <- Z2N.inj_mod, Z.mod_mod, <- Z2N_inj_shiftl by (try apply Z_mod_lt; discriminate + reflexivity).
      rewrite Z.shiftl_mul_pow2, <- Z.mul_mod_distr_r, Z.mul_comm by discriminate.
      apply toZ_ofZ. change 4 with (2^2). change 13%N with (11+2)%N. rewrite Z.mul_comm, <- Z.shiftl_mul_pow2 by discriminate.
      apply signed_range_shiftl. split; assumption.

    destruct newjump eqn:NJ; [|discriminate]. apply invSome in NB. subst b.
    rewrite !map_cons. change N0 with (Z.to_N 0). apply f_equal2; [| apply newjump_asm; [ exact NJ | discriminate | reflexivity ] ].
    unfold rv_decode. change (N.ones _) with (Z.to_N 127). rewrite <- Z2N_inj_land by
    ( try (apply Z.lor_nonneg; split; [ apply Z.lxor_nonneg; split; [|intro; apply Z.land_nonneg; right] |]); discriminate).
    rewrite Z.land_lor_distr_l, Z_lxor_land_distr_l, <- Z.land_assoc, Z.lxor_0_r, Z.lor_0_r.
    change (_ #& 127) with 127. rewrite OP99. simpl (Z.to_N 99).
    change 4096 with (4096 #& 33550463). rewrite <- Z_lxor_land_distr_l.
    rewrite Z2N_inj_lor by (try (apply Z.land_nonneg; right); discriminate).
    rewrite Z2N_inj_land by (try (apply Z.lxor_nonneg; split; intro); discriminate + assumption).
    rewrite Z2N_inj_lxor by (assumption + discriminate).
    unfold rv_decode_op, rv_decode_branch, opposite_branch.
    rewrite !xbits_lor, !xbits_land, !N.land_0_r, !N.lor_0_r.
    rewrite !xbits_land_cancel_r by reflexivity.
    rewrite !xbits_lxor, !N.lxor_0_r, N.lor_0_l.
    rewrite N.land_lor_distr_l, <- N.land_assoc, N.land_0_r, N.lor_0_r.
    change (xbits (Z.to_N 4096) 12 15) with 1%N. change (toZ _ _) with 8.
    assert (UB: (xbits (Z.to_N z) 12 15 < 8)%N).
      unfold xbits. apply N.mod_lt. discriminate.
    destruct (xbits (Z.to_N z) 12 15) as [|p]. reflexivity.
    repeat (discriminate + (destruct p as [p|p|]; [| |reflexivity])).
Qed.

Lemma N2Z_inj_ifbool:
  forall (b:bool) x y, Z.of_N (if b then x else y) = (if b then Z.of_N x else Z.of_N y).
Proof.
  intros. destruct b; reflexivity.
Qed.

Lemma xbits_none':
  forall n i, xbits n i i = N0.
Proof. intros. apply xbits_none. reflexivity. Qed.

Theorem newijump_asm:
  forall l1 iid oid sd z sb l2 b (OP0: 0 <= z) (OP103: z #& 127 = 103)
    (NIJ: newijump l1 (Data iid oid sd z sb) l2 = Some b),
  let n := Z.to_N z in
  let rs1 := xbits n 15 20 in
  let tmp1 := (if rs1 <? 31 then 31 else 29)%N in
  let tmp2 := (if rs1 =? 30 then 29 else 30)%N in
  let tmp3 := (if 29 <? rs1 then rs1 else 29)%N in
  let o := newoffset l1 (Data iid oid sd z sb) 2 l2 (1 + Z.of_nat (List.length l2)) in
  map rv_decode (map Z.to_N b) =
    R5_Addi tmp3 rs1 (scast 12 32 (xbits n 20 32))%N ::
    R5_Andi tmp3 tmp3 4294967292 ::
    R5_Lw tmp1 tmp3 0 ::
    R5_Andi tmp2 tmp1 127 ::
    R5_Bne tmp2 0 16 ::
    R5_Srai tmp1 tmp1 5 ::
    R5_Add tmp3 tmp3 tmp1 ::
    R5_Lw tmp1 tmp3 0 ::
    R5_Lui tmp2 (Z.to_N (oid mod 2^20)) ::
    R5_Ori tmp2 tmp2 55 ::
    (if sb then R5_Bne tmp1 tmp2 (4 * o) :: nil
     else R5_Beq tmp1 tmp2 8 ::
          R5_Jal 0 (4 * o) :: nil ) ++
    R5_Jalr (xbits n 7 12) tmp3 0 :: nil.
Proof.
  intros.
  unfold newijump in NIJ. unfold_consts in NIJ. replace ((z #>> 15) #& 31) with (Z.of_N rs1) in NIJ; swap 1 2.
    unfold rs1, n, xbits. apply Z2N.inj_iff. apply N2Z.is_nonneg. apply Z.land_nonneg. right. discriminate 1.
    rewrite Z2N_inj_land, Z2N_inj_shiftr, <- N.land_ones. apply N2Z.id.
      exact OP0. discriminate 1. apply Z.shiftr_nonneg, OP0. discriminate 1.
  change 29 with (Z.of_N 29) in NIJ. change 30 with (Z.of_N 30) in NIJ. change 31 with (Z.of_N 31) in NIJ.
  rewrite <- N2Z_inj_eqb, !N2Z_inj_ltb, <- !N2Z_inj_ifbool in NIJ. fold tmp1 tmp2 tmp3 in NIJ.
  destruct newbranch as [br|] eqn:NB; [|discriminate]. apply invSome in NIJ. subst b.
  rewrite !map_cons, !map_app, !map_cons. simpl (map _ (map _ nil)).
  set (br' := map rv_decode (map Z.to_N br)). unfold rv_decode.
  rewrite !Z2N_inj_lor, !Z2N_inj_shiftl, !Z2N_inj_land by Z_nonneg. rewrite !N2Z.id.
  rewrite !N.land_lor_distr_l.
  rewrite <- !N.land_assoc, !N.land_0_r.
  rewrite !N_shiftl_land_0 by reflexivity. rewrite !N.lor_0_r. simpl (_ .& N.ones 7). simpl (Z.to_N (Zpos _)).
  change 127%N with (Z.to_N 127) at 1. rewrite <- Z2N_inj_land, OP103 by Z_nonneg. simpl (Z.to_N 103).
  rewrite <- (N.mod_small rs1 (2^5)) by (apply xbits_bound; discriminate).
  rewrite <- (N.mod_small tmp1 (2^5)) by (destruct (rs1 <? 31)%N; reflexivity).
  rewrite <- (N.mod_small tmp2 (2^5)) by (destruct (rs1 =? 30)%N; reflexivity).
  rewrite <- (N.mod_small tmp3 (2^5)) by (destruct (29 <? rs1)%N; [ apply xbits_bound; discriminate | reflexivity ]).
  rewrite <- !N.land_ones.

  unfold rv_decode_op.
  rewrite !xbits_lor, !xbits_shiftl, !xbits_land, !N.land_0_r, !N.lor_0_r.
  rewrite !N.land_lor_distr_l, N_shiftl_land_0, N.lor_0_r, !xbits_land_cancel_r by reflexivity.
  rewrite xbits_none', !N.shiftl_0_r, !N.lor_0_l, !N.lor_0_r, !xbits_0_land.
  simpl (xbits (Npos _) _ _). simpl (_ - _)%N. change (toZ 13%N _) with 16. change (toZ 12 0)%N with 0.
  rewrite (N.land_ones _ 20). change (2^20)%N with (Z.to_N (2^20)). rewrite <- Z2N.inj_mod, Z.mod_mod by Z_nonneg.
  fold n.

  unfold rv_decode_op_imm.
  rewrite !xbits_lor, !xbits_land, !xbits_shiftl, !xbits_none', !xbits_land.
  rewrite !N.shiftl_0_r, !N.land_0_r, !N.lor_0_r, !N.lor_0_l.
  rewrite !xbits_land_cancel_r by reflexivity.
  simpl (_ - _)%N. simpl (xbits (Npos _) _ _). cbv iota.
  change (scast 12 32 127)%N with 127. change (scast 12 32 55)%N with 55. change (scast 12 32 4092)%N with 4294967292.
  rewrite !xbits_0_land.

  repeat (apply f_equal2; [ reflexivity | ]).
  apply f_equal2; [|reflexivity].

  apply newbranch_asm in NB; [| (destruct (rs1 =? _)%N, (rs1 <? _)%N; (reflexivity + discriminate 1)).. ].
  subst br'. rewrite NB. clear NB. fold o.
  rewrite !Z2N_inj_lor, !Z2N_inj_shiftl, !N2Z.id by Z_nonneg.
  rewrite !N.land_lor_distr_l, !N_shiftl_land_0 by reflexivity.
  rewrite !xbits_lor, !xbits_shiftl, !xbits_none'.
  rewrite !N.lor_0_l, !N.lor_0_r, !N.shiftl_0_r.
  simpl (_ - _)%N. change (xbits _ 12 15) with 1%N.
  unfold rv_decode_branch, opposite_branch.
  replace (xbits tmp1 5 10) with N0 by (destruct (rs1 <? 31)%N; reflexivity).
  rewrite N.lor_0_l, !xbits_0_land. reflexivity.
Qed.

Theorem newauipc_asm:
  forall base l1 iid oid sd z sb b (OP0: 0 <= z)
    (NI: new_auipc base l1 (Data iid oid sd z sb) = Some b),
  let n := Z.to_N z in
  let rd := xbits n 7 12 in
  let t' := (base + Z.of_nat (length l1)) #<< 2 + z #& (2^32 - 2^12) in
  let t := Z.to_N (if 2048%Z <=? t' #& 4095%Z then t' + 4096%Z else t') in
  map rv_decode (map Z.to_N b) =
  if z #& 3968 =? 0 then R5_Xor 0 0 0 :: nil else
    R5_Lui rd (xbits t 12 32) ::
    R5_Addi rd rd (scast 12 32 (xbits (t << 20) 20 32))%N :: nil.
Proof.
  unfold new_auipc. unfold_consts. intros.
  destruct (_ && _)%bool eqn:B0; [|discriminate NI].
  destruct (_ =? 0). apply invSome in NI. subst b. reflexivity.
  destruct (2048 <=? _) eqn:Signed;
  apply andb_prop, proj1, Z.leb_le in B0;
  apply invSome in NI; subst b;
  unfold map, rv_decode;
  rewrite !Z2N_inj_lor, !Z.shiftl_land, !Z2N_inj_land by Z_nonneg;
  rewrite !N.land_lor_distr_l, <- !N.land_assoc, !N.land_0_r, !N.lor_0_r; simpl (_ .& N.ones 7);
  unfold rv_decode_op;
  rewrite !xbits_lor, !xbits_land, !N.land_0_r, !N.lor_0_r;
  change (xbits _ 12 15) with 0%N;
  unfold rv_decode_op_imm;
  rewrite !N.lor_0_l; rewrite !xbits_land_cancel_r by reflexivity;
  rewrite !xbits_lor, !xbits_land, !N.land_0_r, !N.lor_0_r, !N.lor_0_l;
  rewrite !xbits_land_cancel_r by reflexivity;
  rewrite Z2N_inj_shiftl, xbits_shiftl, N.shiftl_0_r by solve [ discriminate 1 | assumption ];
  rewrite Z2N_inj_shiftl by Z_nonneg; reflexivity.
Qed.

Theorem newauipc_exit:
  forall base l1 iid oid sd z sb b k z' s a s' x
    (OP0: 0 <= z)
    (NI: new_auipc base l1 (Data iid oid sd z sb) = Some b)
    (RC: nth_error b k = Some z')
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N z'))) s' x),
  x = None.
Proof.
  intros. apply newauipc_asm in NI; [|exact OP0].

  destruct (_ =? 0).
  destruct b. discriminate. destruct b; [|discriminate].
  unfold map in NI. apply invCons, proj1 in NI.
  destruct k; [|destruct k; discriminate RC]. apply invSome in RC. subst z'.
  rewrite NI in XS. inversion XS. reflexivity.

  repeat (destruct b; try discriminate).
  unfold map in NI. apply invCons in NI. destruct NI as [NI1 NI2]. apply invCons, proj1 in NI2.
  destruct k; [|destruct k; [| destruct k; discriminate RC]]; apply invSome in RC; subst z'.
    rewrite NI1 in XS. eapply r5mov_fallthru. exact XS.
    rewrite NI2 in XS. eapply r5mov_fallthru. exact XS.
Qed.

Theorem newtag_exit:
  forall d k z' s a s' x
    (RC: nth_error (newtag d) k = Some z')
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N z'))) s' x),
  s' = s /\ x = None.
Proof.
  intros. assert (ASM := newtag_asm d).
  destruct d as [iid oid sd z sb]. unfold newtag in *.
  destruct iid as [iid|]; [| destruct k; discriminate ].
  destruct k; [| destruct k; discriminate ].
  apply invSome in RC. subst z'.
  unfold map in ASM. apply invCons, proj1 in ASM. rewrite ASM in XS.
  inversion XS. split; reflexivity.
Qed.

Lemma simpl_jal_dest:
  forall n, ((4 * n) .& (N.ones 32 - 1) = (n mod 2^30) * 4)%N.
Proof.
  intro.
  change (_-_)%N with ((N.ones 30 << 2) .| 2). change 4%N with (2^2)%N.
  rewrite (N.mul_comm (_^_)), <- !N.shiftl_mul_pow2, N.land_lor_distr_r, (N_shiftl_land_0 _ _ 2),
          <- N.shiftl_land, N.land_ones by reflexivity.
  apply N.lor_0_r.
Qed.

Theorem newjump_exit:
  forall rd o' b k z' s a s' x
    (NJ: newjump rd o' = Some b)
    (RC: nth_error b k = Some z')
    (LO: 0 <= rd) (HI: rd < 32)
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N z'))) s' x),
  -2^18 <= o' < 2^18 /\
  x = Some (Addr (4 * (Z.to_N (Z.of_N a + o') mod 2^30))%N).
Proof.
  split.

  unfold newjump in NJ. destruct (andb _ _) eqn:BND; [|discriminate]. split.
    eapply Z.leb_le, proj1, andb_prop, BND.
    eapply Z.ltb_lt, proj2, andb_prop, BND.

  apply newjump_asm in NJ; [|assumption..].
  destruct b. discriminate. destruct b; [|discriminate].
  destruct k; [|destruct k; discriminate]. apply invSome in RC. subst z.
  unfold map in NJ. apply invCons, proj1 in NJ. rewrite NJ in XS. clear NJ.
  unfold rv2il in XS. rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N_inj_mul, simpl_jal_dest in XS by (left; discriminate).
  inversion XS; clear XS; subst.
    apply r5mov_fallthru in XS0. discriminate XS0.
    inversion XS0; clear XS0; subst. inversion E; clear E; subst. rewrite N.mul_comm. reflexivity.
Qed.

Lemma decode_opp_branch:
  forall n,
  opposite_branch n = rv_decode_branch (n .^ 1).
Proof.
  intros.
  destruct n as [|n]. reflexivity.
  destruct n; reflexivity.
Qed.

Theorem newbranch_exit:
  forall l1 d c l2 op i b k z' s a s' x a'
    (NB: newbranch l1 d c l2 op i = Some b)
    (OP0: 0 <= op) (OP99: op #& 127 = 99) (OP256: op #& 256 = 0)
    (RC: nth_error b k = Some z')
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N z'))) s' x)
    (EX: exitof (4 * N.succ a)%N x = Addr a')
    (END: (a + N.of_nat (length b - k) < 2^30)%N),
  ((exists j', a' = 4 * (a + j') /\ (N.to_nat j' <= length b - k)%nat) \/
   a' = 4 * (Z.to_N (Z.of_N a + Z.of_nat (length b - k) - 1 + newoffset l1 d c l2 i) mod 2^30))%N.
Proof.
  intros.
  destruct x as [x|].

    simpl in EX. subst x.
    destruct d as [iid oid sd z sb]. apply newbranch_asm in NB; try assumption.
    destruct sb.

      destruct b. discriminate. destruct b; [|discriminate].
      destruct k; [| destruct k; discriminate ]. apply invSome in RC. subst.
      apply invCons, proj1 in NB. rewrite NB in XS. clear NB. right.
      rewrite <- (N2Z.id 4), Z.add_simpl_r, <- N.Div0.mul_mod_distr_l by discriminate.
      rewrite <- Z2N_inj_mul by (left; discriminate).
      rewrite Z.mul_add_distr_l, <- N2Z.inj_mul.
      eapply exec_branch_taken, XS.

      destruct b. discriminate. destruct b. discriminate. destruct b; [|discriminate].
      apply invCons in NB. destruct NB as [NB1 NB2]. apply invCons, proj1 in NB2.
      destruct k; [| destruct k; [| destruct k; discriminate ] ].

        left. exists 2%N. split; [| reflexivity ].
        apply invSome in RC. subst. rewrite NB1 in XS. clear NB1 NB2.
        erewrite <- (N.mod_small (a+2)) by eassumption.
        rewrite <- N.Div0.mul_mod_distr_l, <- (N2Z.id (4*_)), N.mul_add_distr_l, N2Z.inj_add by discriminate.
        eapply exec_branch_taken. rewrite <- decode_opp_branch. exact XS.

        right. apply invSome in RC. subst. rewrite NB2 in XS. clear NB1 NB2.
        rewrite <- Z.add_sub_assoc, Z.add_0_r, <- N.Div0.mul_mod_distr_l, <- (N2Z.id 4) by discriminate.
        rewrite <- Z2N_inj_mul, Z.mul_add_distr_l, <- N2Z.inj_mul by (left; discriminate).

        unfold rv2il in XS.
        rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N_inj_mul, simpl_jal_dest in XS by (left; discriminate).
        inversion XS; clear XS; subst. solve [ inversion XS0 ].
        inversion XS1; clear XS1; subst. inversion XS0; clear XS0; subst. inversion E; clear E; subst.
        rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N_inj_mul, N.Div0.mul_mod_distr_l by (try left; discriminate).
        apply N.mul_comm.

    apply invAddr in EX. subst. left. exists 1%N. split. rewrite N.add_1_r. reflexivity.
    apply Nat.le_add_le_sub_l. rewrite Nat.add_1_r. apply Nat.le_succ_l, nth_error_Some. rewrite RC. discriminate.
Qed.

Lemma newijump_cfg:
  forall l1 iid oid sd z sb l2 b k ie s a s' x a'
    (NIJ: newijump l1 (Data iid oid sd z sb) l2 = Some b)
    (OPNN: 0 <= z)
    (OP103: z #& 127 = 103)
    (IE: nth_error b k = Some ie)
    (K: (k < Nat.pred (length b))%nat)
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N ie))) s' x)
    (EX: exitof (4 * N.succ a)%N x = Addr (4 * a')%N)
    (UB: (a + N.of_nat (length b - k) + Z.to_N (sumsizes l2) < 2^30)%N),
  (match k with
   | 4%nat => a' = N.succ a \/ a' = a + 4
   | 10%nat => a' = N.succ a \/ a' = a + if sb then N.of_nat (length b - k) + Z.to_N (sumsizes l2) else 2
   | 11%nat => sb = false /\ (a' = a + N.of_nat (length b - k) + Z.to_N (sumsizes l2))
   | _ => a' = N.succ a
   end)%N.
Proof.
  intros. apply newijump_asm in NIJ; try assumption.
  repeat (let r := fresh "r" in remember (if (_ _ _:bool) then _ else _ :N) as r eqn:H; clear H).
  remember (scast _ _ _) as imm eqn:H. clear H. remember (Z.to_N (_ mod _)) as imm0 eqn:H. clear H.
  repeat (let imm := fresh "imm" in remember (xbits _ _ _) as imm eqn:H; clear H).
  repeat (destruct b; [discriminate|]). rewrite !map_cons in NIJ.
  repeat (apply invCons in NIJ; destruct k;
  [ apply proj1 in NIJ; apply invSome in IE; rewrite <- IE, NIJ in XS;
    try (apply r5mov_fallthru in XS; rewrite XS in EX;
         apply invAddr, N.mul_cancel_l in EX; [|discriminate]; symmetry; exact EX)
  | apply proj2 in NIJ ]).
  destruct x as [x|].

    right. apply exec_stmt_r5branch in XS. change 16 with (4*Z.of_N 4) in XS. change (2^32)%N with (4*2^30)%N in XS.
    rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N.inj_mul, N.Div0.mul_mod_distr_l, Z2N.inj_add, !N2Z.id in XS by
      repeat (apply Z.add_nonneg_nonneg + apply N2Z.is_nonneg + discriminate).
    rewrite !length_cons, !Nat.sub_succ, !Nat.sub_0_r, 4!Nat2N.inj_succ, (N.add_comm a), <- !N.add_1_l,
            !N.add_assoc, (N.add_comm _ a), N.add_assoc, <- N.add_assoc in UB.
    rewrite N.mod_small in XS by (eapply N.le_lt_trans; [apply N.le_add_r|exact UB]).
    subst x. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. subst a'. reflexivity.

    left. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. symmetry. exact EX.

  destruct sb; repeat (destruct b; try discriminate); rewrite !map_cons in NIJ;
  repeat (apply invCons in NIJ; destruct k;
  [ apply proj1 in NIJ; apply invSome in IE; rewrite <- IE, NIJ in XS
  | apply proj2 in NIJ ]);
  try rewrite Z.add_1_l, <- Nat2Z.inj_succ in XS;
  try solve [ destruct k; discriminate | contradict K; apply Nat.lt_irrefl ].

    destruct x as [x|].

      right. apply exec_stmt_r5branch in XS. change (2^32)%N with (4*2^30)%N in XS.
      unfold newoffset in XS. rewrite sumnsizes_sumsizes, Zle_imp_le_bool, Nat2Z.id in XS by apply Nat2Z.is_nonneg.
      ereplace (S (length l2)) in XS; [ rewrite firstn_all in XS | reflexivity ].
      rewrite Z.add_0_l, sumsizes_cons, <- Z.add_assoc, Z.add_simpl_l in XS.
      rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N.inj_mul, N.Div0.mul_mod_distr_l, !Z2N.inj_add, !N2Z.id, (N.add_comm _ 2) in XS by
        repeat (apply Z.add_nonneg_nonneg + apply sumsizes_nonneg + apply N2Z.is_nonneg + discriminate).
      rewrite N.mod_small in XS by (rewrite N.add_assoc; exact UB).
      subst x. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. subst a'. reflexivity.

      left. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. symmetry. exact EX.

    destruct x as [x|].

      right. apply exec_stmt_r5branch in XS. change 8 with (4*2) in XS. change (2^32)%N with (4*2^30)%N in XS.
      rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N.inj_mul, N.Div0.mul_mod_distr_l, !Z2N.inj_add, !N2Z.id, (N.add_comm _ 2) in XS by
        repeat (apply Z.add_nonneg_nonneg + apply sumsizes_nonneg + apply N2Z.is_nonneg + discriminate).
      rewrite N.mod_small in XS by (apply N.lt_succ_l; rewrite <- N.add_succ_l, N.add_comm; eapply N.le_lt_trans; [ apply N.le_add_r | exact UB ] ).
      subst x. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. subst a'. apply N.add_comm.

      left. apply invAddr, N.mul_cancel_l in EX; [|discriminate]. symmetry. exact EX.

    split. reflexivity. rewrite N.mul_comm, Z.mul_comm, Nat2Z.inj_succ in XS.
    inversion XS; subst. solve [ inversion XS0 ].
    inversion XS0; subst. inversion E; subst. clear XS XS0 XS1 E. rewrite <- Nat2Z.inj_succ in EX.
    unfold newoffset in EX. rewrite sumnsizes_sumsizes, Zle_imp_le_bool, Nat2Z.id in EX by apply Nat2Z.is_nonneg.
    ereplace (S (length l2)) in EX; [ rewrite firstn_all in EX | reflexivity ].
    rewrite Z.add_0_l, sumsizes_cons, <- Z.add_assoc, Z.add_simpl_l in EX.
    rewrite N2Z.inj_mul, <- Z.mul_add_distr_r, Z2N.inj_mul, (N.mul_comm _ 4), simpl_jal_dest in EX by (Z_nonneg; try apply sumsizes_nonneg).
    rewrite !Z2N.inj_add, N2Z.id, (N.add_comm _ 2), N.add_assoc in EX by (Z_nonneg; try apply sumsizes_nonneg).
    rewrite N.mod_small, (N.mul_comm _ 4) in EX by exact UB.
    apply invAddr, N.mul_cancel_l in EX; [|discriminate]. subst a'. reflexivity.
Qed.

Corollary newijump_exit_internal:
  forall l1 iid oid sd z sb l2 b k ie s a s' x a'
    (NIJ: newijump l1 (Data iid oid sd z sb) l2 = Some b)
    (OPNN: 0 <= z)
    (OP103: z #& 127 = 103)
    (IE: nth_error b k = Some ie)
    (K: (k < Nat.pred (length b))%nat)
    (XS: exec_stmt s (rv2il (4 * a)%N (rv_decode (Z.to_N ie))) s' x)
    (EX: exitof (4 * N.succ a)%N x = Addr (4 * a')%N)
    (UB: (a + N.of_nat (length b - k) + Z.to_N (sumsizes l2) < 2^30)%N),
  ((exists j', a' = a + j' /\ (N.to_nat j' < length b - k)%nat) \/
   a' = (a + (N.of_nat (length b - k) + Z.to_N (sumsizes l2))))%N.
Proof.
  intros. eapply newijump_cfg in XS; try eassumption. apply newijump_size in NIJ.
  do 12 try (destruct k; [ try destruct XS as [XS|XS]; try solve [ left; eexists; split;
  [ rewrite N.add_1_r; exact XS
  | apply Nat.lt_add_lt_sub_l, Nat.lt_add_lt_sub_r; rewrite Nat.sub_1_r; exact K ] ] |]).

  left. eexists. split. exact XS. apply Nat.ltb_lt. rewrite NIJ. destruct sb; reflexivity.
  destruct sb.
    right. exact XS.
    left. eexists. split. exact XS. apply Nat.ltb_lt. rewrite NIJ. reflexivity.
  right. rewrite N.add_assoc. eapply proj2, XS.
  rewrite NIJ in K. apply Nat.ltb_lt in K. destruct sb; discriminate.
Qed.

Lemma mem_In:
  forall z sd, mem z sd = true -> In z sd.
Proof.
  unfold mem. intros.
  destruct in_dec as [?|?]. assumption. discriminate.
Qed.

Definition execution_IH l' bi j0 s0 n :=
  forall t : trace, (S (length t) < n)%nat ->
  forall s j q s' x j'
    (ENTRY: startof t (Addr (4 * N.of_nat j)%N, s) = (Addr (4 * N.of_nat (bi+j0))%N, s0))
    (XP: exec_prog rv_prog ((Addr (4 * N.of_nat j)%N, s)::t))
    (LU: rv_prog s (4 * N.of_nat j)%N = Some (4%N, q))
    (XS: exec_stmt s q s' x)
    (EX: exitof (4 * N.of_nat (S j))%N x = Addr (4 * N.of_nat j')%N),
  (bi <= j)%nat /\
  (indexmap' l' (j-bi) = indexmap' l' (j'-bi) \/
   blockboundary l' (j'-bi) \/
   j' < bi \/ bi + length (concat l') <= j')%nat.

Definition codebytes l' bi j0 s0 :=
  forall s t x m w i
    (ENTRY: startof t (x,s) = (Addr (4 * N.of_nat (bi+j0))%N, s0))
    (XP: exec_prog rv_prog ((x,s)::t))
    (MEM: s V_MEM32 = VaM m w),
  match nth_error (concat l') i with
  | Some ie => m Ⓓ[(4 * N.of_nat (bi+i))%N] = Z.to_N ie
  | None => True
  end.

Definition nonexecutable_data (l':list (list Z)) bi j0 s0 :=
  forall t s x e w i
    (ENTRY: startof t (x,s) = (Addr (4 * N.of_nat (bi+j0))%N, s0))
    (XP: exec_prog rv_prog ((x,s)::t))
    (EXEC: s A_EXEC = VaM e w)
    (OUT: (i < bi \/ bi + length (concat l') <= i)%nat),
  (e (4 * N.of_nat i) = 0)%N.

Lemma boundary_offset_iszero:
  forall l i k b
    (BB: blockboundary l (length (concat (firstn i l)) + k))
    (BLK: nth_error l i = Some b)
    (BND: (k < length b)%nat),
  k = O.
Proof.
  intros. destruct BB as [i0 BB]. destruct k. reflexivity. contradict BB. apply Nat.lt_gt_cases. destruct (Nat.le_gt_cases i0 i).
    right. rewrite <- (firstn_skipn i0 l) at 2. rewrite firstn_app, firstn_firstn, Nat.min_r, concat_app, app_length,
      <- Nat.add_assoc by assumption. apply Nat.lt_add_pos_r, Nat.add_pos_r, Nat.lt_0_succ.
    left. rewrite <- (firstn_skipn i l) at 2.
      rewrite firstn_app, firstn_firstn, Nat.min_r, concat_app, app_length by apply Nat.lt_le_incl, H.
      rewrite firstn_length_le by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
      apply Nat.sub_gt in H. destruct (i0 - i)%nat. contradiction.
      rewrite nth_skipn in BLK. destruct (skipn i l). discriminate. apply invSome in BLK. rewrite BLK.
      rewrite firstn_cons. rewrite concat_cons. rewrite app_length.
      apply Nat.add_lt_mono_l, Nat.lt_lt_add_r, BND.
Qed.

(*
Lemma exec_prev_in_block:
  forall l' bi j0 s0 n t i b k' s',
    let addr' x := Addr (4 * N.of_nat (bi + (length (concat (firstn i l')) + x)))%N in forall
    (IH: execution_IH l' bi j0 s0 n)
    (BLK : nth_error l' i = Some b)
    (BB: blockboundary l' j0)
    (ENTRY: startof t (addr' (S k'),s') = (Addr (4 * N.of_nat (bi+j0))%N, s0))
    (XP: exec_prog rv_prog ((addr' (S k'),s')::t))
    (BND: (S k' < length b)%nat),
  exists s1 k t', (k < length b)%nat /\ t = (addr' k, s1)::t' /\
    n = S n0 /\ (k < length b)%nat /\
    exec_prog rv_prog (4 * N.of_nat (bi+j0))%N s0 n0 s1 (addr' k) /\
    exec_prog rv_prog (addr' k) s1 1 s' (addr' (S k')).
Proof.
  intros. destruct n as [|n0].
    set (m4 := N.mul 4) in XP. inversion XP; subst. subst m4. apply N.mul_cancel_l, Nat2N.inj, Nat.add_cancel_l in H; [|discriminate]. subst j0.
    destruct BB as [i0 BB]. exfalso. destruct (Nat.le_ge_cases i0 i).

      rewrite <- (firstn_skipn i0 l') in BB at 1. 
      rewrite firstn_app, firstn_firstn, Nat.min_r, concat_app, app_length, <- Nat.add_assoc, <- Nat.add_0_r in BB by assumption.
      apply Nat.add_cancel_l, Nat.eq_add_0, proj2 in BB. discriminate.

      rewrite <- (firstn_cons_skipn _ _ _ _ BLK) in BB at 2.
      rewrite firstn_app, firstn_firstn, Nat.min_r, concat_app, app_length in BB by assumption.
      apply Nat.add_cancel_l in BB. revert BND. apply Nat.le_ngt. rewrite BB.
      destruct (_-_)%nat. discriminate.
      rewrite firstn_cons, concat_cons, app_length. apply Nat.le_add_r.

  rewrite <- Nat.add_1_r in XP. apply exec_prog_split in XP. destruct XP as [s1 [a [XP1 XP2]]].
  inversion XP2; clear XP2; subst. rewrite N.mul_comm in XP. inversion XP; clear XP; subst.
  assert (LU':=LU). unfold rv_prog in LU'. destruct (s1 V_MEM32), (s1 A_EXEC); try discriminate. destruct (m0 a). discriminate.
  unfold rv_stmt in LU'. destruct (a mod 4)%N eqn:A4; [| inversion LU'; subst; inversion XS; subst; discriminate ].
  inversion LU'. subst sz. clear LU' H1.
  rewrite (N.div_mod' a 4), A4, N.add_0_r in XP1, LU, EX. rewrite (N.mul_comm _ 4) in EX.
  specialize (IH n0 (Nat.lt_succ_diag_r _) s1 (N.to_nat (a/4)) q s' x1 (bi + (length (concat (firstn i l')) + S k'))%nat).
  assert (AS: (forall x y, x + y - x = y)%nat). intros. rewrite Nat.add_comm. apply Nat.add_sub.
  rewrite Nat2N.inj_succ, N2Nat.id, N.mul_succ_r, AS in IH. specialize (IH XP1 LU XS EX).
  destruct IH as [HI [IH|[IH|[IH|IH]]]].

    rewrite indexmap_length, Nat.min_l in IH by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
    assert (H:=BLK). rewrite nth_skipn in H. unfold hd_error in H. destruct (skipn i l') as [|b' t]. discriminate. apply invSome in H. subst b'.
    unfold indexmap' in IH at 2. rewrite (proj2 (Nat.ltb_lt _ _) BND), Nat.add_0_r in IH.
    exists n0, s1, (N.to_nat (a/4) - (bi + length (concat (firstn i l'))))%nat.
    rewrite Nat.add_assoc, le_pmr by (rewrite <- IH; etransitivity;
    [ apply Nat.add_le_mono_l, firstn_indexmap_above | rewrite le_pmr by exact HI; reflexivity ]).
    rewrite N2Nat.id. repeat split.

      apply -> Nat.le_succ_l. rewrite <- Nat.sub_succ_l by (rewrite <- IH; etransitivity;
      [ apply Nat.add_le_mono_l, firstn_indexmap_above | rewrite le_pmr by exact HI; reflexivity ]).
      apply Nat.le_sub_le_add_l, Nat.le_succ_l. rewrite <- Nat.add_assoc, <- app_length, concat_last, firstn_app_nth by exact BLK.
      rewrite <- IH. eapply Nat.le_lt_trans; [| apply Nat.add_lt_mono_l, firstn_indexmap_below].
        rewrite le_pmr by exact HI. reflexivity.
      apply Nat.nle_gt. intro H. rewrite (proj2 (nth_error_None _ _)) in BLK. discriminate.
      rewrite <- (app_nil_r l'), indexmap_app2, Nat.add_0_r in IH by apply H. rewrite IH. reflexivity.

      exact XP1.

      eapply XStep. exact LU. exact XS. exact EX. apply XDone.

    eapply boundary_offset_iszero in IH. discriminate. exact BLK. exact BND.

    contradict IH. apply Nat.le_ngt, Nat.le_add_r.

    contradict IH. apply Nat.lt_nge. rewrite <- (firstn_skipn i l') at 2. rewrite concat_app, app_length.
    apply Nat.add_lt_mono_l. rewrite nth_skipn in BLK. destruct (skipn i l'). discriminate.
    apply invSome in BLK. rewrite BLK, concat_cons, app_length. apply Nat.add_lt_mono_l, Nat.lt_lt_add_r, BND.
Qed.

Inductive rv_trace h a0 s0: list (addr * store) -> addr -> store -> Prop :=
| RVT_End: rv_trace h a0 s0 nil a0 s0
| RVT_Step q x a1 s1 t a' s'
    (LU: rv_prog s0 (4 * a0)%N = Some (4%N, q))
    (XS: exec_stmt h s0 q s1 x)
    (EX: exitof (4 * N.succ a0) x = Exit (4 * a1))
    (TR: rv_trace h a1 s1 t a' s'):
  rv_trace h a0 s0 ((a1,s1)::t) a' s'.

Lemma trace_append:
  forall t1 t2 h a0 a1 a2 s0 s1 s2
    (TR1: rv_trace h a0 s0 t1 a1 s1) (TR2: rv_trace h a1 s1 t2 a2 s2),
  rv_trace h a0 s0 (t1++t2) a2 s2.
Proof.
  induction t1; intros.
    inversion TR1. exact TR2.
    simpl. destruct a. inversion TR1; subst. eapply RVT_Step; try eassumption. eapply IHt1; eassumption.
Qed.

Definition inblock bi (l': list (list Z)) i (p : addr * store) :=
  (N.of_nat (bi + length (concat (firstn i l'))) < fst p < N.of_nat (bi + length (concat (firstn (S i) l'))))%N.

Lemma exec_start_block:
  forall l' h bi j0 s0 n i b k' s'
    (IH: execution_IH l' h bi j0 s0 n)
    (BLK : nth_error l' i = Some b)
    (BB: blockboundary l' j0)
    (XP: exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n s' (Exit (4 * N.of_nat (bi + (length (concat (firstn i l')) + k')))))
    (BND: (k' < length b)%nat),
  exists s1 t,
    exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 (n - length t) s1 (Exit (4 * N.of_nat (bi + length (concat (firstn i l'))))) /\
    rv_trace h (N.of_nat (bi + length (concat (firstn i l')))) s1 t (N.of_nat (bi + (length (concat (firstn i l')) + k'))) s' /\
    Forall (inblock bi l' i) t.
Proof.
  set (m4 := N.mul 4). intros. revert n k' s' XP BND IH. induction n; intros.

    exists s0, nil.
    inversion XP; subst; subst m4. apply N.mul_cancel_l in H; [|discriminate]. apply Nat2N.inj, Nat.add_cancel_l in H. subst j0.
    replace k' with O.
      rewrite Nat.add_0_r. repeat split. apply XDone. apply RVT_End. apply Forall_nil.
      symmetry. eapply boundary_offset_iszero; eassumption.

    destruct k'.

      exists s', nil. rewrite Nat.add_0_r, Nat.sub_0_r. rewrite Nat.add_0_r in XP. repeat split.
        exact XP. apply RVT_End. apply Forall_nil.

      eapply exec_prev_in_block in XP; [|eassumption..]. destruct XP as [m [s1 [k [H [BND0 [XP1 XP3]]]]]].
      inversion H; clear H; subst m. specialize (IHn k s1 XP1 BND0). destruct IHn as [s2 [t2 [XP1' [RVT FA]]]].
        intros m LT. apply IH. apply Nat.lt_lt_succ_r, LT.

        inversion XP3; clear XP3; subst.
        replace sz with 4%N in * by (unfold rv_prog in LU;
          destruct (s1 V_MEM32); [|destruct (s1 A_EXEC); [|destruct (m0 _)]]; try discriminate; inversion LU; reflexivity ).
        fold m4 in XP. inversion XP; clear XP; subst. subst m4.
          eexists s2, (t2++_::nil). repeat split.
            rewrite app_length, length_cons, Nat.add_1_r, Nat.sub_succ. exact XP1'.
            eapply trace_append. exact RVT. eapply RVT_Step.
              exact LU. exact XS. rewrite N.mul_succ_r. exact EX. apply RVT_End.
            apply Forall_app. exact FA. apply Forall_cons; [|apply Forall_nil]. split.
              apply Nat2N_lt, Nat.add_lt_mono_l, Nat.lt_add_pos_r, Nat.lt_0_succ.
              rewrite firstn_last, BLK, concat_app, concat_cons, app_nil_r, app_length. apply Nat2N_lt, Nat.add_lt_mono_l, Nat.add_lt_mono_l, BND.
Qed.
*)

Lemma notLui0_imp_not55:
  forall b
    (NN: Forall (Z.le 0) b)
    (ASM: Forall (fun a => match a with R5_Lui 0 _ => False | _ => True end) (map rv_decode (map Z.to_N b))),
  Forall (fun ie => ie #& 4095 <> 55) b.
Proof.
  intros. rewrite map_map in ASM. apply Forall_forall. intros a IN OP55.
  assert (RS0:=OP55). apply (f_equal (fun x => x #>> 7)) in RS0. rewrite Z.shiftr_land in RS0.
    change (4095 #>> 7) with 31 in RS0. change (55 #>> 7) with 0 in RS0.
  apply (f_equal (fun x => x #& 127)) in OP55. rewrite <- Z.land_assoc in OP55.
    change (4095 #& 127) with 127 in OP55. change (55 #& 127) with 55 in OP55.
  assert (A0: 0 <= a). eapply Forall_forall; eassumption.
  assert (DEC := proj1 (Forall_forall _ _) ASM _ (in_map _ _ _ IN)). simpl in DEC.
  unfold rv_decode in DEC. change (N.ones 7) with (Z.to_N 127) in DEC.
  rewrite <- Z2N_inj_land, OP55 in DEC; [| apply (proj1 (Forall_forall _ _) NN a IN) | discriminate ].
  simpl in DEC. unfold xbits in DEC. rewrite <- N.land_ones in DEC.
  change 7%N with (Z.to_N 7) in DEC. change (N.ones _) with (Z.to_N 31) in DEC.
  rewrite <- Z2N_inj_shiftr, <- Z2N_inj_land, RS0 in DEC by Z_nonneg.
  apply DEC.
Qed.

Lemma newinstr_notags:
  forall base l1 d l2 b (NI: newinstr base l1 d l2 = Some b),
  Forall (fun ie => ie #& 4095 <> 55) b.
Proof.
  intros. destruct d as [iid oid sd z sb].
  unfold newinstr in NI. unfold_consts in NI.
  destruct (z <? 0) eqn:OP0; [discriminate|]. apply Z.ltb_ge in OP0.

  destruct (z #& 4095 =? 55) eqn:OP55.
  destruct mem; [|discriminate]. apply invSome in NI. subst b.
  apply Forall_cons. discriminate. apply Forall_nil.

  destruct (z #& 127 =? 23).
  apply notLui0_imp_not55. eapply newauipc_nonneg. exact NI.
  apply newauipc_asm in NI; [|exact OP0]. destruct (_ =? 0) eqn:H1.

    destruct b. discriminate. destruct b; [|discriminate]. unfold map.
    apply invCons, proj1 in NI. rewrite NI.
    apply Forall_cons. exact I. apply Forall_nil.

    destruct b. discriminate. destruct b. discriminate. destruct b; [|discriminate]. unfold map.
    apply invCons in NI. destruct NI as [NI1 NI2]. apply invCons, proj1 in NI2. rewrite NI1, NI2.
    repeat constructor. destruct xbits eqn:H2; [|exact I].
    apply Z.eqb_neq in H1. apply H1.
    apply Z2N.inj; Z_nonneg. rewrite Z2N_inj_land; Z_nonneg.
    rewrite <- (recompose_bytes 7 (Z.to_N z)). unfold xbits in H2.
    rewrite <- N.land_ones, N.land_lor_distr_l, <- N.land_assoc, N.land_0_r.
    change (Z.to_N 3968) with (N.ones (12-7) << 7). rewrite <- N.shiftl_land, N.land_ones, H2.
    reflexivity.

  destruct (z #& 127 =? 99) eqn:OP99. apply Z.eqb_eq in OP99.
  destruct andb eqn:OP256; [|discriminate]. do 4 apply andb_prop, proj1 in OP256. apply Z.eqb_eq in OP256.
  assert (NN:=NI). apply newbranch_nonneg in NN.
  apply newbranch_asm in NI; [|assumption..].
  apply notLui0_imp_not55. exact NN. rewrite NI. destruct sb.
    apply Forall_cons; try apply Forall_nil.
      destruct (_ .| _) as [|op]. exact I. repeat (exact I + destruct op).
    repeat apply Forall_cons; try apply Forall_nil.
      destruct (_ .| _) as [|op]. exact I. repeat (exact I + destruct op).
      exact I.

  destruct (z #& 127 =? 103) eqn:OP103. apply Z.eqb_eq in OP103.
  assert (NN:=NI). apply newijump_nonneg in NN.
  apply newijump_asm in NI; [|assumption..].
  apply notLui0_imp_not55. exact NN. rewrite NI.
  destruct sb; repeat apply Forall_cons; try (exact I + apply Forall_nil);
    destruct (_ =? 30)%N; exact I.

  destruct (z #& 127 =? 111).
  destruct andb; [|discriminate].
  assert (NN:=NI). apply newjump_nonneg in NN; [|Z_nonneg].
  apply newjump_asm in NI; [|Z_nonneg|].
    apply notLui0_imp_not55. exact NN. rewrite NI. apply Forall_cons. exact I. apply Forall_nil.
    change 31 with (Z.ones 5). rewrite Z.land_ones by discriminate 1. apply Z.mod_pos_bound. reflexivity.

  destruct mem; [|discriminate]. apply invSome in NI. subst b.
  apply Forall_cons. apply Z.eqb_neq, OP55. apply Forall_nil.
Qed.

Lemma tags_at_blockboundaries:
  forall base l2 l1 l' j ie
    (NC: newinstrs base nil l1 l2 = Some l')
    (NTH: nth_error (concat l') j = Some ie)
    (OP55: ie #& 4095 = 55),
  exists i d, j = length (concat (firstn i l')) /\
    nth_error l2 i = Some d /\
    match d with Data (Some iid) _ _ _ _ => ie #>> 12 = iid mod 2^20 | _ => False end.
Proof.
  intros base l2 l1 l'. rewrite newinstrs_newinstrs', app_nil_l. revert l1 l'. induction l2 as [|d]; intros.
    apply invSome in NC. subst l'. destruct j; discriminate.

    unfold newinstrs' in NC; fold newinstrs' in NC.
    destruct newinstr as [b|] eqn:NI; [|discriminate]. simpl in NC. destruct optlist as [l|] eqn:NIS; [|discriminate].
    apply invSome in NC. subst l'.
    rewrite concat_cons in NTH. destruct (Nat.lt_ge_cases j (length (newtag d ++ b))) as [TBL|TBL].

      rewrite nth_error_app1 in NTH by exact TBL. destruct (Nat.lt_ge_cases j (length (newtag d))) as [TB|TB].

        rewrite nth_error_app1 in NTH by exact TB. exists O,d. unfold newtag in NTH. destruct d as [[iid|] oid sd z sb].

          destruct j; [|destruct j; discriminate]. apply invSome in NTH. subst ie. repeat split.
          rewrite Z.shiftr_lor, Z.lor_0_l, Z.shiftr_shiftl_r by discriminate. apply Z.shiftr_0_r.

          contradict TB. apply Nat.nlt_0_r.

        rewrite nth_error_app2 in NTH by exact TB. apply nth_error_In in NTH.
        contradict OP55. pattern ie. revert ie NTH. eapply Forall_forall, newinstr_notags, NI.

      rewrite nth_error_app2 in NTH by exact TBL.
      specialize (IHl2 _ _ _ _ NIS NTH OP55). destruct IHl2 as [i1 [d1 [BB [NTH1 OID]]]].
      exists (S i1), d1. repeat split; try assumption.
      rewrite firstn_cons, concat_cons, app_length, <- BB. symmetry. rewrite Nat.add_comm. apply Nat.sub_add, TBL.
Qed.

Lemma nth_error_concat {A}:
  forall ll l i j (x:A),
  nth_error ll i = Some l -> nth_error l j = Some x -> nth_error (concat ll) (length (concat (firstn i ll)) + j) = Some x.
Proof.
  intros.
  rewrite <- (firstn_skipn i ll) at 1. rewrite concat_app, nth_error_app2, Nat.add_comm, Nat.add_sub by apply Nat.le_add_r.
  rewrite nth_skipn in H. destruct skipn. discriminate. apply invSome in H. subst l0.
  rewrite concat_cons, nth_error_app1. assumption. apply nth_error_Some. rewrite H0. discriminate.
Qed.

(*
Lemma step_in_block {l' h bi j0 s0 n1 s1 i t s' k' b ie}:
  forall k1
    (CODE: codebytes l' h bi j0 s0)
    (XP: exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n1 s1 (Exit (4 * N.of_nat (bi + (length (concat (firstn i l')) + k1)))))
    (TR: rv_trace h (N.of_nat (bi + (length (concat (firstn i l')) + k1))) s1 t (N.of_nat (bi + (length (concat (firstn i l')) + k'))) s')
    (BLK: nth_error l' i = Some b)
    (IE: nth_error b k1 = Some ie)
    (END: (k' - k1 <> 0)%nat),
  exists s2 x a' t2,
    exec_stmt h s1 (rv2il (4 * N.of_nat (bi + (length (concat (firstn i l')) + k1))) (rv_decode (Z.to_N ie))) s2 x /\
    exitof (4 * N.of_nat (bi + (length (concat (firstn i l')) + S k1))) x = Exit (4 * a') /\
    t = (a',s2)::t2 /\
    exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 (S n1) s2 (Exit (4 * a')) /\
    rv_trace h a' s2 t2 (N.of_nat (bi + (length (concat (firstn i l')) + k'))) s'.
Proof.
  set (m4 := N.mul 4). intros.
  destruct t. contradict END.
    inversion TR. apply Nat2N.inj, Nat.add_cancel_l, Nat.add_cancel_l in H. subst k'. apply Nat.sub_diag.
  specialize (CODE s1).
  destruct p. inversion TR; clear TR; subst.
  assert (LU1:=LU). unfold rv_prog in LU1. destruct (s1 V_MEM32); [|destruct (s1 A_EXEC); [|destruct (m0 _)]]; try discriminate.
  specialize (CODE _ _ _ _ (length (concat (firstn i l')) + k1)%nat XP (eq_refl _)).
  erewrite nth_error_concat in CODE by eassumption.
  unfold rv_stmt in LU1. rewrite CODE in LU1. rewrite N.mul_comm, N.mod_mul in LU1 by discriminate.
  inversion LU1; clear LU1; subst. subst m4. eexists _, _, _, _. repeat split.
    rewrite N.mul_comm. exact XS.
    rewrite !Nat.add_succ_r, Nat2N.inj_succ. exact EX.
    eapply exec_prog_append in XP; [| exact LU | exact XS ]. unfold exitof in EX. rewrite <- N.mul_succ_r, EX in XP. exact XP.
    exact TR0.
Qed.

Corollary step_after_tag {l' h bi j0 s0 n1 s1 i t s' k' d b ie}:
  forall k1
    (CODE: codebytes l' h bi j0 s0)
    (XP: exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n1 s1 (Exit (4 * N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + k1))))))
    (TR: rv_trace h (N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + k1)))) s1 t (N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + k')))) s')
    (BLK: nth_error l' i = Some (newtag d ++ b))
    (IE: nth_error b k1 = Some ie)
    (END: (k' - k1 <> 0)%nat),
  exists s2 x a' t2,
    exec_stmt h s1 (rv2il (4 * N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + k1)))) (rv_decode (Z.to_N ie))) s2 x /\
    exitof (4 * N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + S k1)))) x = Exit (4 * a') /\
    t = (a',s2)::t2 /\
    exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 (S n1) s2 (Exit (4 * a')) /\
    rv_trace h a' s2 t2 (N.of_nat (bi + (length (concat (firstn i l')) + (length (newtag d) + k')))) s'.
Proof.
  intros. rewrite Nat.add_succ_r. eapply step_in_block; try eassumption.
    rewrite nth_error_app2, Nat.add_comm, Nat.add_sub by apply Nat.le_add_r. exact IE.
    rewrite Nat.sub_add_distr, Nat.add_comm, Nat.add_sub. exact END.
Qed.
*)

Lemma rv_varid_nonmem:
  forall id, V_MEM32 <> rv_varid id.
Proof.
  intro. destruct id as [|id]. discriminate.
  repeat (destruct id as [id|id|]; try discriminate).
Qed.

Lemma r5mov_nomem:
  forall s n e s' x (XS: exec_stmt s (r5mov n e) s' x),
  s' V_MEM32 = s V_MEM32.
Proof.
  intros. destruct n as [|n].
    inversion XS. reflexivity.
    unfold r5mov in XS. set (v := rv_varid _) in XS. inversion XS. apply update_frame, rv_varid_nonmem.
Qed.

Lemma rv_varid_nontmp:
  forall id, V_TMP <> rv_varid id.
Proof.
  intro. destruct id as [|id]. discriminate.
  repeat (destruct id as [id|id|]; try discriminate).
Qed.

Lemma r5mov_notmp:
  forall s n e s' x (XS: exec_stmt s (r5mov n e) s' x),
  s' V_TMP = s V_TMP.
Proof.
  intros. destruct n as [|n].
    inversion XS. reflexivity.
    unfold r5mov in XS. set (v := rv_varid _) in XS. inversion XS. apply update_frame, rv_varid_nontmp.
Qed.

Lemma newijump_indirect_exit:
  forall base l l' i iid oid sd z sb b ie bi j0 s0 n s t s' x' j',
  let a' := (4 * N.of_nat (bi + Nat.pred (length (concat (firstn (S i) l')))))%N in forall
    (IH: execution_IH l' bi j0 s0 n)
    (CODE: codebytes l' bi j0 s0)
    (SIZ: (N.of_nat (bi + length (concat l')) < 2^30)%N)
    (NC: newinstrs base nil nil l = Some l')
    (DAT: nth_error l i = Some (Data iid oid sd z sb))
    (OP0: 0 <= z) (OP103: z #& 127 = 103)
    (BLK: nth_error l' i = Some (newtag (Data iid oid sd z sb) ++ b))
    (NIJ: newijump (rev (firstn i l)) (Data iid oid sd z sb) (skipn (S i) l) = Some b)
    (IE: nth_error b (Nat.pred (length b)) = Some ie)
    (BB: blockboundary l' j0)
    (ENTRY: startof t (Addr a', s) = (Addr (4 * N.of_nat (bi+j0))%N, s0))
    (XP: exec_prog rv_prog ((Addr a', s)::t))
    (XS': exec_stmt s (rv2il (4 * N.of_nat (bi + Nat.pred (length (concat (firstn (S i) l')))))%N (rv_decode (Z.to_N ie))) s' x')
    (EX': exitof (4 * N.of_nat (bi + length (concat (firstn (S i) l'))))%N x' = Addr (4 * N.of_nat j')%N)
    (HI: (bi <= j')%nat),
  match nth_error l (indexmap' l' (j'-bi)) with
  | Some (Data (Some iid') _ _ _ _) => blockboundary l' (j'-bi) /\ eqm (2^20) oid iid'
  | None => (bi + length (concat l') <= j')%nat
  | _ => False
  end.
Proof.
  set (m4 := N.mul 4). intros. subst a'.
  rewrite firstn_last, BLK, concat_app, concat_cons, app_nil_r, app_length, <- Nat.add_pred_r in XP
    by (erewrite app_length, newijump_size with (b:=b) by exact NIJ; destruct iid, sb; discriminate 1).
  eapply exec_start_block in XP; [| exact IH | exact BLK | exact BB
  | apply Nat.lt_pred_l; erewrite app_length, newijump_size with (b:=b) by exact NIJ; destruct iid, sb; discriminate 1 ].
  destruct XP as [s1 [t [XP [TR INB]]]].
  rewrite app_length, <- Nat.add_pred_r in TR by (erewrite newijump_size by exact NIJ; destruct sb; discriminate 1).
  set (ilen := length (concat (firstn i l'))) in XP, TR.
  set (taglen := length (newtag (Data iid oid sd z sb))) in TR.
(*
  set (n1 := (n - length t)%nat) in XP. clearbody n1. clear n IH.
  remember (length t) as tlen eqn:TLEN. revert t n1 s1 s s' x' j' TLEN XP TR INB XS' EX'. pattern tlen. apply strong_induction. intros. clear tlen TLEN. move IH at top.
*)
  destruct (nth_error l (indexmap' l' (j'-bi))) as [d'|] eqn:DAT';
  [| erewrite <- (firstn_all2 l') by (rewrite (newinstrs_length NC); apply nth_error_None, DAT');
     etransitivity;
     [ apply Nat.add_le_mono_l, firstn_indexmap_above
     | rewrite Nat.add_comm, (Nat.sub_add _ _ HI); reflexivity ] ].

  (* Execute the tag, if one exists. *)
  assert (H: exists n1 t1,
      exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n1 s1 (Exit (4 * N.of_nat (bi + (ilen + taglen)))) /\
      rv_trace h (N.of_nat (bi + (ilen + taglen))) s1 t1 (N.of_nat (bi + (ilen + (taglen + Nat.pred (length b))))) s /\
      Forall (inblock bi l' i) t1).
  destruct iid as [iid|].
    rewrite <- (Nat.add_0_r ilen) in XP, TR at 1.
    destruct (step_in_block 0 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]].
      rewrite Nat.sub_0_r. intro H. apply Nat.eq_add_0, proj1 in H. discriminate H.
    destruct (newtag_exit (Data (Some iid) oid sd z sb) 0 _ _ _ _ _ _ (eq_refl _) XS). subst s2 x.
    apply invExit, N.mul_cancel_l in EX; [|discriminate 1]. subst a.
    eexists _, _. repeat split. exact XP'. exact TR'. rewrite TL in INB. eapply Forall_tail, INB.

    rewrite Nat.add_0_r. eexists _, _. repeat split; eassumption.

  clear n t IH XP TR INB. destruct H as [n [t [XP [TR INB]]]].

  (* Execute the rest of the block *)
  apply newijump_asm in NIJ; [| exact OP0 | exact OP103 ].
  set (rs1 := xbits (Z.to_N z) 15 20) in NIJ.
  replace (if rs1 <? 31 then 31 else 29)%N with (N.pos (if (rs1 <? 31)%N then 31 else 29)) in NIJ by (destruct (rs1 <? 31)%N; reflexivity).
  set (tmp1 := (if (rs1 <? 31)%N then 31 else 29)%positive) in NIJ.
  replace (if rs1 =? 30 then 29 else 30)%N with (N.pos (if (rs1 =? 30)%N then 29 else 30)) in NIJ by (destruct (rs1 =? 30)%N; reflexivity).
  set (tmp2 := (if (rs1 =? 30)%N then 29 else 30)%positive) in NIJ.
  replace (if 29 <? rs1 then rs1 else 29)%N with (N.pos (if (29 <? rs1)%N then N.succ_pos (N.pred rs1) else 29)) in NIJ by
  ( destruct (29 <? rs1)%N eqn:H; [ rewrite N.succ_pos_spec; apply N.succ_pred_pos; transitivity 29%N; [ reflexivity | apply N.ltb_lt, H ] | reflexivity ] ).
  set (tmp3 := (if (29 <? rs1)%N then _ else 29)%positive) in NIJ.
  set (v1 := rv_varid (N.pos tmp1)). set (v2 := rv_varid (N.pos tmp2)). set (v3 := rv_varid (N.pos tmp3)).
  assert (V12: v1 <> v2). destruct rs1 as [|rs1]; repeat (discriminate 1 + destruct rs1).
  assert (V31: v3 <> v1). destruct rs1 as [|rs1]; repeat (discriminate 1 + destruct rs1).
  assert (V32: v3 <> v2). destruct rs1 as [|rs1]; repeat (discriminate 1 + destruct rs1).

  repeat (destruct b; [discriminate|]). rewrite !map_cons in NIJ.
  repeat (apply invCons in NIJ; let H := fresh "ASM0" in destruct NIJ as [H NIJ]).
  simpl in IE. simpl Nat.pred in TR. rewrite <- (Nat.add_0_r taglen) in XP, TR at 1.

  assert (H: exists m2 a' s2 n2 t2,
      exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n2 s2 (Exit (4 * N.of_nat (bi + (ilen + (taglen + 8))))) /\
      rv_trace h (N.of_nat (bi + (ilen + (taglen + 8)))) s2 t2 (N.of_nat (bi + (ilen + (taglen + (length b + 9))))) s /\
      Forall (inblock bi l' i) t2 /\
      s2 V_MEM32 = Ⓜm2 /\
      s2 v3 = Ⓓa' /\ (a' < 2^32)%N /\ (a' mod 4 = 0)%N /\
      s2 v1 = Ⓓm2 Ⓓ[a']).

    (* Addi tmp3, rs1, imm *)
    destruct (step_after_tag 0 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
    [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
    rewrite ASM0 in XS. unfold rv2il, r5mov in XS. fold v3 in XS. set (u_rs1 := r5var rs1) in XS.
    inversion XS; clear XS. subst v e s2 x. apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.
    destruct u as [a1 w1|]; [|solve [inversion E]].
    inversion E; clear E. subst bop e1 e2 w. assert (A1LO: (a1 < 2^w1)%N). subst a1. apply N.mod_lt, N.pow_nonzero. discriminate 1. clear H.
    inversion E2; clear E2; subst. clear u_rs1 n1 E1.

    (* Andi tmp3, tmp3, -3 *)
    destruct (step_after_tag 1 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
    [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
    rewrite ASM1 in XS. unfold rv2il, r5mov, r5var in XS. fold v3 in XS.
    inversion XS; clear XS. subst v e s2 x. apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.
    inversion E; clear E; subst. rewrite update_cancel in XP, TR. unfold eval_binop in XP, TR.
    inversion E1; clear E1; subst. rewrite update_updated in H. inversion H; clear H; subst n1 w.
    inversion E2; clear E2; subst. apply (land_bound _ _ 4294967292) in A1LO.

    (* Lw tmp1, tmp3, 0 *)
    destruct (step_after_tag 2 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
    [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
    rewrite ASM2 in XS. unfold rv2il, r5mov, r5var in XS. fold v1 v3 in XS.
    inversion XS; clear XS. subst v e s2 x. apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.
    inversion E; clear E R; subst. exists m.
    inversion E1; clear E1; subst. rename H into MEM1. erewrite <- (update_frame (s1[v3:=_]) v1) in MEM1;
    [ eassert (CODE1:=CODE _ _ _ _ _ (N.to_nat (m Ⓓ[a] / 4)) XP MEM1)
    | apply rv_varid_nonmem ].
    rewrite Nat2N.inj_add, N2Nat.id in CODE1. rewrite !update_frame in MEM1 by apply rv_varid_nonmem.
    inversion E2; clear E2; subst.
    inversion E0; clear E0; subst. rewrite N.add_0_r in CODE1, XP, TR.
    inversion E1; clear E1; subst. rewrite update_updated in H. inversion H; clear H; subst n1.
    rewrite N.mod_small in XP, TR, CODE1 by apply A1LO. change (Mb * 4)%N with 32%N in XP, TR.
    set (n1 := m Ⓓ[ a1 .& 4294967292 ]) in XP, TR.

    (* Andi tmp2, tmp1, 127 *)
    destruct (step_after_tag 3 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
    [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
    rewrite ASM3 in XS. unfold rv2il, r5mov, r5var in XS. fold v1 v2 in XS.
    inversion XS; clear XS; subst. inversion E; clear E. unfold eval_binop in H3. subst.
      inversion E1; clear E1. rewrite update_updated in H. inversion H; clear H. subst v n0 w.
      inversion E2; clear E2; subst.
    apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.

    (* Bne tmp2, x0, +16 *)
    destruct (step_after_tag 4 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
    [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
    rewrite ASM4 in XS. unfold rv2il, r5var, r5branch in XS. fold v2 in XS.
    change 16 with (Z.of_N (4*N.of_nat 4)) in XS. rewrite <- N2Z.inj_add, N2Z.id, <- N.mul_add_distr_l in XS.
    change (2^32)%N with (4*2^30)%N in XS. rewrite N.mul_mod_distr_l in XS by discriminate.
    rewrite <- Nat2N.inj_add, <- Nat.add_assoc in XS. simpl (3+4)%nat in XS.

    assert (LEPT: (forall n m p, n <= m -> n <= m + p)%nat). intros. eapply Nat.le_trans. apply H. apply Nat.le_add_r.
    rewrite N.mod_small in XS by
    ( eapply N.le_lt_trans; [apply Nat2N_le | exact SIZ];
      apply Nat.add_le_mono_l;
      rewrite <- (firstn_skipn i l') at 2; rewrite concat_app, app_length, <- Nat.add_assoc; apply Nat.add_le_mono_l;
      rewrite nth_skipn in BLK; destruct skipn; [discriminate|]; apply invSome in BLK; rewrite BLK;
      rewrite concat_cons, !app_length, <- !Nat.add_assoc;
      apply Nat.add_le_mono_l, LEPT; repeat apply le_n_S; apply Nat.le_0_l ).

    fold m4 in XS. inversion XS; clear XS; subst. destruct c.

      (* fallthrough (perform lookup before guarded branch) *)
      inversion E; clear E; subst.
        inversion E1; clear E1. rewrite update_updated in H2. inversion H2; clear H2. subst.
        inversion E2; clear E2. rewrite H in H1, H3. subst.
      destruct (n1 .& 127) eqn:N1; [clear H|discriminate H].
      inversion XS0; clear XS0; subst.
      apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.

      (* Srli tmp1, tmp1, 5 *)
      destruct (step_after_tag 5 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
      [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
      rewrite ASM5 in XS. unfold rv2il, r5mov, r5var in XS. fold v1 in XS.
      inversion XS; clear XS; subst. inversion E; clear E; subst.
        inversion E1; clear E1. rewrite update_frame, update_updated in H by exact V12. inversion H; clear H. subst v n0 w.
        inversion E2; clear E2; subst. unfold eval_binop in XP, TR.
      apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.

      (* Add tmp3, tmp3, tmp1 *)
      destruct (step_after_tag 6 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
      [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
      rewrite ASM6 in XS. unfold rv2il, r5mov, r5var in XS. fold v3 v1 in XS. set (n1sr5 := n1 >> 5) in XS.
      inversion XS; clear XS; subst. inversion E; clear E; subst.
        inversion E1; clear E1. rewrite !update_frame, update_updated in H by assumption. inversion H; clear H. subst v n0 w.
        inversion E2; clear E2. rewrite update_updated in H. inversion H; clear H. subst v n2. unfold eval_binop, towidth in TR, XP.
      apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.

      (* Lw tmp1, tmp3, 0 *)
      destruct (step_after_tag 7 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
      [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
      rewrite ASM7 in XS. unfold rv2il, r5mov, r5var in XS. fold v1 v3 in XS.
      inversion XS; clear XS; subst. inversion E; clear E R; subst.
        inversion E1; clear E1. rewrite !update_frame, MEM1 in H by apply rv_varid_nonmem. inversion H; clear H; subst.
        inversion E2; clear E2; subst.
          inversion E1; clear E1. rewrite update_updated in H. inversion H; clear H. subst v n0 n1sr5.
          inversion E0; clear E0; subst. rewrite N.add_0_r in XP, TR.
      apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.

      eexists _, _, _, _. repeat split.
        exact XP.
        rewrite (Nat.add_comm _ 9). exact TR.
        repeat apply Forall_tail in INB. exact INB.
        rewrite !update_frame by apply rv_varid_nonmem. exact MEM1.
        rewrite update_frame, update_updated by exact V31. reflexivity.
        apply N.mod_lt. discriminate 1.

        clear - A1LO N1.
        change (2^32)%N with (4*(2^30))%N. rewrite N.mod_mul_r, N.mul_comm, N.mod_add, N.mod_mod, N.add_mod by discriminate 1.
        change 4%N with (2^2)%N. rewrite <- !N.land_ones, <- N.land_assoc, N.land_0_r, N.add_0_l, !N.land_ones, N.mod_mod by discriminate.
        unfold ashiftr, sbop1. rewrite <- ofZ_toZ, toZ_ofZ_canonicalZ, ofZ_canonicalZ by discriminate.
        erewrite <- ofZ_mod_pow2 by reflexivity. rewrite <- Z.land_ones by discriminate. change (Z.ones _) with ((toZ 32 127 #& 96) #>> 5). rewrite <- Z.shiftr_land.
        rewrite Z.land_assoc. rewrite <- toZ_land. rewrite N1. reflexivity.

        rewrite update_updated, N.mod_mod by discriminate 1. reflexivity.

      (* branch taken (no lookup before guarded branch) *)
      clear p E. inversion XS0; clear XS0; subst.
      inversion E; clear E; subst. apply invExit in EX. subst m4. apply N.mul_cancel_l in EX; [|discriminate]. subst a.
      eexists _, _, _, _. repeat split.
        rewrite <- !Nat.add_assoc in XP. exact XP.
        rewrite <- (Nat.add_1_r (length b)), !plus_n_Sm, <- !Nat.add_assoc in TR. exact TR.
        repeat apply Forall_tail in INB. exact INB.
        rewrite !update_frame by apply rv_varid_nonmem. apply MEM1.
        rewrite 2!update_frame, update_updated by assumption. reflexivity.
        exact A1LO.
        change 4%N with (2^2)%N. rewrite <- N.land_ones, <- N.land_assoc. apply N.land_0_r.
        rewrite update_frame, update_updated by exact V12. reflexivity.

  clear t s1 XP TR INB. destruct H as [m2 [a' [s1 [n1 [t [XP [TR [INB [MEM1 [S1V3 [A'LO [A'4 S1V1]]]]]]]]]]]].

  (* Lui tmp2, out_id *)
  destruct (step_after_tag 8 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
  [ rewrite !Nat.add_succ_r; discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
  rewrite ASM8 in XS. unfold rv2il, r5mov in XS. fold v2 in XS. set (pow20 := 2^20) in XS.
  inversion XS; clear XS; subst. apply invExit in EX. apply N.mul_cancel_l in EX; [|discriminate]. subst a.
  inversion E; clear E; subst.
  inversion E2; clear E2; subst. unfold eval_binop, towidth in XP, TR.
  inversion E1; clear E1; subst.
  subst pow20. rewrite N.mod_small in XP, TR by ( change 32%N with (20+12)%N; apply shiftl_bound;
    change (2^20)%N with (Z.to_N (2^20)); apply Z2N_lt; [|apply Z.mod_pos_bound]; reflexivity).

  (* Ori tmp2, tmp2, 55 *)
  destruct (step_after_tag 9 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
  [ rewrite Nat.add_sub; destruct b; [ destruct sb |]; discriminate | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
  rewrite ASM9 in XS. unfold rv2il, r5mov, r5var in XS. fold v2 in XS. set (pow20 := 2^20) in XS.
  inversion XS; clear XS; subst. rewrite update_cancel in XP, TR. apply invExit, N.mul_cancel_l in EX; [|discriminate]. subst a.
  inversion E; clear E; subst.
  inversion E2; clear E2; subst. unfold eval_binop, towidth in XP, TR.
  inversion E1; clear E1; subst. rewrite update_updated in H. inversion H; clear H; subst.

  assert (H: exists n3 s3 t3,
      exec_prog h rv_prog (4 * N.of_nat (bi+j0)) s0 n3 s3 (Exit (4 * N.of_nat (bi + (ilen + (taglen + (length b + 9)))))) /\
      rv_trace h (N.of_nat (bi + (ilen + (taglen + (length b + 9))))) s3 t3 (N.of_nat (bi + (ilen + (taglen + (length b + 9))))) s /\
      Forall (inblock bi l' i) t3 /\ m2 Ⓓ[a'] = (Z.to_N (oid mod pow20) << 12) .| 55 /\
      s3 V_MEM32 = Ⓜm2 /\ s3 v3 = Ⓓa' /\ s3 v1 = Ⓓm2 Ⓓ[a'] /\ s3 v2 = Ⓓ ((Z.to_N (oid mod pow20) << 12) .| 55) /\
      rv_decode (Z.to_N ie) = R5_Jalr (xbits (Z.to_N z) 7 12) (N.pos tmp3) 0).

    destruct sb;
    repeat (destruct b; [discriminate|]); rewrite !map_cons in NIJ;
    repeat (apply invCons in NIJ; let H := fresh "ASM0" in destruct NIJ as [H NIJ]);
    (destruct b; [clear NIJ|discriminate]).

      (* Bne tmp1, tmp2, abort *)
      destruct (step_after_tag 10 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
      [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
      rewrite ASM10 in XS. unfold rv2il, r5branch, r5var in XS. fold v1 v2 in XS.
      rewrite N2Z.inj_mul, <- Z.mul_add_distr_l, Z2N_inj_mul, nat_N_Z in XS by (left; discriminate 1).
      rewrite 2!Nat2Z.inj_add, <- (sumsizes_newinstrs _ NC) in XS.
      assert (IL: (i < length l)%nat). rewrite <- (newinstrs_length NC). apply Nat.le_succ_l, nth_error_Some. rewrite BLK. discriminate 1.
      rewrite Z.add_1_l, <- Nat2Z.inj_succ, skipn_length, <- Nat.sub_succ_l, Nat.sub_succ in XS by exact IL.
      rewrite newoffset_index in XS.
      rewrite rev_length, firstn_length_le, <- Nat2Z.inj_add, le_pmr, Nat2Z.id in XS by apply Nat.lt_le_incl, IL.
      rewrite rev_involutive, firstn_cons_skipn, firstn_all in XS by exact DAT.
      rewrite sumsizes_cons, sumsizes_rev, (newsize_length _ _ _ _ _ _ NC DAT BLK), app_length, !Nat2Z.inj_add in XS.
      rewrite <- Z.add_sub_assoc, (Z.add_comm _ 12), !Z.sub_add_distr, (Z.sub_opp_l 10), <- !Z.add_opp_r, (Z.add_comm (-_+_)), <- !Z.opp_add_distr in XS.
      rewrite <- (Z.add_assoc (Z.of_nat bi)), Z.add_opp_r, Zplus_minus in XS.
      rewrite (sumsizes_newinstrs_all NC), <- Nat2Z.inj_add, Nat2Z2N in XS.
      change (2^32)%N with (4*2^30)%N in XS. rewrite N.mul_mod_distr_l in XS by discriminate 1. rewrite N.mod_small in XS by exact SIZ.
      fold m4 in XS. inversion XS; clear XS; subst.
      inversion E; clear E; subst.
      inversion E1; clear E1; subst. rewrite update_frame, S1V1 in H by exact V12. apply invVaN in H; destruct H; subst.
      inversion E2; clear E2; subst. rewrite update_updated in H. apply invVaN, proj1 in H; subst.
      destruct (_ =? _)%N eqn:CMP in XS0; simpl N.b2n in XS0; cbv match in XS0.

        (* fallthru *)
        inversion XS0; clear XS0; subst. apply invExit, N.mul_cancel_l in EX; [|discriminate]. subst a.
        eexists _, _, _. repeat split.
          exact XP.
          exact TR.
          repeat apply Forall_tail in INB. exact INB.
          apply N.eqb_eq, CMP.
          rewrite update_frame by apply rv_varid_nonmem. exact MEM1.
          rewrite update_frame by exact V32. exact S1V3.
          rewrite update_frame by exact V12. exact S1V1.
          apply update_updated.
          apply invSome in IE. subst ie. exact ASM11.

        (* branch taken: abort *)
        inversion XS0; clear XS0; subst. apply invExit in EX. subst a0.
        fold m4 in E. inversion E; clear E; subst. subst m4. apply N.mul_cancel_l in H; [|discriminate]. subst a.
        do 2 apply Forall_tail in INB. apply Forall_inv, proj2 in INB. contradict INB. apply N.le_ngt, Nat2N_le.
        rewrite <- (firstn_skipn (S i) l') at 2. rewrite concat_app, app_length. apply Nat.add_le_mono_l, Nat.le_add_r.

      (* R5_Beq tmp1, tmp2, +8 *)
      destruct (step_after_tag 10 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
      [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
      rewrite ASM10 in XS. unfold rv2il, r5branch, r5var in XS. fold v1 v2 in XS.
      rewrite Z2N.inj_add, N2Z.id, <- (N.mul_add_distr_l 4 _ 2), <- (Nat2N.inj_add _ 2), <- !Nat.add_assoc, (Nat.add_assoc _ taglen), N.mod_small in XS;
        cycle 1; try solve [ Z_nonneg ].
        change (2^32)%N with (4*2^30)%N. apply N.mul_lt_mono_pos_l; [reflexivity|]. eapply N.le_lt_trans; [|exact SIZ].
        rewrite <- (firstn_cons_skipn _ _ l' i BLK) at 2.
        rewrite concat_app, app_length, <- Nat.add_assoc; apply Nat2N_le, Nat.add_le_mono_l, Nat.add_le_mono_l.
        rewrite concat_cons, !app_length, <- !Nat.add_assoc.
        apply Nat.add_le_mono_l. etransitivity; [|apply Nat.le_add_r]. apply le_S, le_n.
      fold m4 in XS. inversion XS; clear XS; subst.
      inversion E; clear E; subst.
        inversion E1; clear E1; subst. rewrite update_frame, S1V1 in H by exact V12. apply invVaN in H; destruct H; subst.
        inversion E2; clear E2; subst. rewrite update_updated in H. apply invVaN, proj1 in H; subst.
      destruct (_ =? _)%N eqn:CMP in XS0; simpl N.b2n in XS0; cbv match beta in XS0.

        (* branch taken: policy check passed *)
        inversion XS0; clear XS0; subst. inversion E; clear E; subst.
        unfold m4 in EX. apply invExit, N.mul_cancel_l in EX; [|discriminate]. rewrite <- Nat.add_assoc in EX. subst a.
        eexists _, _, _. repeat split.
          exact XP.
          exact TR.
          repeat apply Forall_tail in INB. exact INB.
          apply N.eqb_eq, CMP.
          rewrite update_frame by apply rv_varid_nonmem. exact MEM1.
          rewrite update_frame by exact V32. exact S1V3.
          rewrite update_frame by exact V12. exact S1V1.
          apply update_updated.
          apply invSome in IE. subst ie. exact ASM12.

        (* R5_Jal r0, abort *)
        inversion XS0; clear XS0; subst.
        apply invExit, N.mul_cancel_l in EX; [|discriminate]. subst a.
        destruct (step_after_tag 11 CODE XP TR BLK (eq_refl _)) as [s2 [x [a [t' [XS [EX [TL [XP' TR']]]]]]]];
        [ discriminate 1 | clear XP TR; subst t; rename XP' into XP; rename TR' into TR; rename t' into t; fold taglen in XS, EX, TR ].
        rewrite ASM11 in XS. unfold rv2il, r5mov in XS.
        rewrite Z.add_1_l, <- Nat2Z.inj_succ, N2Z.inj_mul, <- Z.mul_add_distr_l, nat_N_Z, newoffset_index, <- Nat2Z.inj_add, Nat2Z.id in XS.
        erewrite rev_involutive, rev_length, <- length_cons, <- app_length, firstn_all, firstn_cons_skipn in XS by exact DAT.
        erewrite sumsizes_cons, sumsizes_rev, sumsizes_newinstrs in XS by exact NC. erewrite newsize_length in XS by eassumption.
        rewrite app_length, (Nat.add_comm _ 13), (Nat2Z.inj_add 13), <- Z.add_sub_assoc, <- Z.add_assoc, Z.sub_add_distr in XS.
        rewrite Z.add_sub_assoc, (Z.add_opp_r _ 11), <- Z.sub_add_distr, <- Nat2Z.inj_add in XS.
        rewrite (Nat2Z.inj_add bi), <- Z.add_assoc in XS.
        rewrite <- (Nat2Z.inj_add 11), (Nat.add_assoc 11), (Nat.add_comm 11 _), (Nat.add_comm (_+11)), Zplus_minus in XS.
        rewrite Z2N_inj_mul, simpl_jal_dest in XS by (left; discriminate 1).
        rewrite (sumsizes_newinstrs_all NC), <- Nat2Z.inj_add, Nat2Z2N, N.mod_small in XS by exact SIZ.
        inversion XS; [ solve [ inversion XS0 ] | clear XS; subst ].
          inversion XS1; clear XS1; subst.
          inversion XS0; clear XS0; subst. inversion E; clear E; subst.
        rewrite (N.mul_comm _ 4) in EX. apply invExit, N.mul_cancel_l in EX; [|discriminate 1]. subst a.
        do 3 apply Forall_tail in INB. apply Forall_inv, proj2 in INB. contradict INB. apply N.le_ngt.
        rewrite <- (firstn_skipn (S i) l') at 2. rewrite concat_app, app_length. apply Nat2N_le, Nat.add_le_mono_l, Nat.le_add_r.

  clear s1 MEM1 S1V3 S1V1 XP TR INB. destruct H as [n' [s3 [t3 [XP [TR [INB [CMP [MEM2 [S3V3 [S3V1 [S3V2 ASM]]]]]]]]]]].

  (* Jalr rs, tmp3, 0 *)
  inversion TR; clear TR; subst.

    (* end of trace *)
    rewrite ASM in XS'. unfold rv2il, r5var in XS'. fold v3 in XS'.
    inversion XS'; [ solve [ inversion XS ] |]; clear XS'; subst.
    inversion XS1; clear XS1; subst. inversion E; clear E; subst.
      inversion E1; clear E1; subst.
        inversion E0; clear E0; subst. rewrite S3V3 in H. inversion H; clear H; subst n3 w.
        inversion E3; clear E3; subst. rewrite N.add_0_r in XS0.
      inversion E2; clear E2; subst. unfold eval_binop in XS0.
    inversion XS0; clear XS0; subst; [ apply r5mov_fallthru in XS; discriminate XS |].
    assert (TMP:=XS1). apply r5mov_notmp in TMP. rewrite update_updated in TMP.
    apply r5mov_nomem in XS1. rewrite !update_frame in XS1 by (discriminate 1 + apply rv_varid_nonmem). rename XS1 into MEM'.
    inversion XS2; clear XS2; subst e s2 x'. inversion E; clear E; subst. rewrite TMP in H. inversion H; clear H; subst.
    apply invExit in EX'. change 4294967294%N with ((N.ones 30 << 2) .| 2) in EX'.
    rewrite N.mod_small in EX', TMP by exact A'LO.
    rewrite (N.div_mod' a' 4), A'4, N.add_0_r, N.mul_comm, <- (N.shiftl_mul_pow2 _ 2), N.land_lor_distr_r, (N_shiftl_land_0 _ _ 2), N.lor_0_r in EX' by reflexivity.
    rewrite <- N.shiftl_land, N.shiftl_mul_pow2, N.mul_comm, N.land_ones, N.mod_small in EX' by (apply N.div_lt_upper_bound; [ discriminate 1 | exact A'LO ]).
    apply N.mul_cancel_l, (f_equal N.to_nat) in EX'; [|discriminate 1]. rewrite Nat2N.id in EX'. subst j'.

    specialize (CODE _ _ _ _ _ (N.to_nat (a'/4) - bi)%nat XP MEM2). rewrite le_pmr in CODE by exact HI.
    assert (H: (N.to_nat (a'/4) - bi < length (concat l'))%nat).
      apply indexmap_inlist. rewrite (newinstrs_length NC). apply nth_error_Some. rewrite DAT'. discriminate 1.
    apply nth_error_Some in H. destruct (nth_error (concat l') (N.to_nat (a'/4) - bi)%nat) as [ie'|] eqn:IE'; [clear H|contradiction].
    rewrite N2Nat.id, <- (N.add_0_r (4*_)), <- A'4, <- N.div_mod' in CODE. rewrite CODE in CMP.
    assert (IE'NN: 0 <= ie').
      eapply Forall_forall; [|eapply nth_error_In, IE'].
      eapply Forall_concat, newinstrs_nonneg, NC.
    change 12%N with (Z.to_N 12) in CMP. change 55%N with (Z.to_N 55) in CMP.
    rewrite <- Z2N_inj_shiftl, <- Z2N_inj_lor in CMP by Z_nonneg.
    apply Z2N.inj in CMP; [|Z_nonneg..]. subst ie'.
    eapply tags_at_blockboundaries in IE'; [| exact NC |
      rewrite Z.land_lor_distr_l, (shiftl_landones_0 12) by discriminate 1; reflexivity ].
    destruct IE' as [i' [[iid' oid' sd' ie' sb'] [H1 [H2 H3]]]].
    erewrite H1, (indexmap_inv _ NC), H2 in DAT' by (rewrite (newinstrs_length NC); apply Nat.lt_le_incl, nth_error_Some; rewrite H2; discriminate 1).
    apply invSome in DAT'. subst d'. destruct iid'; [split|exact H3].
      eexists. exact H1.
      rewrite Z.shiftr_lor, Z.lor_0_r, Z.shiftr_shiftl_l, Z.shiftl_0_r in H3 by discriminate 1. exact H3.

    (* final indirect jump is within the trace (impossible) *)
    unfold rv_prog in LU. rewrite MEM2 in LU. destruct (s3 A_EXEC) as [|e w]; [discriminate LU|]. destruct (e _) as [|p]; [discriminate LU|]. clear e w p.
    fold m4 in LU. inversion LU; clear LU; subst.
    assert (CODE2 := CODE _ _ _ _ _ (ilen + (taglen + (length b + 9)))%nat XP MEM2). erewrite (nth_error_concat _ _ _ _ _ BLK) in CODE2 by
    ( rewrite nth_error_app2, Nat.add_comm, Nat.add_sub, Nat.add_comm by apply Nat.le_add_r; exact IE ).
    unfold rv_stmt, m4 in XS. rewrite N.mul_comm, N.mod_mul, N.mul_comm, CODE2, ASM in XS by discriminate 1. clear CODE2.
    unfold rv2il, r5var in XS. fold m4 v3 in XS.
    inversion XS; [ solve [ inversion XS0 ] |]; clear XS; subst.
    inversion XS1; clear XS1; subst. inversion E; clear E; subst.
      inversion E1; clear E1; subst.
        inversion E0; clear E0; subst. rewrite S3V3 in H. inversion H; clear H; subst n3 w.
        inversion E3; clear E3; subst. rewrite N.add_0_r in XS0.
      inversion E2; clear E2; subst. unfold eval_binop in XS0.
    inversion XS0; clear XS0; subst; [ apply r5mov_fallthru in XS; discriminate XS |].
    assert (TMP2:=XS1). apply r5mov_notmp in TMP2. rewrite update_updated in TMP2.
    apply r5mov_nomem in XS1. rewrite update_frame, MEM2 in XS1 by (discriminate 1 + apply rv_varid_nonmem). rename XS1 into MEM3.
    inversion XS2; clear XS2; subst e s2 x. inversion E; clear E; subst. rewrite TMP2 in H. inversion H; clear H; subst.
    apply invExit in EX. change 4294967294%N with ((N.ones 30 << 2) .| 2) in EX.
    rewrite N.mod_small in EX by exact A'LO.
    rewrite (N.div_mod' a' 4), A'4, N.add_0_r, N.mul_comm, <- (N.shiftl_mul_pow2 _ 2), N.land_lor_distr_r, (N_shiftl_land_0 _ _ 2), N.lor_0_r in EX by reflexivity.
    rewrite <- N.shiftl_land, N.shiftl_mul_pow2, N.mul_comm, N.land_ones, N.mod_small in EX by (apply N.div_lt_upper_bound; [ discriminate 1 | exact A'LO ]).
    apply N.mul_cancel_l in EX; [|discriminate 1]. subst a1.

    apply Forall_inv in INB.
    assert (HI': (bi <= N.to_nat (a'/4))%nat).
      apply Nat2N_le. rewrite N2Nat.id. etransitivity. apply N.le_add_r. rewrite <- Nat2N.inj_add. apply N.lt_le_incl, INB.
    specialize (CODE _ _ _ _ _ (N.to_nat (a'/4) - bi)%nat XP MEM2). rewrite le_pmr in CODE by exact HI'.
    assert (H: (N.to_nat (a'/4) - bi < length (concat l'))%nat).
      eapply Nat.add_lt_mono_l. rewrite le_pmr by exact HI'. eapply Nat.lt_le_trans.
        apply Nat2N_lt. rewrite N2Nat.id. apply INB.
        rewrite <- (firstn_skipn (S i) l') at 2. rewrite concat_app, app_length. apply Nat.add_le_mono_l, Nat.le_add_r.
    apply nth_error_Some in H. destruct (nth_error (concat l') (N.to_nat (a'/4) - bi)%nat) as [ie'|] eqn:IE'; [clear H|contradiction].
    rewrite N2Nat.id, <- (N.add_0_r (4*_)), <- A'4, <- N.div_mod' in CODE. rewrite CODE in CMP.
    assert (IE'NN: 0 <= ie').
      eapply Forall_forall; [|eapply nth_error_In, IE'].
      eapply Forall_concat, newinstrs_nonneg, NC.
    change 12%N with (Z.to_N 12) in CMP. change 55%N with (Z.to_N 55) in CMP.
    rewrite <- Z2N_inj_shiftl, <- Z2N_inj_lor in CMP by Z_nonneg.
    apply Z2N.inj in CMP; [|Z_nonneg..]. subst ie'.
    eapply tags_at_blockboundaries in IE'; [| exact NC |
      rewrite Z.land_lor_distr_l, (shiftl_landones_0 12) by discriminate 1; reflexivity ].
    destruct IE' as [i' [d'' [BB' H]]]. clear d'' H.
    destruct INB as [INB1 INB2]. simpl fst in INB1, INB2.
    destruct (Nat.le_gt_cases i' i) as [H|H].

      contradict INB1. apply N.le_ngt, N2Nat_le. rewrite Nat2N.id. apply Nat.le_sub_le_add_l. rewrite BB'.
      rewrite <- (firstn_skipn i' l') at 2. rewrite firstn_app, firstn_firstn, min_r, concat_app, app_length by exact H.
      apply Nat.le_add_r.

      contradict INB2. apply N.le_ngt, N2Nat_le. rewrite Nat2N.id, <- (Nat.sub_add _ _ HI'), Nat.add_comm. apply Nat.add_le_mono_r. rewrite BB'.
      rewrite <- (firstn_skipn (S i) l') at 2. rewrite firstn_app, firstn_firstn, min_r, concat_app, app_length by exact H.
      apply Nat.le_add_r.
Qed.



(* Here's the main theorem to prove: *)
Theorem rewriter_safety: forall pol, safety pol (newcode pol) (indexmap pol).
Proof.
  (* Set up a strong induction with a suitable induction hypothesis. *)
  unfold safety. intros. unfold indexmap. rewrite NC.
  revert s j q s' x j' XP0 LU XS EX. pattern n. apply strong_induction. intros.
  clear n. rename n1 into n.
  assert (IHe: execution_IH l' h bi' j0 s0 n). intros n0 LT s1 j1 q1 s1' x1 j1' XP1 LU1 XS1 EX1. split.
    apply Nat.nlt_ge. intro H1. contradict LU1.
      unfold rv_prog. destruct (s1 V_MEM32); [discriminate|]. destruct (s1 A_EXEC) eqn:H2; [discriminate|].
      rewrite (NXD _ _ _ _ _ j1 XP1 H2). discriminate 1. left. exact H1.
    destruct (IH n0 LT s1 j1 q1 s1' x1 j1' XP1 LU1 XS1 EX1) as [H1|[H2|[H3|H4]]].
      left. exact H1.
      right. left. eapply proj1, H2.
      right. right. left. exact H3.
      do 3 right. exact H4.
  clear IH. move IHe at top. fold (nonexecutable_data l' h bi j0 s0) in NXD.

  (* Infer that current code equals statically rewritten code. *)
  assert (CODE: codebytes l' h bi' j0 s0).
    intros n0 s1 x1 m w i XP1 MEM1. destruct nth_error eqn:NTH; [|exact I]. etransitivity.
      eapply NWC; try eassumption. apply nth_error_Some. rewrite NTH. discriminate.
      apply CS. exact NTH.
  clear CS NWC. move CODE before NC.
  unfold rv_prog in LU. assert (CODE1 := CODE s n). assert (NXD1 := NXD n s).
  destruct (s V_MEM32) as [|m mw]. discriminate. specialize (CODE1 _ m mw (j-bi')%nat XP0 (eq_refl _)).
  destruct (s A_EXEC) as [|e ew]. discriminate. specialize (NXD1 _ e ew j XP0 (eq_refl _)).
  destruct (e (4 * N.of_nat j)%N). discriminate.
  replace q with (rv_stmt m (4 * N.of_nat j)%N) in XS by (inversion LU; reflexivity). clear q LU.
  assert (JHI: (bi' <= j)%nat). apply Nat.le_ngt. intro H. discriminate NXD1. left. exact H.
  eassert (JLO: (j - bi' < _)%nat).
    eapply Nat.add_lt_mono_l. rewrite (le_pmr _ _ JHI). apply Nat.lt_nge. intro H. discriminate NXD1. right. exact H.
  unfold rv_stmt in XS. destruct (_ mod 4)%N; [| inversion XS; subst; discriminate ].
  destruct nth_error as [ie'|] eqn:IE'; [| apply nth_error_Some in JLO; rewrite IE' in JLO; contradiction ].
  rewrite (le_pmr _ _ JHI) in CODE1. rewrite CODE1 in XS. clear m mw e ew p CODE1 NXD1.

  (* Derive the metadata (before and after shrink-optimization) used in rewriting. *)
  apply find_block in JLO. unfold policytarget. set (i:=indexmap' l' (j-bi')) in *.
  destruct JLO as [b0 [BLK BND]].
  unfold newcode in NC. apply invPair, proj2 in NC.
  destruct (sumsizes _ <? _) eqn:SIZ; [|discriminate]. apply Z.ltb_lt, Z.lt_add_lt_sub_l in SIZ.
  assert (NIS:=nth_newinstrs _ _ _ _ i NC). rewrite BLK in NIS.
  destruct (nth_error (shrink _ _) _) as [d'|] eqn:DAT'; [|discriminate].
  destruct (newinstr _ _ d' _) as [b|] eqn:NI; [|discriminate]. rewrite app_nil_r in NI.
  apply invSome in NIS. subst b0.
  destruct (nth_error (map todata (combine pol l)) i) as [d|] eqn:DAT;
  [| contradict DAT; apply nth_error_Some;
     rewrite <- (Nat.add_0_l (length _)); change O with (length (@nil instr_data));
     rewrite <- shrink_length; apply nth_error_Some; rewrite DAT'; discriminate ].
  assert (DEQ: dateq (d,d')). eapply (Forall_forall dateq).
    eapply (shrink_preserves _ nil). reflexivity. apply Forall_nil.
    eapply combine_nth_error.
      simpl. exact DAT.
      exact DAT'.
  destruct d as [iid oid sd ie sb1]. destruct d' as [iid' oid' sd' z' sb].
  inversion DEQ. subst iid' oid' sd' z'. clear DEQ.
  rewrite nth_error_map, nth_error_combine in DAT.
  destruct (nth_error pol i) as [(iid0,(oid0,sd0))|]; [|discriminate].
  destruct (nth_error l i); [|discriminate].
  inversion DAT; subst. clear DAT.

  (* Locate the rewritten instruction being executed within its containing block. *)
  rewrite <- (firstn_skipn i l'), concat_app, nth_error_app2 in IE' by apply BND.
  assert (BLK':=BLK). rewrite nth_skipn in BLK'.

  (* If the rewritten code is the tag within a block, it's safe because it falls thru to the same block. *)
  destruct (skipn i l') as [|bb t] eqn:BLK0. discriminate.
  apply invSome in BLK'. subst bb.
  rewrite concat_cons, nth_error_app1 in IE' by (eapply Nat.add_lt_mono_l; rewrite Nat.add_comm, Nat.sub_add; apply BND).
  destruct (Nat.lt_ge_cases (j-bi') (length (concat (firstn i l')) + length (newtag (Data iid oid sd ie sb)))) as [TAG|TAG].
  rewrite nth_error_app1 in IE' by (eapply Nat.add_lt_mono_l; rewrite Nat.add_comm, Nat.sub_add by apply BND; exact TAG).
  eapply newtag_exit, proj2 in XS; [| exact IE' ]. subst x. apply invExit in EX. apply N.mul_cancel_l, Nat2N.inj in EX; [| discriminate ]. subst j'.
  left. eapply indexmap_same.
    exact BLK.
    apply BND.
    apply Nat.sub_le_mono_r, Nat.le_succ_r.
    left. reflexivity.
    rewrite app_length, Nat.add_assoc, (Nat.sub_succ_l _ _ JHI), <- Nat.add_1_r. apply Nat.add_lt_le_mono.
      exact TAG.
      destruct b. contradict NI. apply newinstr_nonnil. apply le_n_S, Nat.le_0_l.

  (* Otherwise the current instruction is in the non-tag portion of the block. *)
  rewrite nth_error_app2 in IE' by apply Nat.le_add_le_sub_l, TAG.
  assert (NS := newsize_newinstr NI).
  unfold newinstr in NI. unfold_consts in NI. destruct (ie <? 0) eqn:IE0. discriminate. apply Z.ltb_ge in IE0.

  (* If the original code was a tag, the rewritten code falls thru to next block. *)
  destruct (ie #& 4095 =? 55) eqn:OP55.
  right. left. clear SIZ S0 CODE BB IHe XP0 DAT' OP55.
  destruct (mem 1 sd) eqn:IN1; [|discriminate].
  apply invSome in NI. subst b.
  rewrite app_length, Nat.add_assoc in BND.
  assert (IDX := Nat_squeeze (j-bi') _ TAG (proj2 BND)). clear TAG.
  rewrite IDX in IE' at 1. rewrite <- Nat.sub_add_distr, Nat.sub_diag in IE'.
  apply invSome in IE'. subst ie'.
  inversion XS; clear XS; subst s' x.
  apply invExit, N.mul_cancel_l, Nat2N.inj in EX; [|discriminate].
  rewrite <- Nat.add_1_r in EX. subst j'. rewrite (Nat.add_sub_swap _ 1 _ JHI).
  split.

    change 1%nat with (length (16435::nil)).
    exists (i + 1)%nat.
    rewrite <- (firstn_skipn i l'), IDX, <- Nat.add_assoc, <- 2!app_length.
    rewrite firstn_app, firstn_firstn, Nat.min_r by apply Nat.le_add_r.
    rewrite firstn_length, Nat.min_l, Nat.add_comm, Nat.add_sub by
      (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
    rewrite nth_skipn in BLK. destruct (skipn i l'). discriminate. apply invSome in BLK. subst l0.
    rewrite concat_app. simpl. rewrite app_nil_r. reflexivity.

    left. replace (indexmap' _ _) with (indexmap' l' (j-bi') + 1)%nat.
      rewrite Nat2Z.inj_add, Z.add_simpl_l. apply mem_In, IN1.
    symmetry. rewrite IDX. rewrite <- Nat.add_assoc.
    change 1%nat with (length (16435::nil)) at 1. rewrite <- 2!app_length.
    replace (_++_::nil) with (concat (match nth_error l' i with None => nil | Some x => x::nil end))
      by (rewrite BLK; apply app_nil_r).
    rewrite <- concat_app, <- firstn_last.
    erewrite indexmap_next.
      apply Nat.add_cancel_r. eapply indexmap_same.
        exact BLK.
        reflexivity.
        apply Nat.le_add_r.
        rewrite app_length, Nat.add_assoc, Nat.add_1_r. apply Nat.lt_succ_diag_r.
      exact BLK.
      intro H. apply app_eq_nil, proj2 in H. discriminate.
      eapply newinstrs_nonnil. exact NC.

  (* If the original code was a position-independent code address computation,
     the rewritten code falls thru to the next block. *)
  destruct (ie #& 127 =? 23) eqn:OP23.
  eapply newauipc_exit in XS; try eassumption. subst x.
  apply invExit, N.mul_cancel_l, Nat2N.inj in EX; [|discriminate 1]. subst j'.
  unfold new_auipc in NI. destruct (mem Z1 sd) eqn:IN1; [clear NI|rewrite Bool.andb_false_r in NI; discriminate NI].
  rewrite (Nat.sub_succ_l _ _ JHI) in *.
  assert (HI:=proj2 BND). apply Nat.le_succ_l, Nat.le_lteq in HI. destruct HI as [HI|HI].
    left. eapply indexmap_same.
      eassumption.
      apply BND.
      apply Nat.lt_le_incl, Nat.lt_succ_diag_r.
      apply HI.
    right. left. split.
      exists (S i). rewrite firstn_last, BLK, <- concat_last, app_length. apply HI.
      left. rewrite HI, <- app_length, concat_last. replace (_++_) with (firstn (S i) l').
        erewrite indexmap_inv.
          rewrite Nat2Z.inj_succ, Z.sub_succ_l, Z.sub_diag. apply mem_In, IN1.
          exact NC.
          apply Nat.le_succ_l, nth_error_Some. rewrite BLK. discriminate 1.
        rewrite firstn_last, BLK. reflexivity.

  (* If the original code was a branch... *)
  destruct (ie #& 127 =? 99) eqn:OP99. clear OP55. apply Z.eqb_eq in OP99.
  destruct andb eqn:H; [|discriminate].
  apply andb_prop in H. destruct H as [H I'LE]. apply Z.leb_le in I'LE.
  apply andb_prop in H. destruct H as [H I'GE]. apply Z.leb_le in I'GE.
  apply andb_prop in H. destruct H as [H IN'].
  apply andb_prop in H. destruct H as [OP256 IN1]. apply Z.eqb_eq in OP256.
  rewrite Nat2N.inj_succ in EX. rewrite <- Nat.sub_add_distr in IE'.
  eapply newbranch_exit in XS; try eassumption.

    destruct XS as [[k [FT1 FT2]]|JMP].

      (* If the branch falls through, the fall-through destination satisfies the policy. *)
      rewrite <- (N2Nat.id k), <- Nat2N.inj_add in FT1.
      apply N.mul_cancel_l, Nat2N.inj in FT1; [|discriminate]. subst j'.
      rewrite Nat_sub_sub_distr in FT2 by (assumption +
        (apply Nat.le_sub_le_add_l, Nat.lt_le_incl; rewrite <- Nat.add_assoc, <- app_length; apply BND)).
      rewrite Nat.add_comm, <- Nat.add_assoc, <- app_length in FT2.
      apply Nat.le_lteq in FT2. destruct FT2 as [SAME|NXT].

        left. eapply indexmap_same. exact BLK. apply BND. apply Nat.sub_le_mono_r, Nat.le_add_r.
        rewrite Nat.add_comm, <- (Nat.add_sub_assoc _ _ _ JHI). apply Nat.lt_add_lt_sub_r, SAME.

        apply (Nat.add_cancel_l _ _ (j-bi')) in NXT. rewrite (Nat.add_comm _ (_-_)%nat), Nat.sub_add in NXT by apply Nat.lt_le_incl, BND.
        rewrite (Nat.add_sub_swap _ _ _ JHI), NXT, <- app_length, concat_last, firstn_app_nth by exact BLK.
        right. left. split; [|left].

          eexists. reflexivity.

          rewrite (indexmap_inv _ NC) by (apply Nat.le_succ_l, nth_error_Some; rewrite BLK; discriminate).
          rewrite Nat2Z.inj_succ, Z.sub_succ_l, Z.sub_diag. apply mem_In, IN1.

      (* If the branch jumps, the target satisfies the policy. *)
      apply N.mul_cancel_l in JMP; [|discriminate].
      rewrite nat_N_Z, <- Nat2Z.inj_add, Nat.add_sub_assoc in JMP by
      (apply Nat.le_sub_le_add_l; rewrite <- Nat.add_assoc, <- app_length; apply Nat.lt_le_incl, BND).
      rewrite Nat.add_comm, <- Nat.sub_add_distr, <- Nat.add_sub_assoc in JMP by apply Nat.le_sub_l.
      rewrite Nat_sub_sub_cancel in JMP by (rewrite <- (Nat.sub_add _ _ JHI), Nat.add_comm; apply Nat.add_le_mono_r, TAG).
      rewrite Nat.add_comm, <- !Nat.add_assoc, <- !app_length, concat_last, firstn_app_nth in JMP by exact BLK.
      rewrite Nat2Z.inj_add, <- (sumsizes_newinstrs _ NC), N.mod_small in JMP by (
        rewrite <- (N2Z.id (2^30)%N);
        (apply Z2N_lt; [reflexivity|]);
        (eapply Z.le_lt_trans; [apply Z.add_le_mono_l, newoffset_bounds|]);
        rewrite Z.add_assoc, Z.sub_add, <- Z.add_assoc, <- sumsizes_app, firstn_skipn; exact SIZ ).
      rewrite newoffset_index, rev_involutive, firstn_cons_skipn, Z.add_sub_assoc, Z.sub_add_simpl_r_r, sumsizes_cons,
              sumsizes_rev, (Z.add_comm (newsize _)), <- sumsizes_firstn_S in JMP by exact DAT'.
      rewrite <- Z.add_sub_assoc, <- Z.add_assoc, Zplus_minus in JMP.
      rewrite (sumsizes_newinstrs _ NC), <- Nat2Z.inj_add, Nat2Z2N in JMP. apply Nat2N.inj in JMP.
      right. left. subst j'. rewrite Nat.add_comm, Nat.add_sub. split; [|left].

        eexists. reflexivity.

        rewrite rev_length, firstn_length_le by (apply Nat.lt_le_incl, nth_error_Some; rewrite DAT'; discriminate).
        rewrite skipn_length, <- (newinstrs_length NC), Nat.sub_succ_r, Nat2Z.inj_pred in I'LE by
        ( apply Nat.lt_add_lt_sub_r, nth_error_Some; rewrite Nat.add_0_l, BLK; discriminate ).
        rewrite rev_length, firstn_length_le in I'GE by
        ( rewrite <- (newinstrs_length NC); apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate ).
        rewrite (indexmap_inv _ NC).
          rewrite Z2Nat.id, Z.add_simpl_l by exact I'GE. apply mem_In, IN'.

          rewrite <- (Nat2Z.id (length l')). apply Z2Nat_le, Z.le_add_le_sub_l.
          rewrite <- Nat2Z.inj_sub by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
          etransitivity. apply I'LE. apply Z.le_pred_l.

    rewrite <- Nat2N.inj_add, Nat.add_sub_assoc by
    (apply Nat.le_sub_le_add_l; rewrite <- Nat.add_assoc, <- app_length; apply Nat.lt_le_incl, BND).
    rewrite Nat.add_comm, <- Nat.add_sub_assoc by (rewrite <- Nat.sub_add_distr; apply Nat.le_sub_l).
    rewrite <- Nat.sub_add_distr, Nat_sub_sub_cancel, Nat.add_comm, <- !Nat.add_assoc by
    ( rewrite <- (Nat.sub_add _ _ JHI), Nat.add_comm; apply Nat.add_le_mono_r, TAG ).
    apply N2Z.inj_lt. rewrite nat_N_Z, 2!Nat2Z.inj_add, <- (sumsizes_newinstrs _ NC), <- NS.
    rewrite <- sumsizes_firstn_S by exact DAT'.
    eapply Z.le_lt_trans. apply Z.add_le_mono_l, sumsizes_firstn_le. exact SIZ.

  (* If the original code was an indirect jump... *)
  destruct (ie #& 127 =? 103) eqn:OP103. clear OP55 OP99. apply Z.eqb_eq in OP103.
  set (k := (j - bi' - _ - _)%nat) in IE'.
  assert (K: (k < length b)%nat). apply nth_error_Some. rewrite IE'. discriminate 1.
  apply Nat.lt_le_pred, Nat.le_lteq in K. destruct K as [K|K].

    (* All the direct control-flows within the guard code are policy-compliant. *)
    assert (JBK: (j - bi' + (length b - k))%nat = length (concat (firstn (S i) l'))).
      unfold k. rewrite <- Nat.sub_add_distr, Nat_sub_sub_distr by (exact TAG +
        apply Nat.le_sub_le_add_l; rewrite <- Nat.add_assoc, <- app_length; apply Nat.lt_le_incl, BND).
      rewrite (Nat.add_comm (length b)), <- Nat.add_assoc, <- app_length, le_pmr by apply Nat.lt_le_incl, BND.
      rewrite <- app_length, concat_last, (firstn_app_nth _ _ _ _ BLK). reflexivity.
    rewrite Nat2N.inj_succ in EX. eapply newijump_exit_internal in NI; try eassumption.

      destruct NI as [[k' [NI1 NI2]]|NI].

        left. apply (f_equal N.to_nat) in NI1. rewrite N2Nat.inj_add, !Nat2N.id in NI1. subst j'.
        eapply indexmap_same. eassumption. apply BND. apply Nat.sub_le_mono_r, Nat.le_add_r.
        rewrite <- app_length, concat_last, (firstn_app_nth _ _ _ _ BLK), <- JBK, (Nat.add_sub_swap _ _ _ JHI). apply Nat.add_lt_mono_l, NI2.

        right. right. right.
        apply (f_equal N.to_nat) in NI. rewrite !N2Nat.inj_add, !Nat2N.id, Z_N_nat, Nat.add_assoc, <- (Nat.sub_add _ _ JHI), (Nat.add_comm _ bi'), <- (Nat.add_assoc bi'), JBK in NI.
        subst j'. rewrite <- Nat.add_assoc. apply Nat.add_le_mono_l, Nat2Z.inj_le.
        rewrite Nat2Z.inj_add, Z2Nat.id, <- (sumsizes_newinstrs _ NC), <- sumsizes_app, firstn_skipn by apply sumsizes_nonneg.
        erewrite sumsizes_newinstrs_all by exact NC. reflexivity.

      apply N2Z.inj_lt. rewrite <- Nat2N.inj_add, <- (Nat.sub_add _ _ JHI), (Nat.add_comm _ bi'), <- Nat.add_assoc, JBK, N2Z.inj_add, nat_N_Z, Z2N.id by apply sumsizes_nonneg.
      rewrite Nat2Z.inj_add, <- (sumsizes_newinstrs _ NC), <- Z.add_assoc, <- sumsizes_app, firstn_skipn. exact SIZ.

    (* The final indirect jump is safe due to the guard code. *)
    right. destruct (Nat.le_gt_cases bi' j') as [BIJ'|J'BI]; [| right; left; exact J'BI ].
    unfold k in K. rewrite <- Nat.sub_add_distr in K. eapply Nat.add_cancel_r in K. rewrite Nat.sub_add in K by apply TAG.
    rewrite Nat.add_pred_l in K by (erewrite newijump_size by exact NI; destruct sb; discriminate 1).
    rewrite Nat.add_comm, <- Nat.add_assoc in K. rewrite <- !app_length, concat_last, firstn_app_nth in K by exact BLK.
    eapply Nat.add_cancel_l in K. rewrite (le_pmr _ _ JHI) in K.
    rewrite K in XP0, XS, EX. rewrite plus_n_Sm, Nat.succ_pred_pos in EX by (destruct l'; [ discriminate BLK | destruct l0; [ apply (newinstrs_nonnil _ _ _ _ O) in NC; contradiction | apply Nat.lt_0_succ ] ] ).
    eapply newijump_indirect_exit in XP0; try eassumption.
      destruct (nth_error _ (indexmap' l' (j'-bi'))) as [[[iid2|] oid2 sd2 ie2 sb2]|] eqn:DAT2.
        left. split. apply XP0. right. exists iid2, (oid2, sd2). split; [|apply XP0]. eapply nth_shrink_preserves. exact DAT2.
        contradiction.
        right. right. exact XP0.
      apply N2Z.inj_lt. rewrite nat_N_Z, Nat2Z.inj_add, <- (sumsizes_newinstrs_all NC). exact SIZ.
      replace (Nat.pred _) with k. exact IE'.
        subst k. rewrite K, Nat.add_comm, Nat.add_sub, firstn_last, BLK, concat_app, concat_cons, app_nil_r, !app_length, Nat.add_assoc, <- Nat.sub_add_distr, <- Nat.add_pred_r.
          rewrite Nat.add_comm. apply Nat.add_sub.
          erewrite newijump_size by exact NI. destruct sb; discriminate 1.

  (* If the original code was a direct jump, the destination satisfies the policy. *)
  destruct (ie #& 127 =? 111) eqn:OP111. clear OP55 OP99 OP103. apply Z.eqb_eq in OP111.
  destruct andb eqn:H; [|discriminate].
  apply andb_prop in H. destruct H as [H I'LE]. apply Z.leb_le in I'LE.
  apply andb_prop in H. destruct H as [IN' I'GE]. apply Z.leb_le in I'GE.
  right. left. eapply newjump_exit in XS; [| eassumption | eassumption | Z_nonneg
  | change 31 with (Z.ones 5); rewrite Z.land_ones by discriminate 1; apply Z.mod_pos_bound; reflexivity ].
  destruct XS as [[J'LB J'UB] H]. subst x.
  apply invExit, N.mul_cancel_l in EX; [|discriminate].
  rewrite nat_N_Z, newoffset_index, rev_involutive, rev_length, firstn_cons_skipn in EX by exact DAT'.
  rewrite firstn_length_le in EX by (rewrite <- (newinstrs_length NC); apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
  rewrite sumsizes_cons, sumsizes_rev, NS, Nat2Z.inj_add, (sumsizes_newinstrs i NC) in EX.
  rewrite app_length, Nat.add_assoc in BND. rewrite (newjump_size _ _ _ NI) in EX, BND.
  rewrite (Z.add_comm (Z.of_nat (length _)) (Z.of_nat 1)), <- Z.add_assoc, Z.add_add_simpl_r_l in EX.
  rewrite <- (Nat.sub_add _ _ JHI), Nat.add_comm, Nat2Z.inj_add, <- Z.add_assoc in EX.
  rewrite (Nat_squeeze _ _ TAG (proj2 BND)), Nat.add_comm, Nat2Z.inj_add, Zplus_minus in EX.
  rewrite N.mod_small in EX by (rewrite <- (N2Z.id (2^30)); apply Z2N_lt; [ reflexivity | eapply Z.le_lt_trans; [ apply Z.add_le_mono_l, sumsizes_firstn_le | exact SIZ ] ]).
  rewrite Z2N.inj_add, (sumsizes_newinstrs _ NC), !Nat2Z2N, <- Nat2N.inj_add in EX by (apply Nat2Z.is_nonneg + apply sumsizes_nonneg).
  apply Nat2N.inj in EX. subst j'. rewrite Nat.add_comm, Nat.add_sub. split; [|left].

    eexists. reflexivity.

    assert (IL': (i < length l')%nat). apply nth_error_Some. rewrite BLK. discriminate.
    rewrite rev_length, firstn_length_le in I'GE by (rewrite <- (newinstrs_length NC); apply Nat.lt_le_incl, IL').
    rewrite skipn_length, <- (newinstrs_length NC), Nat.sub_succ_r, Nat2Z.inj_pred in I'LE by apply Nat.lt_add_lt_sub_r, IL'.
    rewrite (indexmap_inv _ NC).
      rewrite Z2Nat.id, Z.add_simpl_l by exact I'GE. apply mem_In, IN'.
      apply Nat2Z.inj_le. rewrite Z2Nat.id.
        apply Z.le_add_le_sub_l. rewrite <- Nat2Z.inj_sub by apply Nat.lt_le_incl, IL'.
        etransitivity. apply I'LE. apply Z.le_pred_l.
      apply I'GE.

  (* Otherwise, the original code was a security-irrelevant instruction. *)
  right. left.
  destruct mem eqn:IN1; [|discriminate].
  apply invSome in NI. subst b.
  destruct (j - bi' - _ - _)%nat; [|destruct n0; discriminate]. apply invSome in IE'. subst ie'.
  apply rv_fallthru in XS; try assumption. destruct XS; subst x; [|discriminate].
  apply invExit, N.mul_cancel_l, Nat2N.inj in EX; [|discriminate]. subst j'.
  rewrite app_length, Nat.add_assoc in BND. apply Nat_squeeze in TAG; [|apply BND].
  rewrite <- (Nat.add_sub (length (newtag _)) (length (ie::nil))) in TAG.
  rewrite Nat.add_sub_assoc in TAG by apply Nat.le_add_l.
  rewrite <- (Nat2Z.id (_+length _)), <- NS, <- (Nat2Z.id (length _)), <- (sumsizes_newinstrs _ NC) in TAG.
  rewrite <- Z2Nat.inj_add in TAG; [|apply sumsizes_nonneg | etransitivity; [|apply newsize_pos]; discriminate].
  rewrite <- (sumsizes_firstn_S _ _ _ DAT'), (sumsizes_newinstrs _ NC), Nat2Z.id, Nat.sub_1_r in TAG.
  rewrite (Nat.sub_succ_l _ _ JHI), TAG, Nat.succ_pred by (rewrite firstn_last, BLK, <- concat_last, <- rev_length, !rev_app_distr, !app_length; discriminate).
  split; [|left].

    eexists. reflexivity.

    rewrite (indexmap_inv _ NC) by (apply Nat.le_succ_l, nth_error_Some; rewrite BLK; discriminate).
    rewrite Nat2Z.inj_succ, Z.sub_succ_l, Z.sub_diag. apply mem_In, IN1.
Qed.
