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
Definition Z32767 := 32767.
Definition Z1245169 := 1245169.
Definition Z1245171 := 1245171.
Definition Z33554428 := 33554428.
Definition Z_33554432 := -33554432.
Definition Z4294967296 := 4294967296.

Definition Z_popcount z :=
  match z with Z0 => Z0
  | Z.pos p => Z.pos (Pos_popcount p)
  | _ => Z0
  end.

(* checks if l contains z *)
Definition contains z l :=
  match find (Z.eqb z) l with
  | Some _ => true
  | None => false
  end.

(* checks if all elements in the two lists are unique,
   but allows the two elements at the same index in l and l' to be the same *)
Fixpoint unique_except_pairs l l' :=
  match l, l' with
  | a::t, a'::t' => if contains a (t++t') || contains a' (t++t') then false
                   else unique_except_pairs t t'
  | _, _ => true
  end.

(* H(x) = (x << sl) >> sr *)
Definition apply_hash sl sr z :=
  Z.shiftr ((Z.shiftl z sl) mod (Z4294967296)) sr.

(* checks if the hash produces no unacceptable collisions
   dis dis' - list of old/new destination indexes
   sl sr - hash parameters *)
Definition valid_hash dis dis' sl sr :=
  unique_except_pairs (map (apply_hash sl sr) dis) (map (apply_hash sl sr) dis').

Function find_sr dis dis' sl sr {measure Z.to_nat sr} :=
  if sr <=? Z0 then None
  else if valid_hash dis dis' sl sr then Some sr else find_sr dis dis' sl (sr-Z1).
Proof. unfold Z1 in *. lia. Qed.

Function find_hash dis dis' sl {measure Z.to_nat sl} :=
  if sl <=? Z2 then None
  else match find_sr dis dis' sl Z31 with
       | Some sr => Some (sl, sr)
       | None => find_hash dis dis' (sl-Z1)
       end.
Proof. unfold Z1, Z2 in *. lia. Qed.

(* make a function that maps table index to the value in the table at that index
   dis dis' - list of old/new destination indexes
   sl, sr - from find_hash
   f - default value (fun _ -> abort address) *)
Fixpoint make_jump_table_map dis dis' sl sr f :=
  match dis, dis' with
  | di::t, di'::t' =>
      let j := apply_hash sl sr di in
      let k := apply_hash sl sr di' in
      let f' := make_jump_table_map t t' sl sr f in
      fun x => if (x =? j) || (x =? k) then Z4 * di' else f' x
  | _, _ => f
  end.

Function map2list (m: Z -> Z) n
    {measure Z.to_nat n} :=
  if n >? Z0 then m (n-Z1)::map2list m (n-Z1)
  else nil.
Proof. intros. unfold Z1 in *. lia. Qed.

Fixpoint _map2list (m: Z -> Z) n :=
  match n with
  | S n' => m (Z.of_nat n')::_map2list m n'
  | O => nil
  end.
Lemma map2list_func : forall m n, _map2list m n = map2list m (Z.of_nat n).
Proof.
  intros. induction n.
    now rewrite map2list_equation.
    simpl. rewrite IHn, map2list_equation with (n := Z.pos _).
      now replace (_ - _) with (Z.of_nat n) by (unfold Z1; lia).
Qed.
Lemma map2list_fix : forall m n, map2list m n = _map2list m (Z.to_nat n).
Proof.
  intros. symmetry. destruct n.
    rewrite <- Nat2Z.inj_0. apply map2list_func.
    rewrite <- (Z2Nat.id _ (Zle_0_pos _)) at 2. apply map2list_func.
    now rewrite map2list_equation.
Qed.

Definition make_jump_table dis dis' ai sl sr n :=
  let m := make_jump_table_map dis dis' sl sr (fun _ => Z4 * ai) in
  rev (map2list m n).


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
Definition MOV rd rm :=
  ARM_data_r ARM_MOV Z14 Z0 Z0 rd 0 Z0 rm.
Definition LSL rd rm imm :=
  ARM_data_r ARM_MOV Z14 Z0 Z0 rd imm Z0 rm.
Definition LSR rd rm imm :=
  ARM_data_r ARM_MOV Z14 Z0 Z0 rd imm Z1 rm.
Definition STMDB2 rn r0 r1 :=
  ARM_lsm ARM_STMDB Z14 Z0 rn ((Z1 << r0) .| (Z1 << r1)).
Definition LDMDB2 rn r0 r1 :=
  ARM_lsm ARM_LDMDB Z14 Z0 rn ((Z1 << r0) .| (Z1 << r1)).
Definition STMDB3 rn r0 r1 r2 :=
  ARM_lsm ARM_STMDB Z14 Z0 rn ((Z1 << r0) .| (Z1 << r1) .| (Z1 << r2)).
Definition LDMDB3 rn r0 r1 r2 :=
  ARM_lsm ARM_LDMDB Z14 Z0 rn ((Z1 << r0) .| (Z1 << r1) .| (Z1 << r2)).
Definition UBFX rd rn sl sr :=
  ARM_bfx false Z14 (Z31-sr) rd (sr-sl) rn.
Definition GOTO (l: bool) (cond src dest: Z) :=
  let offset := Z4 * (dest - src) - Z8 in
  let offset := if (offset >? Z1 << Z31) then offset - (Z1 << Z32) else offset in
  let imm := offset mod (Z1 << Z26) in
  (if l then ARM_BL else ARM_B) cond (imm >> Z2).

Definition arm_add (reg imm: Z) : list arm_inst :=
  let a := ARM_data_i ARM_ADD Z14 Z0 reg reg in
    a ((Z4 << Z8) .| ((imm >> Z24) & Z0xff))::
    a ((Z8 << Z8) .| ((imm >> Z16) & Z0xff))::
    a ((Z12 << Z8) .| ((imm >> Z8) & Z0xff))::
    a (imm & Z0xff)::nil.
(* reg = table[H(reg)] *)
Definition arm_table_lookup ti sl sr reg :=
  [ UBFX reg reg (sl-Z2) sr;
    LSL reg reg Z2          (* lsl reg, reg, #2 *)
  ]++arm_add reg (Z4*ti)++[ (* add reg, reg, #4*ti *)
    LDR reg reg Z0          (* ldr reg, [reg] *)
  ].
Definition IRM := Z -> Z -> Z -> Z -> Z -> option (list Z).
Definition TableCache := list Z -> option (Z * Z * Z).
Definition NewInst := option (list Z * list Z * TableCache).
Definition wo_table z' tc : NewInst :=
  match z' with
  | Some z' => Some (z', nil, tc)
  | None => None
  end.

Definition invert_cond cond :=
  if (cond mod Z2 =? Z0) then cond + Z1
  else cond - Z1.

(* assemble insts and add a branch to the start if conditional *)
Definition arm_assemble_all_cond insts cond :=
  let jump_after := ARM_B (invert_cond cond) (Z.of_nat (length insts) - Z1) in
  if (cond <? Z14) then arm_assemble_all (jump_after::insts)
  else arm_assemble_all insts.

Fixpoint list_eqb l1 l2 :=
  match l1, l2 with
  | a::b, c::d => if a =? c then list_eqb b d else false
  | nil, nil => true
  | _, _ => false
  end.
Definition rewrite_w_table
    (irm: IRM)
    (tc: TableCache)
    (dis dis': list Z)
    (cond z i ti ai: Z)
    : NewInst :=
  match tc dis with
  | None =>
      match find_hash dis dis' Z31 with
      | None => None
      | Some (sl, sr) =>
          match irm cond i ti sl sr with
          | None => None
          | Some irm =>
              let table := make_jump_table dis dis' ai sl sr (Z1 << (Z32 - sr)) in
              let tc' := fun x => if (list_eqb x dis) then Some (ti, sl, sr) else tc x in
              Some (irm, table, tc')
          end
      end
  | Some (ti, sl, sr) =>
      match irm cond i ti sl sr with
      | None => None
      | Some irm => Some (irm, nil, tc)
      end
  end.

Definition bx_irm reg : IRM :=
  fun cond i ti sl sr =>
    arm_assemble_all_cond (
      arm_table_lookup ti sl sr reg++  (* reg = table[H(reg)] *)
      ARM_BX Z14 reg::nil              (* bx reg *)
    ) cond.
Definition rewrite_bx reg := rewrite_w_table (bx_irm reg).
Definition blx_irm reg : IRM :=
  fun cond i ti sl sr =>
    arm_assemble_all_cond (
      arm_table_lookup ti sl sr reg++  (* reg = table[H(reg)] *)
      ARM_BLX_r Z14 reg::nil           (* blx reg *)
    ) cond.
Definition rewrite_blx reg := rewrite_w_table (blx_irm reg).
Definition ldm_pc_irm op Rn register_list reg orig_inst : IRM :=
  fun cond i ti sl sr =>
    let bc := Z4 * Z_popcount register_list in
    let offset := arm_lsm_op_start op bc + bc - Z4 in
    arm_assemble_all_cond ([
      STR reg SP Z_4;                     (* str reg, [sp, #-4] *)
      LDR reg Rn offset                   (* ldr reg, [Rn, #pc_offset] *)
    ]++arm_table_lookup ti sl sr reg++[   (* reg = table[H(reg)] *)
      STR reg Rn offset;                  (* str reg, [Rn, #pc_offset] *)
      LDR reg SP Z_4;                     (* ldr reg, [sp, #-4] *)
      orig_inst                           (* original inst *)
    ]) cond.
Definition rewrite_ldm_pc op Rn register_list reg orig_inst := rewrite_w_table (ldm_pc_irm op Rn register_list reg orig_inst).

(* irm for instructions that use pc as a destination register, but do not modify sp *)
Definition pc_irm sanitized_inst reg : IRM :=
  fun cond i ti sl sr =>
    let a := Z4 * i + Z8 in
    arm_assemble_all_cond ([
      STR   reg SP Z_4;                  (* str reg, [sp, #-4] *)
      MOVW  reg (a & Z0xffff);           (* movw reg, #a[16:0] *)
      MOVT  reg ((a >> Z16) & Z0xffff);  (* movt reg, #a[32:16] *)
      sanitized_inst                     (* sanitized_inst *)
    ]++arm_table_lookup ti sl sr reg++[  (* reg = table[H(reg)] *)
      STR   reg SP Z_8;                  (* str reg, [sp, #-8] *)
      LDR   reg SP Z_4;                  (* ldr reg, [sp, #-4] *)
      LDR   PC  SP Z_8                   (* ldr pc, [sp, #-8] *)
    ]) cond.
(* irm for instructions that use pc as a destination register, and do modify sp *)
Definition pc_sp_irm sanitized_inst reg reg2 : IRM :=
  fun cond i ti sl sr =>
    let a := Z4 * i + Z8 in
    arm_assemble_all_cond ([
      STMDB3 SP reg reg2 PC;
      MOV   reg2 SP;
      MOVW  reg (a & Z0xffff);                (* movw reg, #a[16:0] *)
      MOVT  reg ((a >> Z16) & Z0xffff);       (* movt reg, #a[32:16] *)
      sanitized_inst                          (* sanitized_inst *)
    ]++arm_table_lookup ti sl sr reg++[       (* reg = table[H(reg)] *)
      STR   reg reg2 (Z_4);                   (* str reg, [sp, #-8 - stack offset] *)
      LDMDB3 reg2 reg reg2 PC                 (* ldmdb reg2, {reg, reg2, pc} *)
    ]) cond.
Definition rewrite_pc sanitized_inst reg := rewrite_w_table (pc_irm sanitized_inst reg).
Definition rewrite_pc_sp sanitized_inst reg reg2 := rewrite_w_table (pc_sp_irm sanitized_inst reg reg2).
Definition rewrite_pc_no_jump sanitized_inst cond i reg tc : NewInst :=
  let a := Z4 * i + Z8 in
  wo_table (arm_assemble_all_cond ([
    STR reg SP Z_4;                    (* str reg, [sp, #-4] *)
    MOVW reg (a & Z0xffff);            (* movw reg, #a[16:0] *)
    MOVT reg ((a >> Z16) & Z0xffff);   (* movt reg, #a[32:16] *)
    sanitized_inst;                    (* santitized_inst *)
    LDR reg SP Z_4                     (* ldr reg, [sp, #-4] *)
  ]) cond) tc.
Definition rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc : NewInst :=
  let a := Z4 * i + Z8 in
  wo_table (arm_assemble_all_cond ([
    STMDB2 SP reg reg2;                (* stmdb sp, {reg, reg2} *)
    MOV reg2 SP;                       (* mov reg2, sp *)
    MOVW reg (a & Z0xffff);            (* movw reg, #a[16:0] *)
    MOVT reg ((a >> Z16) & Z0xffff);   (* movt reg, #a[32:16] *)
    sanitized_inst;                    (* santitized_inst *)
    LDMDB2 reg2 reg reg2               (* ldmdb reg2, {reg, reg2} *)
  ]) cond) tc.

Definition canonical_z w z := (z + (Z1 << (w-Z1))) mod (Z1 << w) - (Z1 << (w-Z1)).
Definition rewrite_b_bl (l: bool) (cond imm24: Z) i dis i2i' ai tc : NewInst :=
  let j := (i + Z2 + (canonical_z Z24 imm24)) mod (Z1 << Z30) in
  let dst := if (contains j dis) || true then (i2i' j) else ai in
  match arm_assemble (GOTO l cond (i2i' i) dst) with
  | Some z => Some ([z], nil, tc)
  | None => match arm_assemble (GOTO l cond (i2i' i) ai) with
            | Some z => Some ([z], nil, tc)
            | None => None
            end
  end.
Definition rewrite_b := rewrite_b_bl false.
Definition rewrite_bl := rewrite_b_bl true.

(* "mov lr, pc" should use new pc, not old pc
it's possible that the old pc should be used, if lr is later used as a data memory address,
but a compiler would most likely pick a general register instead of lr if that was the case

although any rewritten jump would be able to handle the old pc value correctly, this inst
is sometimes used when calling a kernel user helper function, which we cannot rewrite *)
Definition rewrite_mov_lr_pc i i2i' tc : NewInst :=
  let pc' := Z4 * i2i' (i+Z2) in
  wo_table (arm_assemble_all ([
    MOVW  LR (pc' & Z0xffff);
    MOVT  LR ((pc' >> Z16) & Z0xffff)
  ])) tc.

Definition unused_reg (r0 r1 r2: Z) :=
  if (r0 =? Z0) || (r1 =? Z0) || (r2 =? Z0) then
    if (r0 =? Z1) || (r1 =? Z1) || (r2 =? Z1) then
      if (r0 =? Z2) || (r1 =? Z2) || (r2 =? Z2) then Z3
      else Z2
    else Z1
  else Z0.
Definition unused_reg_high (r0 r1 r2: Z) :=
  if (r0 =? Z4) || (r1 =? Z4) || (r2 =? Z4) then
    if (r0 =? Z5) || (r1 =? Z5) || (r2 =? Z5) then
      if (r0 =? Z6) || (r1 =? Z6) || (r2 =? Z6) then Z7
      else Z6
    else Z5
  else Z4.
Definition goto_abort i' ai tc : NewInst :=
  match arm_assemble (GOTO true Z14 i' ai) with
  | Some z => Some ([z], nil, tc)
  | None => None
  end.
Definition rewrite_inst (tc: TableCache) (i2i': Z -> Z) (z: Z) (dis: list Z) (i ti ai bi: Z) (txt: list Z) : NewInst :=
  let unchanged := Some ([z], nil, tc) in
  let abort := goto_abort (i2i' i) ai tc in
  let dis' := map i2i' dis in
  let decoded := arm_decode z in
  match decoded with
  (* branching *)
  | ARM_BX cond reg => rewrite_bx reg tc dis dis' cond z i ti ai
  | ARM_BLX_r cond reg => rewrite_blx reg tc dis dis' cond z i ti ai
  | ARM_B cond imm24 => rewrite_b cond imm24 i dis i2i' ai tc
  | ARM_BL cond imm24 => rewrite_bl cond imm24 i dis i2i' ai tc
  (* data processing *)
  | ARM_data_r op cond s Rn Rd imm5 type Rm =>
      let reg := unused_reg Rn Rd Rm in
      let reg2 := unused_reg_high Rn Rd Rm in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rd' := if (Rd =? PC) then reg else Rd in
      let Rm' := if (Rm =? PC) then reg else Rm in
      let sanitized_inst := ARM_data_r op Z14 s Rn' Rd' imm5 type Rm' in
      if (Rd =? PC) then
        rewrite_pc sanitized_inst reg tc dis dis' cond z i ti ai
      else if (Rn =? PC) || (Rm =? PC) then
        if (match op with ARM_MOV => Rd =? LR | _ => false end) then
          rewrite_mov_lr_pc i i2i' tc
        else if (Rd =? SP) then
          rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
        else
          rewrite_pc_no_jump sanitized_inst cond i reg tc
      else unchanged
  | ARM_data_i op cond s Rn Rd imm12 =>
      let reg := unused_reg Rn Rd Z0 in
      let reg2 := unused_reg_high Rn Rd Z0 in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rd' := if (Rd =? PC) then reg else Rd in
      let sanitized_inst := ARM_data_i op Z14 s Rn' Rd' imm12 in
      if (Rd =? PC) then
        rewrite_pc sanitized_inst reg tc dis dis' cond z i ti ai
      else if (Rn =? PC) then
        if (Rd =? SP) then
          rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
        else
          rewrite_pc_no_jump sanitized_inst cond i reg tc
      else unchanged
  (* load/store *)
  | ARM_ls_i ARM_LDR cond P U W Rn Rt imm12 =>
      let reg := unused_reg Rn Rt Z0 in
      let reg2 := unused_reg_high Rn Rt Z0 in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rt' := if (Rt =? PC) then reg else Rt in
      let sanitized_inst := ARM_ls_i ARM_LDR cond P U W Rn' Rt' imm12 in
      if (Rt =? PC) then
        if ((Rn =? SP) && ((P =? Z0) || (W =? Z1))) then rewrite_pc_sp sanitized_inst reg reg2 tc dis dis' cond z i ti ai
        else rewrite_pc sanitized_inst reg tc dis dis' cond z i ti ai
      else if (Rn =? PC) then
        let li := bi-((if (U =? Z1) then i + Z2 + imm12 else i + Z2 - imm12) mod (Z1 << Z32)) in
        match li >? Z0, nth_error txt (Z.to_nat (bi-li)) with
        | true, Some lv =>
             wo_table (arm_assemble_all_cond [
               MOVW  Rt (lv & Z0xffff);
               MOVT  Rt ((lv >> Z16) & Z0xffff)
             ] cond) tc
        | _, _ =>
            if (Rt =? SP) then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
            else rewrite_pc_no_jump sanitized_inst cond i reg tc
        end
      else unchanged
  | ARM_ls_r ARM_LDR cond P U W Rn Rt imm5 type Rm =>
      let reg := unused_reg Rn Rt Rm in
      let reg2 := unused_reg_high Rn Rt Rm in
      let Rn' := if (Rn =? PC) then reg else Rn in
      let Rt' := if (Rt =? PC) then reg else Rt in
      let Rm' := if (Rm =? PC) then reg else Rm in
      let sanitized_inst := ARM_ls_r ARM_LDR cond P U W Rn' Rt' imm5 type Rm' in
      if (Rt =? PC) then
        if ((Rn =? SP) && ((P =? Z0) || (W =? Z1))) then rewrite_pc_sp sanitized_inst reg reg2 tc dis dis' cond z i ti ai
        else rewrite_pc sanitized_inst reg tc dis dis' cond z i ti ai
      else if (Rn =? PC) || (Rm =? PC) then
        if (Rt =? SP) then rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
        else rewrite_pc_no_jump sanitized_inst cond i reg tc
      else unchanged
  | ARM_lsm op cond W Rn register_list =>
      if (register_list <? (Z1 << Z15)) then unchanged (* pc is not in reg list *)
      else
        let reg := if (Rn =? Z0) then Z1 else Z0 in
        rewrite_ldm_pc op Rn register_list reg decoded tc dis dis' cond z i ti ai
  | ARM_vls is_load is_single cond U D Rn Vd imm8 =>
      if (Rn =? PC) then
        let sanitized_inst := ARM_vls is_load is_single cond U D Z0 Vd imm8 in
        rewrite_pc_no_jump sanitized_inst cond i Z0 tc
      else unchanged
  (* | ARM_sync_s ARM_sync_word cond Rn Rd Rt => *)
  (*    match arm_assemble_all_cond [ STR Rt Rn 0; MOVW Rd 0 ] cond with *)
  (*    | Some z => Some (z, nil) *)
  (*    | None => None *)
  (*    end *)
  (* unchanged *)
  | ARM_extra_ls_i op cond P U W Rn Rt imm4H imm4L =>
      let reg := if (Rt =? Z0) then Z1 else Z0 in
      let reg2 := if (Rt =? Z2) then Z3 else Z2 in
      let sanitized_inst := ARM_extra_ls_i op cond P U W reg Rt imm4H imm4L in
      if (Rn =? PC) then
        if (match op with ARM_STRH | ARM_STRD => false | _ => Rt =? SP end) then
          rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
        else rewrite_pc_no_jump sanitized_inst cond i reg tc
      else unchanged
  | ARM_extra_ls_r op cond P U W Rn Rt Rm =>
      let reg := if (Rt =? Z0) then Z1 else Z0 in
      let reg2 := if (Rt =? Z2) then Z3 else Z2 in
      let sanitized_inst := ARM_extra_ls_r op cond P U W reg Rt Rm in
      if (Rn =? PC) then
        if (match op with ARM_STRH | ARM_STRD => false | _ => Rt =? SP end) then
          rewrite_pc_sp_no_jump sanitized_inst cond i reg reg2 tc
        else rewrite_pc_no_jump sanitized_inst cond i reg tc
      else unchanged
  | ARM_sync_l _ _ _ _
  | ARM_sync_s _ _ _ _ _
  | ARM_hint _ _
  | ARM_sat _ _ _ _ _
  | ARM_mul _ _ _ _ _ _ _
  | ARM_hmul _ _ _ _ _ _ _ _
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

  | _ => abort
  end.

(*
   pol - maps indexes to lists of valid destination indexes
   i2i' - maps old indexes to new indexes
   zs - list of instruction encodings
   i - current index
   ti - table index
   ai - abort index
   bi - base index
   txt - same as zs but doesn't change when recursing
*)
Fixpoint _rewrite (tc: TableCache) (pol: Z -> list Z) (i2i': Z -> Z) (zs: list Z) (i ti ai bi: Z) (txt: list Z) : option (list (list Z) * list (list Z)) :=
  match zs with
  | z::zs =>
      match rewrite_inst tc i2i' z (pol i) i ti ai bi txt with
      | None => None
      | Some (z', table, tc') =>
          let ti' := ti + Z.of_nat (length table) in
          match _rewrite tc' pol i2i' zs (i+Z1) ti' ai bi txt with
          | None => None
          | Some (z_t, table_t) => Some (z'::z_t, table::table_t)
          end
      end
  | nil => Some (nil, nil)
  end.

Definition make_i's (z's: list (list Z)) i' :=
  let lens := map (fun x => Z.of_nat (length x)) z's in
  rev (snd (fold_left (fun a b => let sum := fst a + b in (sum, i' + fst a :: snd a)) lens (0, nil))).
Definition get l n := nth (Z.to_nat n) l 0.
Definition of_list (x: list Z) := x.
Definition make_i2i' i's i :=
  let ie := i + Z.of_nat (length i's) in
  let arr := of_list i's in
  fun x => if (x <? i) || (x >=? ie) then x else get arr (x-i).

Definition rewrite (pol: Z -> list Z) (zs: list Z) (i i' ti ai: Z) :=
  let tc := fun _ => None in
  match _rewrite tc pol id zs i ti ai i zs with
  | Some (z's, _) =>
      let i's := make_i's z's i' in
      let i2i' := make_i2i' i's i in
      _rewrite tc pol i2i' zs i ti ai i zs
  | None => None
  end.

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
Extract Inlined Constant nth_error => "(List.nth_opt)".
Extract Inlined Constant app => "List.append".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant combine => "List.combine".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extract Inductive sigT => "( * )"  [ "(,)" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant rev => "List.rev".
Extract Inlined Constant fold_left => "(fun f l a -> List.fold_left f a l)".
Extract Inlined Constant get => "Array.get".
Extract Inlined Constant of_list => "Array.of_list".
Extract Inlined Constant id => "Fun.id".
Separate Extraction rewrite.
