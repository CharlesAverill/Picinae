Require Import Picinae_ftoyisa.
Require Import NArith.
Require Import Lia.
Open Scope N.
Import FTOYNotations.

(* SP points to the next available location on the stack and grows downward. *)
Inductive asm : Set :=
  | add (rd rs rt:ftoyvar)
  | lsl (rd rs:ftoyvar) (imm:N)
  | li (rd:ftoyvar) (imm:N)
  | call (rs:ftoyvar)
  | ret
  | bi (simm:N)
  | br (rs:ftoyvar)
  | str (rd rs:ftoyvar) (simm:N)
  | ldr (rd rs:ftoyvar) (simm:N)
  | cbnz (rd:ftoyvar) (simm:N)
  | cmp (rd:ftoyvar) (simm24:N).


Scheme Equality for asm.

Definition decode_reg n :=
  match n with
  | 0 => Some R_0
  | 1 => Some R_1
  | 2 => Some R_2
  | 3 => Some R_3
  | 4 => Some R_4
  | 5 => Some R_5
  | 6 => Some R_SP
  | 7 => Some R_PC
  | _ => None
  end.

Definition encode_reg var : option N :=
  match var with
  | R_0 => Some 0
  | R_1 => Some 1
  | R_2 => Some 2
  | R_3 => Some 3
  | R_4 => Some 4
  | R_5 => Some 5
  | R_SP => Some 6
  | R_PC => Some 7
  | _ => None
  end.

Section Decode.
  Variable n:N.
(*  31  30  29  28  27  26  25  24  23  22  21  20  19  18  17  16  15  14  13  12  11  10   9   8   7   6   5   4   3   2   1   0
    |-  opcode      -|  |-  rd  -|  |-  rs  -|  |-  rt  -|
    |-  opcode      -|  |-  rd  -|  |-  rs  -|  |-  imm lsl         -|
    |-  opcode      -|  |-  rd  -|  |-  rs  -|  |-  imm addi/str/ldr                                                             -|
    |-  opcode      -|  |-  rd  -|  |-  imm li                                                                                   -| *)
  Definition opcode := xbits n 27 32.
  Definition rd := xbits n 24 27.
  Definition rs := xbits n 21 24.
  Definition rt := xbits n 18 21.
  Definition immlsl := xbits n 15 21.
  (*Definition immaddi := xbits n  0 21.*)
  Definition immstr := xbits n  0 21.
  Definition immldr := xbits n  0 21.
  Definition immli := xbits n 0 24.
  Definition immcbnz := xbits n 0 24.
  Definition immcmp := xbits n 0 24.
  Definition simmbi := xbits n 0 27.

Definition decode_add :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Rt <- decode_reg rt;;
  Some (add Rd Rs Rt).

Definition lift_add Rd Rs Rt:=
  let q := (Move Rd (BinOp OP_PLUS (Var Rs) (Var Rt))) in
  Some (if Rd == R_PC then Seq q (Jmp (Var R_PC)) else q).

Definition decode_lsl :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Some (lsl Rd Rs immlsl).

Definition lift_lsl Rd Rs immlsl :=
  let q := (Move Rd (BinOp OP_LSHIFT (Var Rs) (Word immlsl 32))) in
  Some (if Rd == R_PC then Seq q (Jmp (Var R_PC)) else q).

Definition decode_li :=
  Rd <- decode_reg rd;;
  Some (li Rd immli).

Definition lift_li Rd immli :=
  let q := (Move Rd (Word immli 32)) in
  Some (if Rd == R_PC then Seq q (Jmp (Var R_PC)) else q).

Definition decode_call :=
  Rs <- decode_reg rs ;;
  Some (call Rs).

Definition lift_call Rs :=
  Some
    (Seq (Move V_MEM32 (Store (Var V_MEM32) (Var R_SP) (Var R_PC) LittleE 4))
    (Seq (Move R_SP (BinOp OP_MINUS (Var R_PC) (Word 4 32)))
        (Jmp (Var Rs)))).

Definition lift_ret :=
  Some
   (Seq (Move R_PC (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_SP) (Word 4 32)) LittleE 4))
   (Seq (Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 4 32)))
        (Jmp (Var R_PC)))).

Definition decode_bi :=
  Some (bi simmbi).

Definition lift_bi simmbi :=
  Some
    (Seq (Move R_PC (BinOp OP_LSHIFT (Cast CAST_SIGNED 32 (Word simmbi 27)) (Word 2 32)))
         (Jmp (Var R_PC))).

Definition decode_br :=
  Rs <- decode_reg rs ;;
  Some (br Rs).

Definition lift_br Rs :=
  Some (Jmp (Var Rs)).

Definition decode_str :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Some (str Rd Rs immstr).

Definition lift_str Rd Rs simm :=
  Some (Move V_MEM32 (Store (Var V_MEM32) (BinOp OP_PLUS (Var Rd) (Cast CAST_SIGNED 32 (Word simm 21))) (Var Rs) LittleE 4)).

Definition decode_ldr :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Some (ldr Rd Rs immldr).

Definition lift_ldr Rd Rs simm :=
  let q := (Move Rd (Load (Var V_MEM32) (BinOp OP_PLUS (Var Rs) (Cast CAST_SIGNED 32 (Word simm 21))) LittleE 4)) in
  Some (if Rd == R_PC then Seq q (Jmp (Var R_PC)) else q).

Definition decode_cbnz :=
  Rd <- decode_reg rd;;
  Some (cbnz Rd immcbnz).

Definition lift_cbnz Rd simm :=
  Some (If (BinOp OP_EQ (Var Rd) (Word 0 32))
        (Jmp (BinOp OP_PLUS (Var R_PC) (Cast CAST_SIGNED 32 (BinOp OP_LSHIFT (Word simm 26) (Word 2 26)))))
        Nop).

Definition decode_cmp :=
  Rd <- decode_reg rd;;
  Some (cmp Rd immcmp).

Definition lift_cmp Rd imm24 :=
  Some (Move F_LT (BinOp OP_LT (Var Rd) (Cast CAST_UNSIGNED 32 (Word imm24 24))) $;
        Move F_EQ (BinOp OP_EQ (Var Rd) (Cast CAST_UNSIGNED 32 (Word imm24 24))) $;
        Move F_GT (BinOp OP_LT (Cast CAST_UNSIGNED 32 (Word imm24 24)) (Var Rd))).

Definition decode_insn :=
  match opcode with
  | 0 => decode_add
  | 1 => decode_lsl
  | 2 => decode_li
  | 3 => decode_call
  | 4 => Some ret
  | 5 => decode_bi
  | 6 => decode_br
  | 7 => decode_str
  | 8 => decode_ldr
  | 9 => decode_cbnz
  | 10 => decode_cmp
  | _ => None
  end.

End Decode.

Definition encode_opcode i :=
  match i with
  | add _ _ _  => 0
  | lsl _ _ _ => 1
  | li _ _ => 2
  | call _ => 3
  | ret => 4
  | bi _ => 5
  | br _ => 6
  | str _ _ _ => 7
  | ldr _ _ _ => 8
  | cbnz _ _ => 9
  | cmp _ _ => 10
  end.

Definition encode_add rd rs rt :=
  let op := encode_opcode (add R_0 R_0 R_0) in
  Rd <- encode_reg rd;;
  Rs <- encode_reg rs;;
  Rt <- encode_reg rt;;
  Some (op << 27 .| Rd << 24 .| Rs << 21 .| Rt << 18).

Definition encode_lsl rd rs imm :=
  let op := encode_opcode (lsl R_0 R_0 0) in
  Rd <- encode_reg rd;;
  Rs <- encode_reg rs;;
  if imm <? 2^6 then Some (op << 27 .| Rd << 24 .| Rs << 21 .| imm)
  else None.

Definition encode_li rd imm :=
  let op := encode_opcode (li R_0 0) in
  Rd <- encode_reg rd;;
  if imm <? 2^24 then Some (op << 27 .| Rd << 24 .| imm)
  else None.

Definition encode_call rs :=
  let op := encode_opcode (call R_0) in
  Rs <- encode_reg rs;;
  Some (op << 27 .| Rs << 21).

Definition encode_ret :=
  let op := encode_opcode ret in Some (op << 27).

Definition encode_bi simm :=
  let op := encode_opcode (bi simm) in
  if simm <? 2^27 then Some (op << 27 .| simm)
  else None.

Definition encode_br rs :=
  let op := encode_opcode (br rs) in
  Rs <- encode_reg rs;;
  Some (op << 27 .| Rs << 21).

Definition encode_str rd rs simm :=
  let op := encode_opcode (str rd rs simm) in
  Rd <- encode_reg rd;;
  Rs <- encode_reg rs;;
  Some (op << 27 .| Rs << 21 .| simm).

Definition encode_ldr rd rs simm :=
  let op := encode_opcode (ldr rd rs simm) in
  Rd <- encode_reg rd;;
  Rs <- encode_reg rs;;
  Some (op << 27 .| Rd << 24 .| Rs << 21 .| simm).

Definition encode_cbnz rd simm:=
  let op := encode_opcode (cbnz rd simm) in
  Rd <- encode_reg rd;;
  Some (op << 27 .| Rd << 24 .| simm).

Definition encode_cmp rd imm24 :=
  let op := encode_opcode (cmp rd imm24) in
  Rd <- encode_reg rd;;
  Some (op << 27 .| Rd << 24 .| imm24).

Definition encode_insn i :=
  n <- match i with
  | add rd rs rt => encode_add rd rs rt
  | lsl rd rs imm => encode_lsl rd rs imm
  | li rd imm => encode_li rd imm
  | call rs => encode_call rs
  | ret => encode_ret
  | bi simm => encode_bi simm
  | br rs => encode_br rs
  | str rd rs simm => encode_str rd rs simm
  | ldr rd rs simm => encode_ldr rd rs simm
  | cbnz rd simm => encode_cbnz rd simm
  | cmp rd imm => encode_cmp rd imm
  end;;
  i' <- decode_insn n;;
  if asm_beq i' i then Some n else None.

Definition lift_insn (v:asm) :=
  match v with
  | add rd rs rt => lift_add rd rs rt
  | lsl rd rs imm => lift_lsl rd rs imm
  | li rd imm => lift_li rd imm
  | call rs => lift_call rs
  | ret => lift_ret
  | bi simm => lift_bi simm
  | br rs => lift_br rs
  | str rd rs simm => lift_str rd rs simm
  | ldr rd rs simm => lift_ldr rd rs simm
  | cbnz rd simm => lift_cbnz rd simm
  | cmp rd imm => lift_cmp rd imm
  end
.

Tactic Notation "mdestruct" "in" hyp(H) :=
  lazymatch type of H with
  | context[_ <- ?x ;; _] =>
      let E := fresh "E" in destruct x eqn:E in H
  end.

Ltac head t :=
  lazymatch t with
  | ?t' _ => head t'
  | ?t' => t'
  end.

Tactic Notation "unfold" "def" "in" hyp(H) :=
  match type of H with
  | ?def = _ => let d := head def in unfold d in H
  end.

Tactic Notation "unfold" "def" :=
  match goal with
  |- _ ?x _ => let d := head x in unfold d
  end.

Tactic Notation "destruct" "if" "in" hyp(H) :=
  lazymatch type of H with
  | context[if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E in H
  end.

Tactic Notation "destruct" "if":=
  lazymatch goal with
  | |- context[if ?c then _ else _] => let E := fresh "E" in destruct c eqn:E
  end.


Lemma decode_reg_32bit :
  forall n r, decode_reg n = Some r -> ftoytypctx r = Some 32.
Proof.
  unfold decode_reg; intros n r DECODE.
  destruct n as [|n]; repeat (discriminate || (inversion DECODE; subst; reflexivity) || destruct n as [n|n|]).
Qed.

Definition sizeof v :=
  match ftoytypctx v with Some w => w | _ => 0 end.

Lemma decode_reg_sizeof32 :
  forall n r, decode_reg n = Some r -> sizeof r = 32.
Proof.
  unfold decode_reg; intros n r DECODE.
  destruct n as [|n]; repeat (discriminate || (inversion DECODE; subst; reflexivity) || destruct n as [n|n|]).
Qed.

Lemma decode_reg_sizeof :
  forall n r, decode_reg n = Some r -> ftoytypctx r = Some (sizeof r).
Proof.
  unfold decode_reg; intros n r DECODE.
  destruct n as [|n]; repeat (discriminate || (inversion DECODE; subst; reflexivity) || destruct n as [n|n|]).
Qed.

Lemma decode_reg_sizeof2 :
  forall n r n2 r2, decode_reg n = Some r -> decode_reg n2 = Some r2 -> ftoytypctx r = Some (sizeof r2).
Proof.
  intros n r n2 r2 DECODE DECODE2.
  erewrite decode_reg_sizeof, !decode_reg_sizeof32; reflexivity || eassumption.
Qed.


Local Lemma update_some:
  forall x y (c c': typctx),
    c x = Some y ->
    c ⊆ c' ->
    c ⊆ c'[x := Some y].
Proof.
  intros. rewrite <- store_upd_eq. assumption. apply H0. assumption.
Qed.
Ltac unfold_rec a :=
  match a with
  | ?x ?y => unfold_rec x
  | _ => unfold a
  end.
Local Ltac etyp :=
  repeat match goal with
         | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ ?x _) _ => apply TBinOp with (w := s)
         | H: hastyp_exp _ ?x ?s |- hastyp_exp _ (BinOp _ _ ?x) _ => apply TBinOp with (w := s)
         | |- hastyp_exp _ (BinOp _ (Word _ ?s) _) _ => apply TBinOp with (w := s)
         | |- hastyp_exp _ (BinOp _ _ (Word _ ?s)) _ => apply TBinOp with (w := s)
         | H: decode_reg _ = Some ?v |- hastyp_exp _ (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := 32)
         | H: decode_reg _ = Some ?v |- hastyp_exp _ (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := 32)
         | |- hastyp_exp _ (BinOp _ (Var ?v) _) _ => apply TBinOp with (w := sizeof v)
         | |- hastyp_exp _ (BinOp _ _ (Var ?v)) _ => apply TBinOp with (w := sizeof v)
         | |- hastyp_exp _ (BinOp ?o ?x ?y) ?a => match eval compute in (widthof_binop o 0 =? 0) with true => apply TBinOp with (w := a) end
         (*| |- hastyp_exp _ (Var (arm_varid _)) 32 => apply hastyp_arm_varid*)
         | |- hastyp_exp _ (Var _) _ => apply TVar
         | |- hastyp_exp _ (Ite _ _ _) ?a => apply TIte with (w := 1)
         | |- hastyp_exp _ (UnOp _ _) _ => apply TUnOp
         | |- hastyp_exp _ (Unknown _) _ => apply TUnknown
         | |- hastyp_exp _ (Word _ _) _ => apply TWord
         | |- hastyp_exp _ (Load _ _ _ _) _ => apply TLoad with (w := 32)
         | |- hastyp_exp _ (Store _ _ _ _ _) _ => apply TStore with (w := 32)
         | X: hastyp_exp _ ?x ?a, Y: hastyp_exp _ ?y ?b |- hastyp_exp _ (Concat ?x ?y) _ => apply TConcat with (w1 := a) (w2 := b)
         | |- pfsub ftoytypctx ftoytypctx  => reflexivity
         | |- _ < _ => reflexivity
         | |- _ _ = Some _ => reflexivity
         | |- _ _ = Some 32 => eapply decode_reg_32bit; eassumption
         | H: decode_reg _ = Some ?t |- _ ?t = Some (sizeof ?t) => eapply decode_reg_sizeof; eassumption
         | H: decode_reg _ = Some ?t,
           H2: decode_reg _ = Some ?t2 |- _ ?t = Some (sizeof ?t2) => eapply decode_reg_sizeof2; eassumption
         | |- hastyp_exp _ (Cast _ _ (Word ?x ?width)) _ => unfold_rec x;
             apply TCast with (w := width); try apply xbits_bound; try lia
         end.
Local Ltac etypn size :=
  match goal with
  | |- hastyp_exp _ (BinOp _ _ _) _ => apply TBinOp with (w := size)
  | |- hastyp_exp _ (Cast _ _ _) _ => apply TCast with (w := size)
  | |- hastyp_exp _ (Extract _ _ _) _ => apply TExtract with (w := size)
  | |- _ <= _ => easy
  | |- _ < _ => reflexivity
  end.
Local Ltac etyps size := repeat (etyp + etypn size).
Local Ltac stypc c :=
  cbn; repeat match goal with
         | |- hastyp_stmt _ _ (Seq _ _) _ => apply TSeq with (c1 := c) (c2 := c)
         | |- hastyp_stmt _ _ (If _ _ _) _ => apply TIf with (c2 := c)
         | |- hastyp_stmt _ _ (Exn _) _ => apply TExn
         | |- hastyp_stmt _ _ (Rep _ _) _ => eapply TRep with (w:=32) (c':=c)
         | |- hastyp_stmt _ _ Nop _ => apply TNop
         | |- hastyp_stmt _ _ (Jmp _) _ => apply TJmp with (w := 32)
         (*| |- hastyp_stmt _ _ (Move temp0 _) _ => apply TMove with (w := 32)*)
         (*| H: decode_reg _ = Some ?v |- hastyp_stmt _ _ (Move ?v _) _ => apply TMove with (w := 32);*)
         (*     [> right | | apply update_some]; try reflexivity*)
         | |- hastyp_stmt _ _ (Move ?v _) _ => apply TMove with (w := sizeof v); [> right | | apply update_some]; try reflexivity
         | |- pfsub ftoytypctx ftoytypctx  => reflexivity
         | |- hastyp_exp _ _ _  => etyp
  end.
Local Ltac styp := stypc ftoytypctx.
Local Ltac unfold_stmt := match goal with | |- hastyp_stmt _ _ ?a _ => unfold_rec a end.
Local Ltac stypu :=
  repeat match goal with
         | [ |- hastyp_stmt _ _ ?a _ ] => unfold_rec a
         | _ => styp
         end.

Theorem welltyped_lift_insn :
  forall n i q, decode_insn n = Some i -> lift_insn i = Some q -> exists c'', hastyp_stmt ftoytypctx ftoytypctx q c''.
Proof.
  unfold lift_insn, decode_insn; intros z i q DECODE LIFT; remember (opcode _) as n eqn:Heqn; clear Heqn.
  destruct n as [|n]; repeat (discriminate || destruct n as [n|n|]);
    try unfold def in DECODE; repeat mdestruct in DECODE; try solve[inversion DECODE];
    inversion DECODE; subst; unfold def in LIFT.
    all: try destruct if in LIFT; inversion LIFT; try subst.

    (*all: try solve [apply typchk_stmt_compute; cbn; erewrite? decode_reg_32bit; try eassumption; timeout 2 vm_compute; exact I].*)
    eexists. stypu; try (etyp || reflexivity).
    eexists. stypu; try (etyp || reflexivity).
    eexists. stypu; try (etyp || reflexivity); try (apply xbits_bound||lia).
    eexists. stypu; try (etyp || reflexivity). etypn 26; etyp; try (lia || unfold def; etransitivity; try apply xbits_bound; psimpl; lia).
    eexists. stypu;[apply xbits_bound|reflexivity].
    eexists. stypu;[lia|reflexivity].
    eexists. stypu; (reflexivity || apply xbits_bound).
    eexists. stypu; try (etyp || reflexivity); try (apply xbits_bound||lia).
    eexists. stypu; try (etyp || reflexivity); try (apply xbits_bound||lia).
    eexists. stypu; try (etyp || reflexivity); try (apply xbits_bound||lia). erewrite (decode_reg_sizeof32 _);[|eassumption]; etyp;[lia|apply xbits_bound].
    eexists. stypu;[lia|reflexivity].
    eexists. stypu. unfold immli. etransitivity. apply xbits_bound. psimpl. lia. reflexivity.


    eexists. stypu; try (etyp || reflexivity).  erewrite decode_reg_sizeof32;[etyp; unfold immli; etransitivity;[apply xbits_bound|psimpl;lia]|eassumption].
    eexists. stypu; try (etyp || reflexivity).  unfold immlsl; etransitivity. apply xbits_bound. psimpl; lia.
    eexists. stypu; try (etyp || reflexivity).  erewrite decode_reg_sizeof32;[etyp; unfold immli; etransitivity;[apply xbits_bound|psimpl;lia]|eassumption].
Qed.

Definition ftoy_prog s a :=
  match a mod 4 with
  | 0 => i <- decode_insn (getmem 32 LittleE 4 (s H_MEM32) a);;
         q <- lift_insn i ;;
        Some (4, q)
  | _ => None
  end.

Theorem welltyped_ftoy_prog :
  welltyped_prog ftoytypctx ftoy_prog.
Proof.
  unfold welltyped_prog; intros;
  destruct (ftoy_prog _ _) eqn:EQ;[|exact I];
  destruct p. unfold ftoy_prog in EQ; destruct (a mod 4); try discriminate.
  destruct (decode_insn _) eqn:EQ2 in EQ; try discriminate.
  inversion EQ; subst; clear EQ.
  eapply welltyped_lift_insn. eassumption.
  destruct (lift_insn _) eqn:EQ3 in H0; inversion H0; subst. assumption.
Qed.

Theorem encode_decode :
  forall n i, encode_insn i = Some n -> decode_insn n = Some i.
Proof.
  intros. unfold encode_insn in H. repeat mdestruct in H; try discriminate.
  destruct asm_beq eqn:EQ. apply internal_asm_dec_bl in EQ; subst a. inversion H; subst n0.
  rewrite E0. reflexivity.
  discriminate.
Qed.
