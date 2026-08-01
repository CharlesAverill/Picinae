Require Import Picinae_toyisa.
Require Import NArith.
Open Scope N.
Import TOYNotations.

Inductive asm : Set :=
  | add (rd rs rt:N)
  | lsl (rd rs imm:N)
  | li (rd imm:N)
  | call (rs:N)
  | ret
  | bi (simm:N)
  | br (rs:N).

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

Section Decode.
  Variable n:N.
(*  31  30  29  28  27  26  25  24  23  22  21  20  19  18  17  16  15  14  13  12  11  10   9   8   7   6   5   4   3   2   1   0
    |-  opcode      -|  |-  rd  -|  |-  rs  -|  |-  rt  -|
    |-  opcode      -|  |-  rd  -|  |-  rs  -|  |-  imm lsl         -|
    |-  opcode      -|  |-  rd  -|  |-  imm li                                                                                      -| *)
  Definition rd := xbits n 24 27.
  Definition rs := xbits n 21 24.
  Definition rt := xbits n 18 21.
  Definition immlsl := xbits n 15 21.
  Definition immli := xbits n 0 24.
  Definition simmbi := xbits n 0 27.


Definition decode_add :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Rt <- decode_reg rt;;
  Some (Move Rd (BinOp OP_PLUS (Var Rs) (Var Rt))).

Definition decode_lsl :=
  Rd <- decode_reg rd;;
  Rs <- decode_reg rs;;
  Some (Move Rd (BinOp OP_LSHIFT (Var Rs) (Word immlsl 32))).

Definition decode_li :=
  Rd <- decode_reg rd;;
  Some (Move Rd (Word immli 32)).

Definition decode_call :option stmt :=
  Rs <- decode_reg rs ;;
  Some
    (Seq (Move V_MEM32 (Store (Var V_MEM32) (Var R_SP) (Var R_PC) LittleE 4))
    (Seq (Move R_SP (BinOp OP_MINUS (Var R_PC) (Word 4 32)))
        (Jmp (Var Rs)))).

Definition decode_ret :=
  Some
   (Seq (Move R_PC (Load (Var V_MEM32) (BinOp OP_PLUS (Var R_SP) (Word 4 32)) LittleE 4))
   (Seq (Move R_SP (BinOp OP_PLUS (Var R_SP) (Word 4 32)))
        (Jmp (Var R_PC)))).

Definition decode_bi :=
  Some
    (Seq (Move R_PC (BinOp OP_LSHIFT (Cast CAST_SIGNED 32 (Word simmbi 27)) (Word 2 32)))
         (Jmp (Var R_PC))).

Definition decode_br :=
  Rs <- decode_reg rs ;;
  Some (Jmp (Var Rs)).

Definition lift_insn :=
  match n with
  | 0 => decode_add
  | 1 => decode_lsl
  | 2 => decode_li
  | 3 => decode_call
  | 4 => decode_ret
  | 5 => decode_bi
  | 6 => decode_br
  | _ => None
  end.

End Decode.

Theorem welltyped_lift_insn :
  forall n q, lift_insn n = Some q -> exists c'', hastyp_stmt toytypctx toytypctx q c''.
Proof.
  unfold lift_insn; intros;
  destruct n as [|n]; repeat (discriminate || destruct n as [n|n|]); cbn in H; inversion H; subst q; clear H;
  try (apply typchk_stmt_compute; vm_compute; exact I).
Qed.

Definition toy_prog s a :=
  match a mod 4 with
  | 0 => q <- lift_insn (getmem 32 LittleE 4 (s V_MEM32) a);;
        Some (4, q)
  | _ => None
  end.

Theorem welltyped_toy_prog :
  welltyped_prog toytypctx toy_prog.
Proof.
  unfold welltyped_prog; intros;
  destruct (toy_prog _ _) eqn:EQ;[|exact I];
  destruct p. unfold toy_prog in EQ; destruct (a mod 4); try discriminate.
  destruct (lift_insn _) eqn:EQ2 in EQ; try discriminate.
  inversion EQ; subst; clear EQ.
  eapply welltyped_lift_insn. eassumption.
Qed.

