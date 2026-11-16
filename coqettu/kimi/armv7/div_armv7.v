(* Automatically generated with pcode2coq
arch: armv7
file: ld-musl-armhf.so.1
SHA256: 30ad527c462b535e1b83932f70f1b6f3b00d999f95683fc1c3a877d0ac8e779e
function: div
*)

Require Import Picinae_armv7.
Require Import NArith.
Require Import Picinae_numbers.
Require Import Lia.
Open Scope N.

Definition div_armv7 : program := fun _ a => match a with

(* 0x0005a5b8: push {r4,lr} *)
(*     370104: push {r4,lr} *)
| 0x5a5b8 => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_LR)) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_MINUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var R_MULT_ADDR) (Cast CAST_UNSIGNED 32 (Var R_R4)) LittleE 4) $;
	Move R_SP (Var R_MULT_ADDR)
)

(* 0x0005a5ba: mov r4,r0 *)
(*     370106: mov r4,r0 *)
| 0x5a5ba => Some (2,
	Move R_R4 (Var R_R0)
)

(* 0x0005a5bc: mov r0,r1 *)
(*     370108: mov r0,r1 *)
| 0x5a5bc => Some (2,
	Move R_R0 (Var R_R1)
)

(* 0x0005a5be: mov r1,r2 *)
(*     370110: mov r1,r2 *)
| 0x5a5be => Some (2,
	Move R_R1 (Var R_R2)
)

(* 0x0005a5c0: bl 0x000306fc *)
(*     370112: bl 0x000306fc *)
| 0x5a5c0 => Some (4,
	Move R_LR (BinOp OP_OR (Word 0x5a5c4 32) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (Word 0x1 8)) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Jmp (Word 0x306fc 32)
)

(* 0x0005a5c4: str r0,[r4,#0x0] *)
(*     370116: str r0,[r4,#0x0] *)
| 0x5a5c4 => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R4) (Word 0x0 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2680)) (Cast CAST_UNSIGNED 32 (Var R_R0)) LittleE 4)
)

(* 0x0005a5c6: str r1,[r4,#0x4] *)
(*     370118: str r1,[r4,#0x4] *)
| 0x5a5c6 => Some (2,
	Move (V_TEMP 0xa2680) (BinOp OP_PLUS (Var R_R4) (Word 0x4 32)) $;
	Move V_MEM32 (Store (Var V_MEM32) (Var (V_TEMP 0xa2680)) (Cast CAST_UNSIGNED 32 (Var R_R1)) LittleE 4)
)

(* 0x0005a5c8: mov r0,r4 *)
(*     370120: mov r0,r4 *)
| 0x5a5c8 => Some (2,
	Move R_R0 (Var R_R4)
)

(* 0x0005a5ca: pop {r4,pc} *)
(*     370122: pop {r4,pc} *)
| 0x5a5ca => Some (2,
	Move R_MULT_ADDR (Var R_SP) $;
	Move R_R4 (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_PC (Load (Var V_MEM32) (Var R_MULT_ADDR) LittleE 4) $;
	Move R_MULT_ADDR (BinOp OP_PLUS (Var R_MULT_ADDR) (Word 0x4 32)) $;
	Move R_SP (Var R_MULT_ADDR) $;
	Move (V_TEMP 0x0) (BinOp OP_AND (Var R_PC) (Word 0x1 32)) $;
	Move R_T (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x0)) (Word 0x0 32))) $;
	Move R_T (Cast CAST_LOW 1 (Cast CAST_UNSIGNED 8 (Var R_T))) $;
	Nop (* Unmodeled Op: CALLOTHER *) $;
	Move R_PC (BinOp OP_AND (Var R_PC) (Word 0xfffffffe 32)) $;
	Jmp (Var R_PC)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog arm7typctx div_armv7.
Proof. Picinae_typecheck. Qed.
