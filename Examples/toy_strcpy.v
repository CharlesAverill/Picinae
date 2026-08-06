Require Import Picinae_toyisa Picinae_toyisa_interpreter.
Require Import List NArith Bool ZArith.
Open Scope N.
Import ListNotations.
Import TOYNotations.

Definition nop := lsl R_1 R_1 0.

(* R_0 : (input) destination pointer
   R_1 : (input) source pointer
   R_2 : (clobbered) 1
   R_3 : (clobbered) character
   clobber R_2 and R_3. *)
Definition strcpy_listing := [
  li R_2 1;       (* ; store value to increment *)
  ldr R_3 R_1 0;  (* ; fetch character to R_3 *)
  str R_0 R_3 0;  (* ; store character to destination *)
  cmp R_3 0;      (* ; test for null terminator *)
  cbeq (ofZ 27 4%Z);
  add R_0 R_0 R_2;
  add R_1 R_1 R_2;
  bi (ofZ 27 (-6)%Z);
  ret
].

Definition call_strcpy (strcpy_base:addr) :=
  if strcpy_base <? 2^24 then
    Some [
      (* R_1 (source pointer) set above (in hypotheses) *)
      lsl R_0 R_SP 0;  (* set destination to buffer on stack. *)
      li R_2 (ofZ 24 (-16)%Z); (* load buffer size into register. *)
      add R_SP R_SP R_2; (* 16-byte buffer on stack pointed at by R_0 *)
      li R_2 strcpy_base;
      call R_2;
      (* Now just do some stuff *)
      li R_2 0;
      li R_3 0;
      li R_4 0;
      li R_5 0
    ]
  else None.

Compute ls <- call_strcpy 0x1000 ;; assemble ls.
Compute assemble strcpy_listing.

(* R_0 : (input) destination pointer
   R_1 : (input) source pointer
   R_2 : (clobbered) 1
   R_3 : (clobbered) character
   clobber R_2 and R_3. *)
Definition strcpy_listing' := [
  li R_2 1;       (* ; store value to increment *)
  nop; nop;
  ldr R_3 R_1 0;  (* ; fetch character to R_3 *)
  nop; nop; nop; nop;
  str R_0 R_3 0;  (* ; store character to destination *)
  nop;
  cmp R_3 0;      (* ; test for null terminator *)
  cbeq (ofZ 27 10%Z);
  nop; nop;
  add R_0 R_0 R_2;
  nop;
  add R_1 R_1 R_2;
  nop; nop; nop;
  bi (ofZ 27 (-17)%Z);
  ret
].

Definition call_strcpy' (strcpy_base:addr) :=
  if strcpy_base <? 2^24 then
    Some [
      (* R_1 (source pointer) set above (in hypotheses) *)
      lsl R_0 R_SP 0;  (* set destination to buffer on stack. *)
      nop;
      li R_2 (ofZ 24 (-16)%Z); (* load buffer size into register. *)
      nop; nop; nop; nop;
      add R_SP R_SP R_2; (* 16-byte buffer on stack pointed at by R_0 *)
      nop; nop;
      li R_2 strcpy_base;
      nop;
      call R_2;
      (* Now just do some stuff *)
      li R_2 0;
      nop; nop;
      li R_3 0;
      nop; nop;
      li R_4 0;
      nop; nop;
      li R_5 0
    ]
  else None.

Compute ls <- call_strcpy' 0x1000 ;; assemble ls.
Compute assemble strcpy_listing'.

