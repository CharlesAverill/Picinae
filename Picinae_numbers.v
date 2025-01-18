(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2024 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
   Number formatting:                                MMMMMMMMMMMZMDMD77$.ZMZMM78
   * configures numeral formatting.                   MMMMMMMMMMMMMMMMMMMZOMMM+Z
                                                       MMMMMMMMMMMMMMMMM^NZMMN+Z
                                                        MMMMMMMMMMMMMMM/.$MZM8O+
                                                         MMMMMMMMMMMMMM7..$MNDM+
                                                          MMDMMMMMMMMMZ7..$DM$77
                                                           MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
                                                             MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
                                                               ZMMMMMMMM.$MM8$MN
                                                               $ZMMMMMMZ..MMMOMZ
                                                                ?MMMMMM7..MNN7$M
                                                                 ?MMMMMZ..MZM$ZZ
                                                                  ?$MMMZ7.ZZM7DZ
                                                                    7MMM$.7MDOD7
                                                                     7MMM.7M77ZZ
                                                                      $MM78ZDZ7Z
                                                                        MM8D$7Z7
                                                                        MM7O$$+Z
                                                                         M 7N8ZD
 *)

Require Import Coq.NArith.NArith.
Require Import Coq.Init.Hexadecimal.

Open Scope N_scope.

Fixpoint add_leading_zeroes (count : nat) (n : uint) : uint :=
  match count with
  | O => n
  | S n' => add_leading_zeroes n' (D0 n)
  end.

Fixpoint length (n : uint) : nat :=
  match n with
  | Nil => 0
  | D0 (n') | D1 (n') | D2 (n') | D3 (n') | D4 (n') | D5 (n') | D6 (n') | D7 (n')
  | D8 (n') | D9 (n') | Da (n') | Db (n') | Dc (n') | Dd (n') | De (n') | Df (n')
      => S (length n')
  end.

Definition format_hex (n : uint) : Number.int :=
  let rem := Nat.modulo (length n) 4 in
  let formatted :=
    if Nat.eqb rem 0
      then n
      else add_leading_zeroes rem n
    in
  Number.IntHexadecimal (Pos formatted).

Definition picinae_to_int (n : N) : Number.int :=
  if n <? 0x00000100
    then N.to_num_int n
    else format_hex (N.to_hex_uint n).

Number Notation N N.of_num_int picinae_to_int : N_scope.
