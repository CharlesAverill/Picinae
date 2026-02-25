(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2025 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
                                                     MMMMMMMMMMMZMDMD77$.ZMZMM78
                                                      MMMMMMMMMMMMMMMMMMMZOMMM+Z
   Support code for instantiating Picinae to           MMMMMMMMMMMMMMMMM^NZMMN+Z
   various particular Instruction Set Architectures.    MMMMMMMMMMMMMMM/.$MZM8O+
                                                         MMMMMMMMMMMMMM7..$MNDM+
   To compile this module, first load and compile:        MMDMMMMMMMMMZ7..$DM$77
   * Picinae_core                                          MMMMMMM+MMMZ7..7ZM~++
                                                            MMMMMMMMMMM7..ZNOOMZ
                                                             MMMMMMMMMM$.$MOMO=7
                                                              MDMMMMMMMO.7MDM7M+
   Then compile this module with menu option                   ZMMMMMMMM.$MM8$MN
   Compile->Compile_buffer.                                    $ZMMMMMMZ..MMMOMZ
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

Require Import Picinae_core.
Require Import Picinae_theory.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Import Picinae_simplifier_base.
Require Import NArith.
Require Import Program.Equality.
Require Import Structures.Equalities.
Require Import Picinae_ISA.
Open Scope N.

Module Type PICINAE_SMC.
  Parameter asm : Set.
  Parameter insn_length : asm -> N.
  Parameter assemble_insn : asm -> N.
End PICINAE_SMC.

Require Import String.
Require Import Ascii.
Require Import Recdef.
Require Import Program.
Require Import Lia.

Open Scope string.
Open Scope N.

Module Picinae_SMC (IL: PICINAE_IL)  (PSIMPL:PSIMPL_BASE IL)
  (TIL: PICINAE_THEORY IL)
  (SIL: PICINAE_STATICS IL TIL)
  (FIL: PICINAE_FINTERP IL TIL SIL)
  (SMC: PICINAE_SMC).
Module ISA := Picinae_ISA IL PSIMPL TIL SIL FIL.

Import IL.
Import SMC.
Import PSIMPL.
Import TIL.
Export ISA.

Definition code_length (code:list asm) : N :=
  List.fold_left N.add (List.map insn_length code) 0%N.

(* Will we ever need to pass the instruction address to the assemble_insn function? *)
Fixpoint assemble' (b mem:N) (code:list asm) : N :=
  match code with
  | nil => mem
  | insn :: t => assemble' (b+insn_length insn) (setmem 32 LittleE (insn_length insn) mem b (assemble_insn insn)) t
  end.

Definition assemble b code := assemble' b 0%N code.

Definition newline :string := String "010" EmptyString.

Program Fixpoint N2str_impl (n:N) (acc:string) {measure (N.to_nat n)}: string :=
  (match n with
    | 0%N => String "0" acc
    | 1%N => String "1" acc
    | 2%N => String "2" acc
    | 3%N => String "3" acc
    | 4%N => String "4" acc
    | 5%N => String "5" acc
    | 6%N => String "6" acc
    | 7%N => String "7" acc
    | 8%N => String "8" acc
    | 9%N => String "9" acc
    | _ => N2str_impl (n/10)
       (String (match (n mod 10)%N with
         | 0%N => "0"
         | 1%N => "1"
         | 2%N => "2"
         | 3%N => "3"
         | 4%N => "4"
         | 5%N => "5"
         | 6%N => "6"
         | 7%N => "7"
         | 8%N => "8"
         | 9%N => "9"
         | _ => "!"
       end) acc)
  end)%nat .
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.
Next Obligation. lia. Defined.

Definition N2str n := N2str_impl n "".

(* All ways of converting numbers to Rocq strings require using "to_nat" which blows up
   the computation process, severely limiting the magnitude of numbers Rocq can convert
   to strings within its TCB.  Thus `Compute N2str assemble base code.` freezes until it
   runs out of memory or the user gets bored. Either way we cannot pring a string containing
   the numeric expression of the code, so we compute the expression and return it as an
   element in the tuple for Rocq's to convert to a string outside of the trusted kernel. *)
Definition endian2str e :=
  match e with
  | LittleE => "LittleE"
  | BigE => "BigE"
  end.

Definition print_code_prop (w:bitwidth) e (vmem:string) (code:list asm) (base_addr:N) (name:string) :=
  ("Definition " ++ name ++ " (s:store) : Prop :=" ++ newline ++
    " getmem " ++ (N2str w) ++ " " ++ (endian2str e) ++ " " ++
    (N2str ((code_length code))) ++ " (s " ++ vmem ++ ") " ++ (N2str base_addr) ++ " = " ++
  "XXXX" ++ ".",
  (assemble 0 code)).

(* We use an xbits implementation instead of getmem because each bit corresponds to a byte,
   using getmem means we cannot set individual bytes to be executable/not executable, our
   finest granularity with getmem/setmem would be 8 bytes at a time.  Do we need byte-level
   granularity?  Unsure. *)
Definition print_exec_prop (code:list asm) (base_addr:N) (name:string) :=
  ("Definition " ++ name ++ "_aexec (mem:N) : Prop :=" ++ newline ++
  "  xbits mem " ++ (N2str base_addr) ++ " " ++
  (N2str (base_addr + (code_length code))) ++ " = " ++
  "XXXX" ++ "." ++ newline
  , N.ones (code_length code) ).

Ltac unfold_store_props :=
  repeat match goal with
  | [P: ?prop (?s _) |- _ ] => match type of s with store => unfold prop in P end
  end.

Ltac unfold_prog_hook := idtac "You need to override this Ltac with an ltac unfolding the definition(s) of your memory-decoding program function.";
  idtac "E.g., `Ltac unfold_prog_hook ::= unfold p32_prog, p32_stmt."; fail.

(* This hook changes which simplifier reduces the effinv expression in
   effinv_none_hook.  vm_compute may produce incomprehensible results (when?)
   that prevent downstream machinery from terminating.  Psimpl may change the
   context an evar is in resulting in the inability to unify it with the necessary
   terms.  In either case, both tactics block execution so this hook is a workaround.
   The ideal case is psimpl handles all the simplification we need without
   preventing evar unification.

   The compromise is to selectively psimpl the left-hand side if the goal is an equality,
   otherwise just psimpl.

   But psimpl is a specialty simplifier and will not simplify goals such as the following:

      (if
          match arm_decode (BinInt.Z.of_N 3800043520) with
          | ARM_UNPREDICTABLE | idk => None
          | _ => Some (4, arm2il base (arm_decode (BinInt.Z.of_N 3800043520)))
          end
          then None
          else Some (mem_unchanged s0 s /\ inp = inp /\ 0 = 0 /\ 0 = 0 /\ 0 = 0)) =
      None
*)
Ltac psimpl_lhs := match goal with
                   | |- ?lhs = _ => psimpl lhs
                   | |- _ => psimpl
                   end.
Ltac invs_simpl_hook := psimpl_lhs.


Ltac reduce_frames :=
  repeat match goal with
         | |- context[update ?s _ _ ?m] => rewrite (update_frame s _ _ m);[|easy]
         end.

(* TODO: this does more than rewrite variables read from the store. For example,
   it will rewrite using the hypothesis `H: base mod 4 = 0`.  This is unexpected,
   but useful where I saw it. *)
Ltac rewrite_vars :=
  repeat match goal with
  | [S: store, H: ?S ?v = _ |- context[?S ?v]] => rewrite H in *
  end.

Ltac reduce_getmem_hyp :=
  match goal with
  | MEM: getmem _ _ _ ?m _ = _ |- context[getbyte ?m _ _] =>
      erewrite (getmem_byte MEM); try lia; psimpl_lhs
  end.

(* Solves simple existentially quantified sums. E.g., `4 = 1 + ?i`. *)
Ltac solve_sum :=
  match goal with |- ?n = 1 + _ => replace n with (1+(n-1)) by lia; simpl N.sub; reflexivity end.

Ltac reduce_getmem x :=
  lazymatch x with
  |  getmem _ _ _ _ _ =>
    let H := fresh "H" in
    eassert (H: x = _);[
        reduce_frames;
        try rewrite update_updated;
        repeat (erewrite getmem_first;[
          (* Make progress removing non-overlapping memory writes,
             or if it does overlap then interpret the byte from it. *)
          repeat match goal with
                | |- context[getbyte (setmem ?w _ ?len _ ?a ?v) ?b ?w] =>
                    first [
                      rewrite getbyte_noverlap;[|apply noverlap_sum; psimpl_lhs; lia]
                    | let i := constr:(b - a) in
                        replace b with (a + i) by lia;
                        rewrite setmem_byte;[|lia|lia]
                    ]
                end;
          try reduce_getmem_hyp

      | solve_sum ]);
      rewrite getmem_0;
      (*  At this point the goal is `byte_1 .| byte_2 .| ... .| 0 = ?Goal`
          We need to use psimpl on the left hand side only, otherwise it
          might instantiate the evar ?Goal to 0 or render some variable out
          of the evar's scope. *)
      psimpl_lhs; reflexivity
  |];
(* Do not put the `rewrite H` inside of the [|] tactical to force evar instantiation before use. *)
  rewrite H in *; clear H
  | _ => idtac "Input was not a getmem call."; fail
  end.

Ltac reduce_testbitmem x H :=
  let htyp := type of H in
  lazymatch ltac:(constr:((htyp, x))) with
  | (xbits ?b ?l ?h = ?mem, N.testbit ?v ?i) =>
    let HELP := fresh "H" in
    assert (HELP: l <= i /\ i <= h) by (split; lia); clear HELP;
    rewrite testbit_xbits, (xbits_split2 l i (N.succ i) h v mem);
    try lia; vm_compute (N.odd _)
  end.

Ltac unfold_h x :=
    match x with
    | ?h => unfold h
    | ?h _ => unfold h
    | ?h _ _ => unfold h
    | ?h _ _ _ => unfold h
    | ?h _ _ _ _ => unfold h
    | ?h _ _ _ _ _ => unfold h
    | ?h _ _ _ _ _ _ => unfold h
    | ?h _ _ _ _ _ _ _ => unfold h
    | ?h _ _ _ _ _ _ _ _ => unfold h
    | ?h _ _ _ _ _ _ _ _ _ => unfold h
    | ?h _ _ _ _ _ _ _ _ _ _ => unfold h
    | _ => idtac "Failed to unfold, function has too many arguments!"; fail
    end.

Ltac unfold_h_in x H :=
    match x with
    | ?h => unfold h in H
    | ?h _ => unfold h in H
    | ?h _ _ => unfold h in H
    | ?h _ _ _ => unfold h in H
    | ?h _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ _ _ _ _ => unfold h in H
    | ?h _ _ _ _ _ _ _ _ _ _ => unfold h in H
    | _ => idtac "Failed to unfold, function has too many arguments!"; fail
    end.


(* Expects goal to be `effinv ...` *)
Ltac unfold_invs_exit :=
  match goal with
  |- effinv _ _ ?invs  ?exit _ = _ => unfold_h invs; unfold_h exit
  end.

(* Try to reduce `a mod n` to 0...n-1.  Called *)
Ltac solve_mod_rec a n i :=
  let H := fresh "H" in
  let iN := eval cbv in (N.of_nat i) in
  first [
    assert (H: a mod n = iN) by lia; rewrite H in *; clear H
  | assert (H: iN < n) by lia; clear H; solve_mod_rec a n (S i)
  ].

Ltac solve_mod a n :=
  let H := fresh "H" in
  assert (H: n < 256) by lia; clear H;
  solve_mod_rec a n O%nat.

Ltac reduce_comps :=
  repeat match goal with
  | |- context [?x =? ?y] =>
      replace (x =? y) with true by lia
  | |- context [?x =? ?y] =>
      replace (x =? y) with false by lia
  | |- context [?x <? ?y] =>
      replace (x <? y) with true by lia
  | |- context [?x <? ?y] =>
      replace (x <? y) with false by lia
  end.

Ltac reduce_comps_in H :=
  repeat match type of H with
  | context [?x =? ?y] => idtac x y;
      replace (x =? y) with true in H by lia
  | context [?x =? ?y] => idtac x y;
      replace (x =? y) with false in H by lia
  | context [?x <? ?y] =>
      replace (x <? y) with true in H by lia
  | context [?x <? ?y] =>
      replace (x <? y) with false in H by lia
  end.

(* These hooks are used in ISA_invseek to simplify the memory program
   instruction expression which, for an interpreted language like this
   one, is read as bytes from memory then decoded. *)
Global Ltac effinv_none_hook ::=
  start ltac profiling;
  try unfold_invs_exit;
  unfold effinv, effinv';
  unfold_prog_hook;
  unfold_store_props;
  reduce_frames;
  repeat match goal with |- context[?a mod ?n] => solve_mod a n end;
  rewrite_vars;
  (* Reduce the comparisons used in variable-location code. *)
  reduce_comps;
  (* Reduce permission bit tests. *)
  repeat match goal with
         | H: xbits ?v _ _ = _ |- context[N.testbit ?v ?m] => reduce_testbitmem (N.testbit v m) H
         end;
  (* Reduce memory reads. *)
  repeat  match goal with
          | MEM: getmem _ _ _ _ _ = _ |- context[getmem ?w ?e ?len ?m ?a] =>
              reduce_getmem (getmem w e len m a)
          end;
  (* When do we want to reduce with vm_compute rather than psimpl? *)
  first [invs_simpl_hook | idtac];
  stop ltac profiling.

(* Original version had a different ltac for decoding instructions, but the arm7 architecture
   shows that some architectures require decoding instructions to tell if the program effectively
   exited. So now effinv_none_hook includes the decoding machinery as well and `psa_some_hook`
   is redundant by default but available for fine tuning the machinery. *)
Ltac psa_some_hook ::=
  effinv_none_hook;
  repeat (rewrite N.mod_small by lia);
  cbn -[N.add]; (* This computes the term without expanding program counters expressed as
                  offsets from a variable base address, e.g., `base + 8`. *)
  show_goal.

Ltac prep_precondition PRE :=
  match type of PRE with
  | true_inv (get_precondition _ ?invs ?exits _ _ _) => unfold_h_in invs PRE; unfold_h_in exits PRE
  end;
  unfold true_inv, get_precondition in PRE;
  reduce_comps_in PRE.

End Picinae_SMC.
