(** * Foundation *)

(* ################################################################# *)
(** * Introduction *)

(** In this chapter we take a look at the data structures and abstractions that are the foundation of Picinae.
    This will clarify the meaning and structure of the expressions and statements we've seen that represent the instructions of programs,
    the meaning of well-typed programs, how programs transition between states, and how Picinae organises its Modules.
    If you only need a working knowledge of Picinae to read and write deductive proofs you can safely skip this chapter.
    If you need to develop low-level tools for Picinae, whether within Rocq or external to it, then this chapter is a useful guide and reference.


    The first tidbit of this chapter builds a small architecture.
    Then we introduce the Picinae's intermediate language for representing the effects of instructrions, which is comprised of expressions and statements.
    We cover expressions first---their syntax, semantics and well-typedness property.
    Then we do the same for statements.
    Penultimately we cover the strucures of representations of Picinae programs.
    Finally we'll show step-by-step how to build a Picinae ISA and which steps are copy-paste and which require thinking.

    This material covers the files Picinae_core and Picinae_statics.
    The typedness of expressions and statements comes from Picinae_statics and the rest from core. *)

(* ################################################################# *)
(** * Setting It Up *)

Require Export Picinae_core.
Require Import NArith.
Require Import Structures.Equalities.

Open Scope N.

(* ================================================================= *)
(** ** A Small Architecture Specification *)

(** Each Picinae instantiation takes a machine architecture as input, expressed as
    a module that defines a type "var" for IL variables, a typing context "typctx"
    that defines the type of each IL variable, and the CPU's memory access model 
    expressed as propositions mem_readable and mem_writable that are satisfied 
    when an address is readable/writable in the context of a given store. *)
Module Type Architecture.
  Declare Module Var : UsualDecidableType.
  Definition var := Var.t.
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.

  Parameter archtyps : typctx.
  Parameter mem_readable: store -> addr -> Prop.
  Parameter mem_writable: store -> addr -> Prop.
End Architecture.

(** We begin by copying the architecture from the _Basics_ chapter where we explained
    that a64var enumerates the hardware register and memory, and a64typctx
    assigns each of them a bit-width.  For exposition we'll add two flags, [F_W] and [F_R],
    specifying whether memory can be written to and read from respectively. *)
Inductive a64var :=
  | V_MEM
  | R_R0 | R_R1 | R_R2
  | F_W  | F_R.

Definition a64typctx (id:a64var) : option N :=
  match id with
  | V_MEM => Some (8*2^64)
  | R_R0 | R_R1 | R_R2 => Some (64)
  | F_W  | F_R => Some (1)
  end.

(** At this point some readers might be thinking "Why does the type context
    return an option?"  Well, it's to ease the translation of instruction semantics
    from lifters such as Ghidra which use temporary registers that don't
    exist on the hardware to store intermediate values in the computation
    of an instruction.  The primary way we lift binaries to Picinae is via translating
    the output of these disassemblers.  This translator forms the bulk of our trusted
    computing base, so we go to extra efforts to make it as simple as possible.
    We'll see later in this chapter how we account for these "temp" registers in our
    instruction semantics. *)

(** With [a64var] and [a64typctx] specified, we're almost ready to create our first Architecture.
    First we'll need to create UsualDecidableType module out of a64var. 
    This is the standard module for encapsulating a type with its decision procedure,
    provided by [Structures.Equalities] in Rocq's standard library. *)

Module MiniA64VarEq <: MiniDecidableType.
  Definition t := a64var.
  (** This definition of eq_dec uses proof-automation to synthesize the decision
      procedure function.  
      <TODO: wording for this sentence:>
      This is a clever trick enabled by the Curry-Howard isomorphism at Rocq's foundation
      which treats proofs as terms of a type. To see the proof-term, equivalently the decision
      procedure, execute [Print eq_dec.] after it's defined within the module, or [Print MiniA64VarEq.eq_dec.]
      after closing the module. *)
  Definition eq_dec (v1 v2:a64var) : {v1=v2}+{v1<>v2}.
    decide equality; apply N.eq_dec.
  Defined.
  (** This [Arguments] line simply tells Rocq to never simplify the arguments
      of eq_dec. *)
  Arguments eq_dec v1 v2 : simpl never.
End MiniA64VarEq.

(** Now! We are ready to begin our Architecture module, but there are still two
    more properties to specify. *)

Module A64Arch <: Architecture.
  (** [Make_UDT] is a functor, a module-to-module function, which creates the desired UsualDecidableType module 
      out of our MiniDecidableType module. *)
  Module Var := Make_UDT MiniA64VarEq.
  (** [Var.t] is an alias for [a64var], the type we specified earlier enumerating the hardware elements: registers, flags, and memory. *)
  Definition var := Var.t.
  (** The [store], aka state, machine state, etc, is a function from each hardware element to its bits, represented as a number N. *)
  Definition store := var -> N.
  Definition typctx := var -> option bitwidth.
  Definition archtyps := a64typctx.

  (** To finish our architecture specification we'll define non-trivial memory access propositions.
      Previously we've filled them in with [True] for simplicity.  Now we'll read the permission
      flags, [F_R] and [F_W], we've included in our architecture for exactly this purpose. *)
  Definition mem_readable (s:store) (a:addr) := s F_R = 1.
  Definition mem_writable (s:store) (a:addr) := s F_W = 1.
End A64Arch.

(** **** Exercise: 1 star, standard, optional (16bit_funky_arch)

    Make a 16-bit architecture with four registers and a memory.
    Define memory to be readable iff the 32nd bit in memory is one.
    Define memory to be writable iff the 43rd bit in memory is the opposite of the first bit in any register. *)


(* ================================================================= *)
(** ** The Picinae Expression Language *)

(** We now turn our attention to the expression language Picinae uses to represent computations.
    In Picinae_core this is encapsulated in a module parameterized by an architecture.

    [[
       Module Type PICINAE_CORE (Arch: Architecture).
    ]]

    Here we'll use the architecture we just created and proceed interactively. *)


(* begin details : Setting up some definitions *)
Import A64Arch.
Definition vareq := Var.eq_dec.
Definition vareqb v1 v2 := if vareq v1 v2 then true else false.
#[export] Instance VarEqDec : EqDec var := { iseq := vareq }.
(* end details *)

(** We'll begin by looking at a simple subset of the expression language
    and cover the syntax, semantics, and expression typing. 
 
    Our expressions include unary and binary operations.  These are encoded
    as an operator ([unop_typ] and [binop_typ]) and the one or two sub-expression
    inputs to the operation.  The operators are also a subset of what Picinae supports. 
    For the unary operations we'll only consider bitwise negation ([NOT]); for binary
    operations we'll consider some arithmetic ([PLUS], [MINUS]), bitwise ([AND],[OR],[XOR]),
    and comparison ([EQ],[LT]) operations. *)
Module SimpleExp.

Inductive unop_typ : Set :=
  | OP_NOT : unop_typ.

Inductive binop_typ : Set :=
  (* Arithmetic *)
    OP_PLUS : binop_typ
  | OP_MINUS : binop_typ
  (* Bitwise logic *)
  | OP_AND : binop_typ
  | OP_OR : binop_typ
  | OP_XOR : binop_typ
  (* Comparison *)
  | OP_EQ : binop_typ
  | OP_LT : binop_typ.

(** The semantics of the operations are given separately by their corresponding [eval_] functions.
    For binary operations, the bitwidth of the output is additionally specified by the [widthof_binop] function.
    This allows us to enforce that the result of comparisons is exactly zero or one.
    For unary operations, the bitwidth of the output is the same as the input. *)

Definition eval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : N :=
  match bop with
  | OP_PLUS => (n1+n2) mod 2^w
  | OP_MINUS => msub w n1 n2
  | OP_AND => N.land n1 n2
  | OP_OR => N.lor n1 n2
  | OP_XOR => N.lxor n1 n2
  | OP_EQ => N.b2n (n1 =? n2)
  | OP_LT => N.b2n (n1 <? n2)
  end.

Definition widthof_binop (bop:binop_typ) (w:bitwidth) : bitwidth :=
  match bop with
  | OP_PLUS | OP_MINUS | OP_AND | OP_OR | OP_XOR => w
  | OP_EQ | OP_LT => 1
  end.

Definition eval_unop (uop:unop_typ) (n:N) (w:bitwidth) : N :=
  match uop with
  | OP_NOT => N.lnot n w
  end.

(** Our first look at the expression language includes the operations just shown,
    variables ([Var]), and constants ([Word]).
    Variables are encoded by [Var (v:var)] where var is exactly the type enumerating our hardware elements.
    For example, 

      * [Var R_R0] denotes the value stored in register R0.
      * [Var F_R] denotes the value of the memory-readable permission flag.
      * [Var V_MEM] denotes the value of memory, an 8*2^32-bit number.

    Constants are encoded by [Word (n:N) (w:bitwidth)] where n is the value of the word and w is its bitwidth
    (i.e. how many bits should be used to represent n).
    For example,

      * [Word 0 1] is the 1-bit representation of zero.
      * [Word 0 64] is the 64-bit representation of zero.
      * [Word 1024 8] is the 8-bit representation of 1024, which is physically impossible.

    As demonstrated in the last example, the value of a word can exceed the maximum value representable by its
    bitwidth.  In this case we would say the expression is not well-typed and our well-typedness property would
    not hold.  More on this later. *)

Inductive exp : Type :=
| Var (v:var)
| Word (n:N) (w:bitwidth)
| BinOp (b:binop_typ) (e1 e2:exp)
| UnOp (u:unop_typ) (e:exp).

(** Here are a few example expressions. *)

Definition r0_plus_r1 : exp :=
  BinOp OP_PLUS (Var R_R0) (Var R_R1).

Definition r0_and_r1__plus__not_7 : exp :=
  BinOp OP_PLUS 
    (BinOp OP_AND (Var R_R0) (Var R_R1)) 
    (UnOp OP_NOT (Word 7 32)).

(** **** Exercise: 1 star, standard, optional (zero_expressions)

   Replace `Word x x` below with three different expressions that you think will 
   always evaluate to zero. You are allowed to use each operation at most once. 
   I.e. if you use `OP_AND` in zero_expression1 then you may not use it in
   zero_expression2 nor zero_expression3.
*)

Definition zero_expression1 := (* Fill in here *) Word 1 1.

Definition zero_expression2 := (* Fill in here *) Word 2 2.

Definition zero_expression3 := (* Fill in here *) Word 3 3.

(** *** Picinae expression semantics *)

(** Expression semantics are defined by the inductive proposition [eval_exp].  A proposition of
    the form [eval_exp c s e n w] reads as:

        "given type context c and store s, expression e may evaluate to value n with
        bitwidth w."  

    Each constructor of [eval_exp] corresponds to evaluating one of the constructors of [exp].

    TODO: A deeper explanation of the necessity of including the bitwidth of expressions.
    
    Importantly, each expression has a bitwidth.
    *)

Inductive eval_exp (c:typctx) (s:store): exp -> N -> bitwidth -> Prop :=
| EVar v w (TYP: c v = Some w): eval_exp c s (Var v) (s v) w
| EWord n w: eval_exp c s (Word n w) n w
| EBinOp bop e1 e2 n1 n2 w (E1: eval_exp c s e1 n1 w) (E2: eval_exp c s e2 n2 w):
         eval_exp c s (BinOp bop e1 e2) (eval_binop bop w n1 n2) (widthof_binop bop w)
| EUnOp uop e1 n1 w (E1: eval_exp c s e1 n1 w):
        eval_exp c s (UnOp uop e1) (eval_unop uop n1 w) w.

(** Let's break it down one by one.

[| EVar v w (TYP: c v = Some w): eval_exp c s (Var v) (s v) w]

    [Var v] evaluates to the value stored for v in the store.  The bitwidth
    is taken from the type context.  This latter typing requirement prevents
    temporary variables from being used before they are written to.

[| EWord n w: eval_exp c s (Word n w) n w]

    [Word n w] evaluates to the w-bit valued n.

[| EBinOp bop e1 e2 n1 n2 w (E1: eval_exp c s e1 n1 w) (E2: eval_exp c s e2 n2 w):
         eval_exp c s (BinOp bop e1 e2) (eval_binop bop w n1 n2) (widthof_binop bop w)]

    The evaluation of [BinOp bop e1 e2] requires e1 and e2 to be evaluable expressions
    of the same bitwidth w.  The value of the expression is determined by this bitwidth
    and the values of e1 and e2 and is computed by the [eval_binop] function we outlined above.
    The width is computed by another function we saw above, [widthof_binop], which sets the bitwidth
    to 1 if it is a comparison operation.

[| EUnOp uop e1 n1 w (E1: eval_exp c s e1 n1 w):
        eval_exp c s (UnOp uop e1) (eval_unop uop n1 w) w.]

    Unary operations are just simpler binary operations.  The value of the expression is
    similarly encapsulated in another function, [eval_unop], and the bitwidth is preserved.
    *)


(** **** Exercise: 2 stars, standard, optional (unop_div2)

    Add a unary operation that divides its w-bit argument by two, returning a (w-1)-bit
    value.  You can decide what the resultant bitwidth is for 1-bit and 0-bit values.
    Modify the semantics to take this bitwidth-modifying unary operator into account. *)
Module unop_div2.

  Inductive unop_typ' :=
    | OP_NOT
    | OP_DIV2.

  Inductive exp' : Type :=
  | Var (v:var)
  | Word (n:N) (w:bitwidth)
  | BinOp (b:binop_typ) (e1 e2:exp')
  | UnOp (u:unop_typ') (e:exp').

  Definition eval_unop' (u:unop_typ') (w:bitwidth) (n:N) :=
    match u with
    | OP_NOT => N.lnot n w
    | OP_DIV2 => (* Replace this zero with your definition: *) 0
    end.

  Inductive eval_exp' (c:typctx) (s:store): exp' -> N -> bitwidth -> Prop :=
  | EVar v w (TYP: c v = Some w): eval_exp' c s (Var v) (s v) w
  | EWord n w: eval_exp' c s (Word n w) n w
  | EBinOp bop e1 e2 n1 n2 w (E1: eval_exp' c s e1 n1 w) (E2: eval_exp' c s e2 n2 w):
          eval_exp' c s (BinOp bop e1 e2) (eval_binop bop w n1 n2) (widthof_binop bop w)
  (* Replace the EUnOp constructor with your modified constructor. *)
  | EUnOp uop e1 n1 w (E1: eval_exp' c s e1 n1 w):
          eval_exp' c s (UnOp uop e1) (eval_unop' uop n1 w) w.

End unop_div2.

(** **** Exercise: 2 stars, standard, optional (zero_expressions_correct))

    Prove that your expressions from exercise (zero_expressions) always evaluate to
    zero. *)

Theorem zero_expression_correct1:
  forall c s n w, eval_exp c s zero_expression1 n w -> n = 0.
Proof.
Abort.

Theorem zero_expression_correct2:
  forall c s n w, eval_exp c s zero_expression2 n w -> n = 0.
Proof.
Abort.

Theorem zero_expression_correct3:
  forall c s n w, eval_exp c s zero_expression3 n w -> n = 0.
Proof.
Abort.

(** **** Exercise: 2 stars, standard, optional (simpl_exp_det)

    Prove this simple expression language is deterministic.  In other words, if the
    expression can evaluate to the w-bit value n and the w'-bit value n' then w=w' and n=n'. *)
Theorem simpl_exp_det:
  forall c s expression n w n' w'
    (E:  eval_exp c s expression n w)
    (E': eval_exp c s expression n' w'),
    n = n' /\ w = w'.
Proof.
  intros c s e. induction e; intros.
  - inversion E; inversion E'; subst. rewrite TYP in TYP0; injection TYP0. now split.
  - inversion E; inversion E'; subst. now split.
  - inversion E;  subst. specialize (IHe1 n1 w0). specialize (IHe2 n2 w0).
    inversion E'; subst. specialize (IHe1 n0 w E1 E0). specialize (IHe2 n3 w E2 E3).
    destruct IHe1, IHe2; subst; now split.
  - inversion E; inversion E'; subst. specialize (IHe n1 w n0 w' E1 E0); destruct IHe; subst; now split.
  (* TODO: Again finding myself having trouble with overly-strict IHs when inducting on
     a derivation.
  intros c s e n w n' w' E E'.
  induction E.
  - inversion E'; subst. split; try reflexivity. rewrite TYP in TYP0. now injection TYP0.
  - inversion E'; subst. now split.
  - inversion E'. enough (HELP:n1=n0/\n2=n3/\w=w0). destruct HELP as [HELP1 [HELP2 HELP3]]; subst.
    now split.
    subst. split. *)
Qed.

(** *** Picinae expression type-safety *)

(** Tracking the bitwidths of hardware elements and expressions gives us a
    straight-edge for measuring the soundness of Picinae's trusted computing
    base (TCB), namely the semantics, which we have glimpsed, and the lifting
    mechanism. The semantics come equipped with progress and preservation
    theorems (see Picinae_statics.v), standard theorems in the programming
    language (PL) field for showing that a language is safe.  The lifting
    mechanism, which transforms binary code into its PIL representation, is
    implemented outside of Coq in Python or Ocaml.  This part of our TCB cannot
    be verified in Coq so we need an alternative way to check it is correct.

    The type-safety properties [hastyp_exp] and [hastyp_stmt] say that an
    expression and statement are well-typed respectively.  These properties can
    be proved automatically with the Picinae_typecheck tactic if the term in
    question is well-typed.  If it is not well-typed then we know something is
    wrong with the code and we need to check the lifting mechanism.

    For example, can you see which, if any, statements in the program below have
    a type error?

    <Insert 5 lifted instructions with one of them having an error>

    Running Picinae_typecheck reveals that this program has one line with at
    least one type error by leaving us the goal of proving it is type safe.
    There are two approaches to finding the issue:

      1.  Look at the code thoroughly trying to find the type mismatch.
      2.  Continue the proof interactively to find where it gets stuck.

    <Insert Picinae_typecheck proof environment.>
 *)

(** Let's take a look at the typing rules for our simple expression language... *)

Inductive hastyp_exp (c:typctx): exp -> bitwidth -> Prop :=
  | TVar v w (CV: c v = Some w): hastyp_exp c (Var v) w
  | TWord n w (LT: n < 2^w): hastyp_exp c (Word n w) w
  | TBinOp bop e1 e2 w
          (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w):
          hastyp_exp c (BinOp bop e1 e2) (widthof_binop bop w)
  | TUnOp uop e w (T1: hastyp_exp c e w):
          hastyp_exp c (UnOp uop e) w.

(** ...and break them down one by one.

[| TVar v w (CV: c v = Some w): hastyp_exp c (Var v) w]

    [Var v] has the bitwidth [w] it has in the typctx, which comes from the
    architecture [A64Arch] we defined and imported at the beginning of this chapter.

[| TWord n w (LT: n < 2^w): hastyp_exp c (Word n w) w]

    [Word n w] has the bitwidth [w] if indeed n can be expressed in w bits as
    required by the [LT] parameter.

[| TBinOp bop e1 e2 w
        (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w):
        hastyp_exp c (BinOp bop e1 e2) (widthof_binop bop w)]

    [BinOp bop e1 e2] is only well typed if both of the operands, [e1] and [e2], are themselves
    well-typed and of the same bitwidth, [w].  If so then the bitwidth of the result is determined
    by the widthof_binop function.  This variable bitwidth is necessary for precisely defining
    the bitwidths of comparison functions (e.g. less-than) which are encoded in our language
    as binary operations.

[| TUnOp uop e w (T1: hastyp_exp c e w):
          hastyp_exp c (UnOp uop e) w]

    Like binary operations, the unary operation's typedness requires the operand to be well
    typed with some bitwidth [w].  Unlike binary operations, this bitwidth is also the bitwidth
    of the result because we do not have any unary operators that change the bitwidth.  We could,
    however, extend Picinae with such operators as in exercise (unop_div2).

 *)

(** **** Exercise: 1 stars, standard, optional (simpl_exp_fix)

    Fix these expressions so that they type-check easily.  Try to make
    as few modifications as possible, but do not worry about the semantics.
    Especially for [untyped_exp2] there is no reasonable interpretation
    for the expression given, it is given only for the exercise. *)

Definition untyped_exp1 := Word 64 4.
Definition untyped_exp2 := BinOp OP_AND (Var R_R2) (Var F_W).
Definition untyped_exp3 := BinOp OP_OR (UnOp OP_NOT (Word 127 8)) (Var R_R1).
Definition untyped_exp4 := BinOp OP_EQ
  (BinOp OP_PLUS (Word 1 64) (BinOp OP_LT (Var R_R0) (Word 120 64)))
  (BinOp OP_XOR (BinOp OP_AND (UnOp OP_NOT (Var F_R)) (Var F_W)) (Word 1 64)).

(* Solution: *)
(*
Definition untyped_exp1 := Word 4 64.
Definition untyped_exp2 := BinOp OP_AND (Var F_R) (Var F_W).
Definition untyped_exp3 := BinOp OP_OR (UnOp OP_NOT (Word 127 64)) (Var R_R1).
Definition untyped_exp4 := BinOp OP_EQ
  (BinOp OP_PLUS (Word 1 1) (BinOp OP_LT (Var R_R0) (Word 120 64)))
  (BinOp OP_XOR (BinOp OP_AND (UnOp OP_NOT (Var F_R)) (Var F_W)) (Word 1 1)).
 *)

Require Import Lia.
Ltac rewrite_widthof :=
  match goal with
  | |- hastyp_exp _ (BinOp ?op _ _)  1 =>
      let w' := fresh "w" in
        evar (w':N);
        replace 1 with (widthof_binop op w'); unfold w'; constructor
  | |- hastyp_exp _ (BinOp ?op _ _) ?w => 
        replace w with (widthof_binop op w); constructor
  end.

Theorem untyped_exp1_solved : exists w, hastyp_exp a64typctx untyped_exp1 w.
Proof. eexists; repeat (reflexivity || lia || constructor). Abort.

Theorem untyped_exp2_solved : exists w, hastyp_exp a64typctx untyped_exp2 w.
Proof. eexists; repeat (reflexivity || lia || constructor). Abort.

Theorem untyped_exp3_solved : exists w, hastyp_exp a64typctx untyped_exp3 w.
Proof. eexists; repeat (reflexivity || lia || constructor). Abort.

Theorem untyped_exp4_solved : exists w, hastyp_exp a64typctx untyped_exp4 w.
Proof. eexists; repeat (reflexivity || lia || rewrite_widthof || constructor). Abort.

End SimpleExp.

(** *** Bit-manipulation expressions*)

(** We now expand our simple expression language with the bit-manipulation expressions [Cast],
    [Extract], and [Concat].  In this and the next section we give a whirlwind introduction
    of the rest of Picinae's expression language, its semantics, and its typing rules, as
    most of the commentary is the same. *)
Module BitManipExp.

(* begin details: Set up unary and binary operations... *)
Require Import ZArith.
(* IL binary operators *)
Inductive binop_typ : Type :=
| OP_PLUS (* Integer addition *)
| OP_MINUS (* Subtract second integer from first. *)
| OP_TIMES (* Integer multiplication *)
| OP_DIVIDE (* Unsigned integer division *)
| OP_SDIVIDE (* Signed integer division *)
| OP_MOD (* Unsigned modulus *)
| OP_SMOD (* Signed modulus *)
| OP_LSHIFT (* Left shift *)
| OP_RSHIFT (* Right shift, fill with 0 *)
| OP_ARSHIFT (* Right shift, sign extend *)
| OP_AND (* Bitwise and *)
| OP_OR (* Bitwise or *)
| OP_XOR (* Bitwise xor *)
| OP_EQ (* Equals *)
| OP_NEQ (* Not equals *)
| OP_LT (* Unsigned less than *)
| OP_LE (* Unsigned less than or equal to *)
| OP_SLT (* Signed less than *)
| OP_SLE (* Signed less than or equal to *).

(* IL unary operators *)
Inductive unop_typ : Type :=
| OP_NEG (* Negate (2's complement) *)
| OP_NOT (* Bitwise not *)
| OP_POPCOUNT (* Count 1 bits *)
| OP_BITWIDTH (* Log2 rounded up *).

(* Perform a binary operation. *)
Definition eval_binop (bop:binop_typ) (w:bitwidth) (n1 n2:N) : N :=
  match bop with
  | OP_PLUS => (n1+n2) mod 2^w
  | OP_MINUS => msub w n1 n2
  | OP_TIMES => (n1*n2) mod 2^w
  | OP_DIVIDE => n1/n2
  | OP_SDIVIDE => sbop2 Z.quot w n1 n2
  | OP_MOD => N.modulo n1 n2
  | OP_SMOD => sbop2 Z.rem w n1 n2
  | OP_LSHIFT => (N.shiftl n1 n2) mod 2^w
  | OP_RSHIFT => N.shiftr n1 n2
  | OP_ARSHIFT => ashiftr w n1 n2
  | OP_AND => N.land n1 n2
  | OP_OR => N.lor n1 n2
  | OP_XOR => N.lxor n1 n2
  | OP_EQ => N.b2n (n1 =? n2)
  | OP_NEQ => N.b2n (negb (n1 =? n2))
  | OP_LT => N.b2n (n1 <? n2)
  | OP_LE => N.b2n (n1 <=? n2)
  | OP_SLT => N.b2n (slt w n1 n2)
  | OP_SLE => N.b2n (sle w n1 n2)
  end.

(* The bitwidth of the result of a binary operation *)
Definition widthof_binop (bop:binop_typ) (w:bitwidth) : bitwidth :=
  match bop with
  | OP_PLUS | OP_MINUS | OP_TIMES | OP_DIVIDE | OP_SDIVIDE | OP_MOD | OP_SMOD
  | OP_LSHIFT | OP_RSHIFT | OP_ARSHIFT | OP_AND | OP_OR | OP_XOR => w
  | OP_EQ | OP_NEQ | OP_LT | OP_LE | OP_SLT | OP_SLE => 1
  end.

(* Count 1-bits *)
Fixpoint Pos_popcount p := match p with
| xH => xH | xO q => Pos_popcount q | xI q => Pos.succ (Pos_popcount q) end.
Definition popcount n := match n with N0 => N0 | N.pos p => N.pos (Pos_popcount p) end.

(* Perform a unary operation. *)
Definition eval_unop (uop:unop_typ) (n:N) (w:bitwidth) : N :=
  match uop with
  | OP_NEG => msub w 0 n
  | OP_NOT => N.lnot n w
  | OP_POPCOUNT => popcount n
  | OP_BITWIDTH => N.size n
  end.
(* end details *)


(** There are four ways to cast a number to a new bitwidth, which we encode using
    [cast_typ]. TODO: add examples. Remember, this is geared to high schoolers.

      1.  CAST_LOW removes the upper bits of a number, keeping the lower bits.

      2.  CAST_HIGH removes the lower bits of a number, keeping the upper bits.

      3.  CAST_SIGNED extends the number by repeating its most significant bit.
          This preserves its value when it is interpreted as a one's or 
          two's complement number.

      4.  CAST_UNSIGNED extends the number with repeated 0-bits.  This preserves
          its value when it is interpreted as an unsigned number. *)

Inductive cast_typ : Type :=
| CAST_LOW
| CAST_HIGH
| CAST_SIGNED
| CAST_UNSIGNED.

(** Like with the binary and unary operations, the semantics of each cast type
    is organized in a function.  Instead of [eval_binop] this function is
    called [cast]. *)

Definition cast (c:cast_typ) (w w':bitwidth) (n:N) : N :=
  match c with
  | CAST_UNSIGNED => n
  | CAST_SIGNED => scast w w' n
  | CAST_HIGH => N.shiftr n (w - w')
  | CAST_LOW => n mod 2^w'
  end.

(** And here are the new expression constructors and their semantics. *)

Inductive exp : Type :=
(* begin details: Var, Word, BinOp, UnOp... *)
| Var (v:var)
| Word (n:N) (w:bitwidth)
| BinOp (b:binop_typ) (e1 e2:exp)
| UnOp (u:unop_typ) (e:exp)
(* end details *)
| Cast (c:cast_typ) (w:bitwidth) (e:exp) (* Cast to a new width. *)
| Extract (hi lo:N) (e:exp) (* Extract hbits to lbits of e. *)
| Concat (e1 e2:exp) (* Bit-concat two NumT expressions together. *)
.

Inductive eval_exp (c:typctx) (s:store): exp -> N -> bitwidth -> Prop :=
(* begin details: EVar, EWord, EBinOp, EUnOp... *)
| EVar v w (TYP: c v = Some w): eval_exp c s (Var v) (s v) w
| EWord n w: eval_exp c s (Word n w) n w
| EBinOp bop e1 e2 n1 n2 w (E1: eval_exp c s e1 n1 w) (E2: eval_exp c s e2 n2 w):
         eval_exp c s (BinOp bop e1 e2) (eval_binop bop w n1 n2) (widthof_binop bop w)
| EUnOp uop e1 n1 w (E1: eval_exp c s e1 n1 w):
        eval_exp c s (UnOp uop e1) (eval_unop uop n1 w) w
(* end details *)
| ECast ct w w' e1 n (E1: eval_exp c s e1 n w):
        eval_exp c s (Cast ct w' e1) (cast ct w w' n) w'
| EExtract w hi lo e val (E1: eval_exp c s e val w):
           eval_exp c s (Extract hi lo e) (xbits val lo (N.succ hi)) (N.succ hi - lo)
| EConcat e' e n' w' n w (E': eval_exp c s e' n' w') (E: eval_exp c s e n w):
          eval_exp c s (Concat e' e) (cbits n' w n) (w'+w).

(** Let's begin breaking these down. 

[| ECast ct w w' e1 n (E1: eval_exp c s e1 n w):
        eval_exp c s (Cast ct w' e1) (cast ct w w' n) w']
  
    Casting takes the w-bit expression [e1] and, given it is well-typed, casts it
    to a w'-bit value according to the cast type [ct].

[| EExtract w hi lo e val (E1: eval_exp c s e val w):
           eval_exp c s (Extract hi lo e) (xbits val lo (N.succ hi)) (N.succ hi - lo)]

    Extraction extracts bits from [val] starting at bit index [lo] and ending at
    bit index [hi].  This extracts a total of [1+hi-lo] bits, seen in the rule as
    [N.succ hi - lo].

    The example below shows how [xbits] (short for 'extract bits') computes the
    extracted value in the rule above.  Bit manipulation is one of the trickiest
    computations to think about so a visual example is very useful.

    --- Example ---

      val :=        0b 0  1  1  0     1  0  1  0     0  0  1  1     0  0  0  1
            indices:  15 14 13 12    11 10  9  8     7  6  5  4     3  2  1  0
      hi := 9
      lo := 4
      xbits val lo hi
      = xbits val 9 4 
      = N.shiftr val 4 mod 2^(9-4)
      = N.shiftr val 4 mod 2^5

      N.shiftr val 4:

         indices:     15 14 13 12    11 10  9  8     7  6  5  4     3  2  1  0
         shift 0:   0b 0  1  1  0     1  0  1  0     0  0  1  1     0  0  0  1
         shift 1:   0b    0  1  1  0     1  0  1  0     0  0  1  1     0  0  0
         shift 2:   0b       0  1  1  0     1  0  1  0     0  0  1  1     0  0
         shift 3:   0b          0  1  1  0     1  0  1  0     0  0  1  1     0
         shift 4:   0b                0  1  1  0     1  0  1  0     0  0  1  1

      N.shiftr val 4 mod 2^5:

         mod 2^0:   0b                                                       0
         mod 2^1:   0b                                                       1
         mod 2^2:   0b                                                    1  1
         mod 2^3:   0b                                                 0  1  1
         mod 2^4:   0b                                              0  0  1  1
         mod 2^5:   0b                                        0     0  0  1  1

      xbits val 4 9  = 0b 00011 = 0b11

      ... but if we extracted one more bit...

         mod 2^5:   0b                                     1  0     0  0  1  1

      xbits val 4 10 = 0b100011

    --- End Example ---

[| EConcat e1 e2 n1 w1 n2 w2 (E1: eval_exp c s e1 n1 w1) (E2: eval_exp c s e2 n2 w2):
          eval_exp c s (Concat e1 e2) (cbits n1 w2 n2) (w1+w2)]

    Concatenation combines the bitstrings of two values.  In the rule, the variables
    with an apostrophe (viz. [e'], [n'], [w']) correspond to the expression that 
    gets put on the high end of the new value, that is, on the left.  The variables
    without the apostrophe are on the low end, on the right.  The resulting bitwidth
    is, unsurprisingly, the sum of each expression's bitwidth ([w'+w]).


    Similar to how [xbits] performs the bit extraction in [EExtract], here [cbits]
    performs the concatenation.  Luckily, concatenation is much simpler.

    Say we want to concatenate a 5-bit value, [v'] on the left and a 4-bit value,
    [v], on the right.  We would write [cbits v' 4 v].

   --- Example ---
    v' := 0b 1 0001
    v  := 0b   0110
    cbits v' 4 v
    = 0b 1 0001 0110
   --- End Example ---
  *)

(** The typing of expressions. *)

Inductive hastyp_exp (c:typctx): exp -> bitwidth -> Prop :=
(* hide details: TVar, TWord, TBinOp, TUnOp, ... *)
| TVar v w (CV: c v = Some w): hastyp_exp c (Var v) w
| TWord n w (LT: n < 2^w): hastyp_exp c (Word n w) w
| TBinOp bop e1 e2 w
         (T1: hastyp_exp c e1 w) (T2: hastyp_exp c e2 w):
         hastyp_exp c (BinOp bop e1 e2) (widthof_binop bop w)
| TUnOp uop e w (T1: hastyp_exp c e w):
        hastyp_exp c (UnOp uop e) w
(* end details *)
| TCast ct w w' e (T1: hastyp_exp c e w)
        (LE: match ct with CAST_UNSIGNED | CAST_SIGNED => w <= w'
                         | CAST_HIGH | CAST_LOW => w' <= w end):
        hastyp_exp c (Cast ct w' e) w'
| TExtract w n1 n2 e1
           (T1: hastyp_exp c e1 w) (HI: n1 < w):
           hastyp_exp c (Extract n1 n2 e1) (N.succ n1 - n2)
| TConcat e1 e2 w1 w2
          (T1: hastyp_exp c e1 w1) (T2: hastyp_exp c e2 w2):
          hastyp_exp c (Concat e1 e2) (w1+w2).









End BitManipExp.
(* ================================================================= *)
(** ** The Picinae Statement Language *)

(** We now turn our attention to the expression language Picinae uses to represent computations.
    In Picinae_core this is encapsulated in a module parameterized by an architecture.

