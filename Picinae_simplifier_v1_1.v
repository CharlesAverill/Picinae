(* Picinae: Platform In Coq for INstruction Analysis of Executables       ZZM7DZ
                                                                          $MNDM7
   Copyright (c) 2022 Kevin W. Hamlen            ,,A??=P                 OMMNMZ+
   The University of Texas at Dallas         =:$ZZ$+ZZI                  7MMZMZ7
   Computer Science Department             Z$$ZM++O++                    7MMZZN+
                                          ZZ$7Z.ZM~?                     7MZDNO$
                                        ?Z8ZO7.OM=+?                     $OMO+Z+
   Any use, commercial or otherwise       ?D=++M++ZMMNDNDZZ$$Z?           MM,IZ=
   requires the express permission of        MZZZZZZ+...=.8NOZ8NZ$7       MM+$7M
   the author.                                 ?NNMMM+.IZDMMMMZMD8O77     O7+MZ+
                                                     MMM8MMMMMMMMMMM77   +MMMMZZ
   Expression simplifier:                            MMMMMMMMMMMZMDMD77$.ZMZMM78
   * auto-simplifies expressions faster than          MMMMMMMMMMMMMMMMMMMZOMMM+Z
     applying series of Coq tactics by leveraging      MMMMMMMMMMMMMMMMM^NZMMN+Z
     reflective ltac programming                        MMMMMMMMMMMMMMM/.$MZM8O+
                                                         MMMMMMMMMMMMMM7..$MNDM+
   To compile this module, first compile:                 MMDMMMMMMMMMZ7..$DM$77
   * Picinae_core                                          MMMMMMM+MMMZ7..7ZM~++
   * Picinae_theory                                         MMMMMMMMMMM7..ZNOOMZ
   * Picinae_statics                                         MMMMMMMMMM$.$MOMO=7
   * Picinae_simplifier_base                                  MDMMMMMMMO.7MDM7M+
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

Require Import Picinae_core.
Require Import Picinae_statics.
Require Import Picinae_finterp.
Require Export Picinae_simplifier_base.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import ZArith.

(* Introduction and Logical Organization:

   This module implements efficient auto-simplification of symbolic expressions
   yielded by abstract interpretation of Picinae IL programs.  To avoid prohibitive
   overheads associated with simplifying expressions via tactics (e.g., "rewrite"),
   we instead adopt an approach based on reflective programming, consisting of the
   following 3-stage pipeline:

   (I) Front end: A recursive Ltac turns the Coq expression to be simplified into
       a Simplification Abstract Syntax Tree (SAST), which is an inductive Gallina
       structure that can be analyzed and manipulated by Gallina functions.

   (II) Simplification Engine: A set of Gallina functions compute a simplified SAST
       from the original SAST.  This turns the simplification effort into a
       computation (effected by "compute", "vm_compute", or "native_compute")
       rather than a series of tactics.

   (III) Back end: The simplified SAST is turned back into a Coq expression and
       substituted for the original.  This step is also implemented as Gallina
       functions, but with special care taken to prevent Coq from over-expanding
       subterms that would blow up into a huge term if expanded.


   Structural Organization:

   The module structure of the implementation is partitioned into three parts:

   * Module Type "PSIMPL_DEFS_V*" defines all the datatypes and code whose
     implementations must remain visible (exported) to the user's proof environment
     in order for simplification to work properly.  This must include the bodies
     of all the simplifier functions, since the user's proof scope must be
     able to completely expand them to obtain simplified terms.

   * Module Type "PICINAE_SIMPLIFIER_V*" declares an interface for the simplifier,
     including all definitions in "PSIMPL_DEFS_V*", plus all tactics invoked during
     simplification, and type signatures for the theorems upon which they rely.

   * Module "Picinae_Simplifier_v*" proves all the theorems declared in the
     "PICINAE_SIMPLIFIER_V*" module type.

   This 3-part structure is necessary to avoid large code duplication, since the
   definitions in "PSIMPL_DEFS_V*" must be included in both the simplifier module
   and its type, but the theorem type signatures must only be included in the
   module type, not the module definition.

*)


Module Type PSIMPL_DEFS_V1_1 (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL).
Import IL.
Import TIL.
Import FIL.

(* Simplification Abstract Syntax Trees over Numbers, Bools, and Memory:

   The following SAST data structure represents Coq expressions to be simplified.
   Most Coq expressions contain at least some subterms that cannot be parsed or
   simplified (e.g., user-defined functions).  These unrecognized subterms get
   represented as "meta-variable" (NVar, BVar, MVar) nodes containing the original
   (unparsed) Coq term they represent.  These need some special considerations:

   * Simplification must preserve (or relocate/delete) these terms without
     expanding them, since expanding them can explode the simplification result
     into a massive, unreadable term.  Fast compute tactics like vm_compute
     expand everything, so we need a way to opacify them during computations.
     To do so, we devise a means to temporarily replace them with existential
     variables when needed.  Specifically, the simplifier puts an existential
     variable within each meta-variable node alongside the expandable term.
     Gallina computations always refer to the existential variable, which
     the back end later unifies with the original subterm to substitute it into
     the final simplified term unexpanded.

   * Even though we cannot directly simplify meta-variable subterms, we require
     a means to (conservatively) decide their equality to facilitate many
     important simplifications.  For example, x + y - y' simplifies to x if
     we can determine that y and y' are meta-variables containing identical
     Coq terms.  To achieve this, the parser labels each meta-variable with
     a numeric identifier.  Meta-variables with equal identifiers are guaranteed
     to contain identical subterms.

   * Likewise, many important simplifications become possible if an upper bound
     for numeric subterms is available.  For example, x mod 2^y simplifies to x
     when x < 2^y.  The parser therefore stocks meta-variable nodes with bounds
     info drawn from the proof context when possible.  This is achieved through
     dependent typing, which allows the proof of boundedness to be embedded
     within the SAST node.  Since the node contents are represented twice (once
     as an existential variable and once as the real Coq term), the bound proof
     must also appear twice. *)

(* A bound on a numeric variable n is either nothing (SIMP_UBND = unbounded)
   or a power of two p with a proof that n < 2^p. *)
Inductive nvar_bound (n:N) : Set :=
| SIMP_UBND
| SIMP_BND (p:N) (BND: n < 2^p).
Arguments SIMP_UBND {n}.
Arguments SIMP_BND {n} p BND.

Definition sastvar_id := N.

Inductive sastN : Set :=
| SIMP_NVar (id:sastvar_id) (n:N) (BND:nvar_bound n) (n':N) (BND':nvar_bound n')
| SIMP_Const (n:N)
| SIMP_Add (e1 e2:sastN)
| SIMP_Sub (e1 e2:sastN)
| SIMP_Mul (e1 e2:sastN)
| SIMP_Mod (e1 e2:sastN)
| SIMP_Pow (e1 e2:sastN)
| SIMP_LAnd (e1 e2:sastN)
| SIMP_LOr (e1 e2:sastN)
| SIMP_Xor (e1 e2:sastN)
| SIMP_ShiftR (e1 e2:sastN)
| SIMP_ShiftL (e1 e2:sastN)
| SIMP_Popcount (e1:sastN)
| SIMP_Parity8 (e1:sastN)
| SIMP_GetMem (en:endianness) (len:bitwidth) (m:sastM) (a:sastN)
| SIMP_App (m:sastM) (a:sastN)
| SIMP_IteNN (e0:sastN) (e1 e2:sastN)
| SIMP_IteBN (e0:sastB) (e1 e2:sastN)
with sastB : Set :=
| SIMP_BVar (id:sastvar_id) (b b':bool)
| SIMP_Bool (b:bool)
| SIMP_Eqb (e1 e2:sastN)
| SIMP_Ltb (e1 e2:sastN)
| SIMP_BAnd (e1 e2:sastB)
| SIMP_IteNB (e0:sastN) (e1 e2:sastB)
| SIMP_IteBB (e0:sastB) (e1 e2:sastB)
with sastM : Set :=
| SIMP_MVar (id:sastvar_id) (m:addr->N) (wtm: option (welltyped_memory m)) (m':addr->N) (wtm': option (welltyped_memory m'))
| SIMP_SetMem (en:endianness) (len:bitwidth) (m:sastM) (a:sastN) (n:sastN)
| SIMP_IteNM (e0:sastN) (e1 e2:sastM)
| SIMP_IteBM (e0:sastB) (e1 e2:sastM).

Scheme sastN_mind := Induction for sastN Sort Prop
  with sastB_mind := Induction for sastB Sort Prop
  with sastM_mind := Induction for sastM Sort Prop.
Combined Scheme sast_mind from sastN_mind, sastB_mind, sastM_mind.

(* Forests of sastN/Ms applied as value arguments to a function (usually returning a Prop) *)
Inductive sastU: Type -> Type :=
| SIMP_RetU {A} (f f':A) : sastU A
| SIMP_BindN {A} (f:sastU (value->A)) (t:sastN) (w:N) : sastU A
| SIMP_BindM {A} (f:sastU (value->A)) (t:sastM) (mw:N) : sastU A.

(* Simplification Abstract Syntax Trees over Store expressions:
   Note: Unrecognized store expression variables (SVar) do not get identifiers, since
   no simplification step requires comparing them for equality. *)
Inductive sastS : Type :=
| SIMP_SVar (s s':store)
| SIMP_Update (s:sastS) (v:var) (u u':value).

(* Forests of sastS's applied as value/store arguments to a function (usually returning a Prop) *)
Inductive sastV : Type -> Type :=
| SIMP_RetV {A} (f f':A) : sastV A
| SIMP_BindV {A} (f:sastV (value->A)) (t:sastS) (v:var) : sastV A
| SIMP_BindS {A} (f:sastV (store->A)) (t:sastS) : sastV A.

(* Semantics of SASTs:
   Each simplification stage (parsing, simplifying, and output) requires a proof of
   semantic preservation in order to be admitted by Coq.  We therefore define a
   denotational semantics for SASTs to serve as the basis for these proofs.  There
   are two important considerations motivating these semantic definitions:

   * Since the front end parser must be implemented as a tactic rather than a
     Gallina computation, we cannot prove general soundness of the parser.  We thus
     need a denotational semantics D such that D(parse(e)) always unifies with e
     (where parse(e) is the SAST that the parser generates for expression e).   The
     denotational semantics must therefore be very straightforward, so that it
     reduces SASTs back to the Coq expressions whence they were derived via only
     Coq's basic term unification reductions.

   * Simplifier soundness requires that the relation from metavar identifiers to
     Coq expressions be functional (i.e., not one-to-many).  To avoid the overhead
     of re-verifying this property for every SAST, we bake this property into the
     semantics of SASTs, so that it holds for every SAST.  Specifically, we
     parameterize the semantic valuation function by an interpretation function
     expressed as a metavariable tree (mvt), which maps metavar identifiers to the
     Coq expressions they denote.  The denotation of a metavar node is thus fully
     defined by its identifier; its other arguments are ignored by the semantics. *)

Inductive metavar_data :=
| MVNum (n:N) (bnd:nvar_bound n)
| MVBool (b:bool)
| MVMem (m:addr->N) (wtm: option (welltyped_memory m)).

Inductive metavar_tree := MVT_Empty | MVT_Node (d:metavar_data) (left: metavar_tree) (right: metavar_tree).

Fixpoint mvt_lookup mvt id :=
  match mvt with MVT_Empty => MVBool true | MVT_Node d t1 t2 =>
    match id with
    | xH => d
    | xO id => mvt_lookup t1 id
    | xI id => mvt_lookup t2 id
    end
  end.

Definition zeromem (a:addr) := N0.

Fixpoint eval_sastN mvt e {struct e} : N :=
  match e with
  | SIMP_NVar id n _ _ _ =>
      match id with N0 => n | Npos id =>
        match mvt_lookup mvt id with MVNum n' _ => n' | _ => N0 end
      end
  | SIMP_Const n => n
  | SIMP_Add e1 e2 => N.add (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Sub e1 e2 => N.sub (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Mul e1 e2 => N.mul (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Mod e1 e2 => N.modulo (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Pow e1 e2 => N.pow (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_LAnd e1 e2 => N.land (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_LOr e1 e2 => N.lor (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Xor e1 e2 => N.lxor (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_ShiftR e1 e2 => N.shiftr (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_ShiftL e1 e2 => N.shiftl (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Popcount e1 => popcount (eval_sastN mvt e1)
  | SIMP_Parity8 e1 => parity8 (eval_sastN mvt e1)
  | SIMP_GetMem en len m a => getmem en len (eval_sastM mvt m) (eval_sastN mvt a)
  | SIMP_App m a => (eval_sastM mvt m) (eval_sastN mvt a)
  | SIMP_IteNN e0 e1 e2 => if eval_sastN mvt e0 then eval_sastN mvt e2 else eval_sastN mvt e1
  | SIMP_IteBN e0 e1 e2 => if eval_sastB mvt e0 then eval_sastN mvt e1 else eval_sastN mvt e2
  end
with eval_sastB mvt e {struct e} : bool :=
  match e with
  | SIMP_BVar id b _ =>
      match id with N0 => b | Npos id =>
        match mvt_lookup mvt id with MVBool b' => b' | _ => true end
      end
  | SIMP_Bool b => b
  | SIMP_Eqb e1 e2 => N.eqb (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_Ltb e1 e2 => N.ltb (eval_sastN mvt e1) (eval_sastN mvt e2)
  | SIMP_BAnd e1 e2 => andb (eval_sastB mvt e1) (eval_sastB mvt e2)
  | SIMP_IteNB e0 e1 e2 => if eval_sastN mvt e0 then eval_sastB mvt e2 else eval_sastB mvt e1
  | SIMP_IteBB e0 e1 e2 => if eval_sastB mvt e0 then eval_sastB mvt e1 else eval_sastB mvt e2
  end
with eval_sastM mvt e {struct e} : addr -> N :=
  match e with
  | SIMP_MVar id m _ _ _ =>
      match id with N0 => m | Npos id =>
        match mvt_lookup mvt id with MVMem m' _ => m' | _ => zeromem end
      end
  | SIMP_SetMem en len m a n => setmem en len (eval_sastM mvt m) (eval_sastN mvt a) (eval_sastN mvt n)
  | SIMP_IteNM e0 e1 e2 => if eval_sastN mvt e0 then eval_sastM mvt e2 else eval_sastM mvt e1
  | SIMP_IteBM e0 e1 e2 => if eval_sastB mvt e0 then eval_sastM mvt e1 else eval_sastM mvt e2
  end.

Fixpoint eval_sastS e :=
  match e with
  | SIMP_SVar s _ => s
  | SIMP_Update s v u _ => update (eval_sastS s) v u
  end.

Fixpoint eval_sastV {A} (t: sastV A) : A :=
  match t with
  | SIMP_RetV f _ => f
  | SIMP_BindV t1 t2 v => eval_sastV t1 (eval_sastS t2 v)
  | SIMP_BindS t1 t2 => eval_sastV t1 (eval_sastS t2)
  end.

Fixpoint eval_sastU {A} mvt (t: sastU A) {struct t} : A :=
  match t with
  | SIMP_RetU f _ => f
  | SIMP_BindN t1 t2 w => eval_sastU mvt t1 (VaN (eval_sastN mvt t2) w)
  | SIMP_BindM t1 t2 mw => eval_sastU mvt t1 (VaM (eval_sastM mvt t2) mw)
  end.

(* The metavar tree that interprets metavar identifiers is constructed by treating
   identifiers as digit-lists denoting binary tree paths (0=left, 1=right), and
   adding metavar contents drawn from the node data (the existential variable args)
   incrementally during a pre-order traversal of the SAST.  Duplicate ids overwrite
   the tree node's contents.  When identifiers uniquely identify terms (which
   should always happen if the parser tactic code is correct), the overwritten
   terms are always identical, so there are no conflicts.  If not (which would
   imply a bug in the parser tactic code), Coq would fail to unify the denotation
   of the resulting SAST with the original term (which would raise an error at
   proof-time, never an incorrect, completed proof). *)

Fixpoint mvt_insert t id d {struct id} :=
  match id with
  | xH => match t with MVT_Empty => MVT_Node d MVT_Empty MVT_Empty
                     | MVT_Node _ t1 t2 => MVT_Node d t1 t2
          end
  | xO id => match t with MVT_Empty => MVT_Node (MVBool true) (mvt_insert MVT_Empty id d) MVT_Empty
                        | MVT_Node d0 t1 t2 => MVT_Node d0 (mvt_insert t1 id d) t2
             end
  | xI id => match t with MVT_Empty => MVT_Node (MVBool true) MVT_Empty (mvt_insert MVT_Empty id d)
                        | MVT_Node d0 t1 t2 => MVT_Node d0 t1 (mvt_insert t2 id d)
             end
  end.

Fixpoint make_mvtN' (mvt:metavar_tree) (e:sastN) {struct e} : metavar_tree
    with make_mvtB' (mvt:metavar_tree) (e:sastB) {struct e} : metavar_tree
    with make_mvtM' (mvt:metavar_tree) (e:sastM) {struct e} : metavar_tree.

  Local Ltac gen_make_mvt :=
    try lazymatch goal with
    | [ f: metavar_tree -> ?t -> metavar_tree |- ?t -> _ ] =>
      intro; lazymatch goal with [ x:t |- _ ] => gen_make_mvt; refine (f _ x) end
    | [ |- _ -> _ ] => intro; gen_make_mvt
    end.

  case e;
  [ intros; exact (match id with N0 => mvt | N.pos id => mvt_insert mvt id (MVNum n BND) end)
  | gen_make_mvt; assumption .. ].

  case e;
  [ intros; exact (match id with N0 => mvt | N.pos id => mvt_insert mvt id (MVBool b) end)
  | gen_make_mvt; assumption .. ].

  case e;
  [ intros; exact (match id with N0 => mvt | N.pos id => mvt_insert mvt id (MVMem m wtm) end)
  | gen_make_mvt; assumption .. ].

Defined.

Fixpoint make_mvtU' {A} mvt (t:sastU A) {struct t} :=
  match t with
  | SIMP_RetU _ _ => mvt
  | SIMP_BindN t' e _ => make_mvtU' (make_mvtN' mvt e) t'
  | SIMP_BindM t' e _ => make_mvtU' (make_mvtM' mvt e) t'
  end.

Definition make_mvtN := make_mvtN' MVT_Empty.
Definition make_mvtB := make_mvtB' MVT_Empty.
Definition make_mvtM := make_mvtM' MVT_Empty.
Definition make_mvtU {A} := @make_mvtU' A MVT_Empty.

(* Opacifying expansion-prone terms:

   After the Coq expression to be simplified has been parsed into an SAST, we
   here opacify any metavar terms, whose expansion we must prohibit during
   simplification, by copying the existential variable arguments of each metavar
   node overtop its other arguments.  Unifying the resulting SAST with the
   original has the secondary utility of instantiating all the existential
   variables, efficiently substituting all the metavar expressions into the
   fully simplified output expression without performing any additional
   computation on it. *)

Local Ltac gen_mutual_recursion tacrec e :=
  let rec recurse_on_args tac :=
    lazymatch goal with
    | |- _ -> _ => intro; lazymatch goal with [ x:?t |- _ ] => recurse_on_args tac;
      (only 1: (try tacrec; exact x)) end
    | _ => tac; revgoals
    end
  in unshelve (case e; revgoals; let ctrs := numgoals in do ctrs let g := numgoals in (
    only 1: lazymatch goal with |- sastvar_id -> _ => shelve | _ => recurse_on_args ltac:(constructor g) end
  )).

Fixpoint simpl_evarsN (e:sastN) : sastN
    with simpl_evarsB (e:sastB) : sastB
    with simpl_evarsM (e:sastM) : sastM.

  all: gen_mutual_recursion ltac:(first [ apply simpl_evarsN | apply simpl_evarsB | apply simpl_evarsM ]) e.
    intros. exact (SIMP_NVar id n BND n BND).
    intros. exact (SIMP_BVar id b b).
    intros. exact (SIMP_MVar id m wtm m wtm).
Defined.

Fixpoint simpl_evarsS e :=
  match e with
  | SIMP_SVar s _ => SIMP_SVar s s
  | SIMP_Update s v u _ => SIMP_Update (simpl_evarsS s) v u u
  end.

Fixpoint simpl_evarsV {A} (t: sastV A) :=
  match t with
  | SIMP_RetV f _ => SIMP_RetV f f
  | SIMP_BindV t1 t2 v => SIMP_BindV (simpl_evarsV t1) (simpl_evarsS t2) v
  | SIMP_BindS t1 t2 => SIMP_BindS (simpl_evarsV t1) (simpl_evarsS t2)
  end.

Fixpoint simpl_evarsU {A} (t: sastU A) :=
  match t with
  | SIMP_RetU f _ => SIMP_RetU f f
  | SIMP_BindN t1 t2 w => SIMP_BindN (simpl_evarsU t1) (simpl_evarsN t2) w
  | SIMP_BindM t1 t2 mw => SIMP_BindM (simpl_evarsU t1) (simpl_evarsM t2) mw
  end.

(*** SAST Simplification Helper Utilities ***)

(* SAST Equivalence:

   Many simplifications require a decision procedure for deciding equivalence of
   arbitrary SASTs.  Equivalence can be decided in the obvious way by recursively
   comparing constructors and their arguments, except for metavars which are
   compared by comparing their numeric identifiers.

   To make it easier to add new constructors to the SAST language, we here build
   the equivalence function programmatically using tactics.  It should therefore
   only be necessary to modify this code when adding a new SAST constructor that
   has a new type of argument, in which case one must tell the code what decision
   procedure should be used to determine equality for that type of argument (see
   comment below).
 *)

Definition mvarid_eq id1 id2 :=
  match id1 with N0 => false | Npos idp1 =>
    match id2 with N0 => false | Npos idp2 => Pos.eqb idp1 idp2 end
  end.

Definition endianness_eq en1 en2 :=
  match en1,en2 with BigE,BigE | LittleE,LittleE => true | _,_ => false end.

Fixpoint sastN_eq (e1 e2: sastN) {struct e1} : bool
    with sastB_eq (e1 e2: sastB) {struct e1} : bool
    with sastM_eq (e1 e2: sastM) {struct e1} : bool.

  Local Ltac pairup_args :=
    repeat match reverse goal with [ x:?t |- ?t -> _ ] => move x at bottom; let y := fresh x in intro y end.

  Local Ltac compare_pairs :=
    lazymatch reverse goal with [ x:?t, y:?t |- _ ] =>
      let cmp := lazymatch t with

      (* NOTE: For each type of SAST constructor argument, include a case here that
         returns a suitable equality decision procedure for it: *)
      | endianness => constr:(endianness_eq)
      | N => constr:(N.eqb)
      | bitwidth => constr:(N.eqb)
      | bool => constr:(Bool.eqb)

      | _ => lazymatch goal with [ cmp: t -> t -> bool |- _ ] => constr:(cmp) | _ => fail "need comparitor for" t end
      end in
      first [ refine (andb (cmp y x) _); clear x y; compare_pairs | exact (cmp y x) ]
    end.

  Local Ltac synthesize_comparison e1 e2 :=
    case e1; revgoals;
    let ctrs := numgoals in do ctrs (
      let n := numgoals in only 1: (intros; case e2; cycle n; cycle -1;
        (only 1: (clear e1 e2; 
          lazymatch reverse goal with [ id:sastvar_id |- sastvar_id -> _ ] =>
              let id' := fresh id in intro id'; intros; exact (mvarid_eq id id')
          | _ => pairup_args; compare_pairs
          end
        ));
        intros; exact false
      )
    ).

  all: synthesize_comparison e1 e2.
Defined.

(* The above synthesizes a definition like the following:

Fixpoint sastN_eq e1 e2 :=
  match e1, e2 with
  | SIMP_NVar id1 _ _ _ _, SIMP_NVar id2 _ _ _ _ => mvarid_eq id1 id2
  | SIMP_Const n1, SIMP_Const n2 => n1 =? n2
  | SIMP_Add e1 e1', SIMP_Add e2 e2' | SIMP_Sub e1 e1', SIMP_Sub e2 e2' | ... => (sastN_eq e1 e2) && (sastN_eq e1' e2')
  | SIMP_GetMem en1 len1 m1 a1, SIMP_GetMem en2 len2 m2 a2 =>
      (endianness_eq en1 en2) && (len1 =? len2) && (sastM_eq m1 m2) && (sastN_eq a1 a2)
  ...
  | _, _ => false
  end
with sastB_eq e1 e2 :=
  match e1, e2 with
  | SIMP_BVar id1 _ _, SIMP_BVar id2 _ _ => mvarid_eq id1 id2
  | SIMP_Bool b1, SIMP_Bool b2 => Bool.eqb b1 b2
  | SIMP_Eqb e1 e1', SIMP_Eqb e2 e2' | ... => (sastN_eq e1 e2) && (sastN_eq e1' e2')
  ...
  | _, _ => false
  end
with sastM_eq e1 e2 :=
  match e1, e2 with
  | SIMP_MVar id1 _ _ _ _, SIMP_MVar id2 _ _ _ _ => mvarid_eq id1 id2
  | SIMP_SetMem en1 len1 m1 a1 n1, SIMP_SetMem en2 len2 m2 a2 n2 =>
      (endianness_eq en1 en2) && (len1 =? len2) && (sastM_eq m1 m2) && (sastN_eq a1 a2) && (sastN_eq n1 n2)
  ...
  | _, _ => false
  end.

*)

(* Upper+lower bounds:

   Many of the most important simplifications require (possibly conservative) lower
   and/or upper bounds for numerical subexpressions.  For example, "x mod y"
   simplifies to "x" whenever x<y.  The following estimates conservative bounds
   for numeric SASTs.  Upper bounds of None indicate no known upper bound. *)

Fixpoint simpl_bounds mvt e {struct e} : N * option N :=
  match e with
  | SIMP_NVar id _ _ _ _ =>
      match id with 0 => (0,None) | Npos id =>
        (0, match mvt_lookup mvt id with MVNum _ (SIMP_BND p _) => Some (N.ones p) | _ => None end)
      end
  | SIMP_Const n => (n, Some n)
  | SIMP_Add e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                      (lo1+lo2, match ohi1 with None => None | Some hi1 => option_map (N.add hi1) ohi2 end)
  | SIMP_Sub e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                      (match ohi2 with None => 0 | Some hi2 => lo1 - hi2 end,
                       match ohi1 with None => None | Some hi1 => Some (hi1 - lo2) end)
  | SIMP_Mul e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                      (lo1*lo2, match ohi1 with None => None | Some hi1 => option_map (N.mul hi1) ohi2 end)
  | SIMP_Mod e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in
                      match simpl_bounds mvt e2 with (0,_) => (0, ohi1) | (lo2,ohi2) =>
                        match ohi1 with None => (0,option_map N.pred ohi2) | Some hi1 =>
                          (if hi1 <? lo2 then lo1 else 0,
                           match ohi2 with None => Some hi1 | Some hi2 => Some (N.min hi1 (N.pred hi2)) end)
                        end
                      end
  | SIMP_Pow e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                      let ohi' := match ohi1 with None => None | Some hi1 => option_map (N.pow hi1) ohi2 end in
                      match lo1 with 0 => (0, option_map (N.max 1) ohi') | _ => (lo1^lo2, ohi') end
  | SIMP_LAnd e1 e2 =>
      (0, match simpl_bounds mvt e1 with (_,None) => None | (_,Some hi1) =>
            match simpl_bounds mvt e2 with (_,None) => None | (_,Some hi2) =>
              Some (N.ones (N.min (N.size hi1) (N.size hi2)))
            end
          end)
  | SIMP_LOr e1 e2 | SIMP_Xor e1 e2 =>
      (0, match simpl_bounds mvt e1 with (_,None) => None | (_,Some hi1) =>
            match simpl_bounds mvt e2 with (_,None) => None | (_,Some hi2) =>
              Some (N.ones (N.max (N.size hi1) (N.size hi2)))
            end
          end)
  | SIMP_ShiftR e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                         (match ohi2 with None => 0 | Some hi2 => N.shiftr lo1 hi2 end,
                          option_map (fun hi1 => N.shiftr hi1 lo2) ohi1)
  | SIMP_ShiftL e1 e2 => let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
                         (N.shiftl lo1 lo2, match ohi1 with None => None | Some hi1 => option_map (N.shiftl hi1) ohi2 end)
  | SIMP_Popcount e1 => (0, option_map N.size (snd (simpl_bounds mvt e1)))
  | SIMP_Parity8 _ => (0, Some 1)
  | SIMP_GetMem _ len m _ =>
      (0, match m with SIMP_MVar (Npos id) _ _ _ _ =>
            match mvt_lookup mvt id with MVMem _ (Some _) => Some (N.ones (Mb*len)) | _ => None end
          | _ => None end)
  | SIMP_App m _ =>
      (0, match m with SIMP_MVar (Npos id) _ _ _ _ =>
            match mvt_lookup mvt id with MVMem _ (Some _) => Some (N.ones Mb) | _ => None end
          | _ => None end)
  | SIMP_IteNN _ e1 e2 | SIMP_IteBN _ e1 e2 =>
      let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
      (N.min lo1 lo2, match ohi1 with None => None | Some hi1 => option_map (N.max hi1) ohi2 end)
  end.

Definition sastN_le mvt e1 e2 :=
  match simpl_bounds mvt e1 with (_,None) => false | (_,Some hi1) => hi1 <=? fst (simpl_bounds mvt e2) end.

Definition sastN_lt mvt e1 e2 :=
  match simpl_bounds mvt e1 with (_,None) => false | (_,Some hi1) => hi1 <? fst (simpl_bounds mvt e2) end.

(* Multiples of powers of two:

   Another important class of simplifications requires deciding whether a
   subexpression is guaranteed to be a multiple of a given power of two.  For
   example, "x mod 2^y" simplifies to 0 whenever x is a multiple of 2^y.  The
   following procedure decides (conservatively) whether an arbitrary SAST
   is guaranteed to denote a multiple of a given power of two. *)

Fixpoint pos_log2opt p :=
  match p with xH => Some 0 | xI _ => None | xO p => option_map N.succ (pos_log2opt p) end.

Fixpoint multiple_of_pow2 mvt e n {struct e} :=
  match n with N0 => true | _ =>
    match e with
    | SIMP_Const n1 => match n1 with N0 => true | N.pos p1 =>
        match pos_log2opt p1 with None => false | Some n2 => n <=? n2 end
      end
    | SIMP_Add e1 e2 | SIMP_Sub e1 e2 | SIMP_Mod e1 e2 | SIMP_LOr e1 e2 | SIMP_Xor e1 e2
    | SIMP_IteNN _ e1 e2 | SIMP_IteBN _ e1 e2 =>
        andb (multiple_of_pow2 mvt e1 n) (multiple_of_pow2 mvt e2 n)
    | SIMP_Mul e1 e2 | SIMP_LAnd e1 e2 => orb (multiple_of_pow2 mvt e1 n) (multiple_of_pow2 mvt e2 n)
    | SIMP_ShiftR e1 e2 => match e2 with SIMP_Const n2 => multiple_of_pow2 mvt e1 (n+n2) | _ => false end
    | SIMP_ShiftL e1 e2 => multiple_of_pow2 mvt e1 (n - fst (simpl_bounds mvt e2))
    | SIMP_Pow e1 e2 =>
        match e1 with SIMP_Const n1 =>
          match n1 with 0 => false | N.pos p1 =>
            match pos_log2opt p1 with None => false | Some m =>
              match simpl_bounds mvt e2 with (0,_) => false | _ =>
                match N.div_eucl m n with (N.pos _,0) => true | _ => false end
              end
            end
          end
        | _ => false
        end
    | SIMP_Popcount _ | SIMP_Parity8 _ | SIMP_NVar _ _ _ _ _ | SIMP_GetMem _ _ _ _ | SIMP_App _ _ => false
    end
  end.

(*** MAIN SIMPLIFICATION LOGIC ***)

(* Simplification is arranged a set of functions, one for each top-level SAST
   constructor.  For each constructor's simplification algorithm we must later prove
   (in the Module definition, not within this Module Type definition) that the
   denotation of the simplified SAST returned by the function equals the denotation
   of the original SAST.  The following subroutines implement each simplification,
   organized by SAST constructor.  Modifying and adding to these subroutines
   constitutes the majority of work for improving and extending the simplifier.
   Most of these subroutines are independent, but the simplification for "mod" has
   a more ambitious implementation that performs a specialized, recursive
   simplification of all operators within the left argument to a "mod"; and the
   simplification for bitwise-and calls into the "mod" simplifier whenever one of
   its arguments is the predecessor of a power of two (e.g., when simplifying
   x & (2^y-1) to x mod 2^y. *)

(** Add simplification **)

Definition simpl_add e1 e2 :=
  match e1 with SIMP_Const n1 =>
    match n1 with 0 => e2 | _ =>
      match e2 with
      | SIMP_Const n2 => SIMP_Const (n1+n2)
      | SIMP_Add e2a e2b => match e2a with SIMP_Const n2a => SIMP_Add (SIMP_Const (n1+n2a)) e2b | _ => SIMP_Add e1 e2 end
      | _ => SIMP_Add e1 e2
      end
    end
  | SIMP_Add e1a e1b =>
    match e1b with SIMP_Const n1b =>
      match e2 with SIMP_Const n2 => SIMP_Add e1a (SIMP_Const (n1b+n2)) | _ => SIMP_Add e1 e2 end
    | _ => SIMP_Add e1 e2
    end
  | _ => match e2 with SIMP_Const n2 =>
           match n2 with 0 => e1 | _ => SIMP_Add e1 e2 end
         | _ => SIMP_Add e1 e2
         end
  end.

(** Sub simplification **)

Definition simpl_sub mvt e1 e2 :=
  if sastN_eq e1 e2 then SIMP_Const 0 else
  match match e1 with
        | SIMP_Const n1 =>
            match e2 with SIMP_Const n2 => Some (SIMP_Const (n1-n2)) | _ => None end
        | _ => match e2 with SIMP_Const 0 => Some e1 | _ => None end
        end
  with Some e' => e' | None =>
    match match e1 with SIMP_Add e1a e1b => if sastN_eq e1b e2 then Some e1a else None | _ => None end
    with Some e' => e' | None =>
      match e2 with SIMP_Sub e2a e2b =>
        if andb (sastN_le mvt e2b e2a) (sastN_le mvt e2 e1) then SIMP_Sub (simpl_add e1 e2b) e2a else SIMP_Sub e1 e2
      | _ => SIMP_Sub e1 e2
      end
    end
  end.

(** Mul simplification **)

Definition simpl_mul e1 e2 :=
  match e1 with SIMP_Const n1 =>
    if n1 <=? 1 then match n1 with 0 => SIMP_Const 0 | _ => e2 end else
    match e2 with SIMP_Const n2 => SIMP_Const (n1*n2) | _ => SIMP_Mul e1 e2 end
  | _ =>
    match e2 with SIMP_Const n2 =>
      if n2 <=? 1 then match n2 with 0 => SIMP_Const 0 | _ => e1 end else
      SIMP_Mul e1 e2
    | _ => SIMP_Mul e1 e2
    end
  end.

(** LOr simplification **)

Definition simpl_lor e1 e2 :=
  if sastN_eq e1 e2 then e1 else
  match e1 with SIMP_Const n1 =>
    match n1 with 0 => e2 | _ =>
      match e2 with SIMP_Const n2 => SIMP_Const (N.lor n1 n2) | _ => SIMP_LOr e1 e2 end
    end
  | _ => match e2 with SIMP_Const n2 =>
           match n2 with 0 => e1 | _ => SIMP_LOr e1 e2 end
         | _ => SIMP_LOr e1 e2
         end
  end.

(** Xor simplification **)

Definition simpl_xor e1 e2 :=
  if sastN_eq e1 e2 then SIMP_Const 0 else
  match e1 with SIMP_Const n1 =>
    match n1 with 0 => e2 | _ =>
      match e2 with SIMP_Const n2 => SIMP_Const (N.lxor n1 n2) | _ => SIMP_Xor e1 e2 end
    end
  | _ => match e2 with SIMP_Const n2 =>
           match n2 with 0 => e1 | _ => SIMP_Xor e1 e2 end
         | _ => SIMP_Xor e1 e2
         end
  end.

(** GetMem simplification **)

Definition simpl_getmem_len en len m a :=
  match len with 0 => SIMP_Const 0 | 1 => SIMP_App m a | _ => SIMP_GetMem en len m a end.

Fixpoint simpl_getmem mvt en len m a {struct m} :=
  match m with
  | SIMP_SetMem en0 len0 m0 a0 n0 =>
      if andb (endianness_eq en en0) (andb (len =? len0) (sastN_eq a a0)) then
        match len with 0 => SIMP_Const 0 | _ => n0 end
      else if sastN_le mvt (SIMP_Add a (SIMP_Const len)) a0 then simpl_getmem mvt en len m0 a
      else if sastN_le mvt (SIMP_Add a0 (SIMP_Const len0)) a then simpl_getmem mvt en len m0 a
      else simpl_getmem_len en len m a
  | _ => simpl_getmem_len en len m a
  end.

(** ShiftR simplification **)

Definition simpl_shiftr mvt e1 e2 :=
  if match simpl_bounds mvt (SIMP_ShiftR e1 e2) with (_,Some 0) => true | _ => false end then SIMP_Const 0 else
  match e2 with SIMP_Const n2 =>
    match n2 with 0 => e1 | _ =>
      match e1 with
      | SIMP_Const n1 => SIMP_Const (N.shiftr n1 n2)
      | SIMP_GetMem LittleE len (SIMP_MVar (Npos id) _ _ _ _ as m) a =>
          match mvt_lookup mvt id with MVMem _ (Some _) =>
            match N.div_eucl n2 Mb with (_,N.pos _) => SIMP_ShiftR e1 e2 | (q,0) =>
              simpl_getmem_len LittleE (len-q) m (simpl_add a (SIMP_Const q))
            end
          | _ => SIMP_ShiftR e1 e2
          end
      | _ => SIMP_ShiftR e1 e2
      end
    end
  | _ => match e1 with SIMP_Const n1 =>
           match n1 with 0 => SIMP_Const 0 | _ => SIMP_ShiftR e1 e2 end
         | _ => SIMP_ShiftR e1 e2
         end
  end.

(** ShiftL simplification **)

Definition simpl_shiftl e1 e2 :=
  match e1 with SIMP_Const n1 =>
    match n1 with 0 => SIMP_Const 0 | _ =>
      match e2 with SIMP_Const n2 => SIMP_Const (N.shiftl n1 n2) | _ => SIMP_ShiftL e1 e2 end
    end
  | _ => match e2 with SIMP_Const n2 =>
           match n2 with 0 => e1 | _ => SIMP_ShiftL e1 e2 end
         | _ => SIMP_ShiftL e1 e2
         end
  end.

(** Pow simplification **)

Definition simpl_pow mvt e1 e2 :=
  match e1 with SIMP_Const n1 =>
    match match e2 with SIMP_Const n2 => Some (SIMP_Const (n1^n2)) | _ => None end
    with Some e' => e' | None =>
      match n1 with 0 => match simpl_bounds mvt e2 with (0,_) => SIMP_Pow e1 e2 | _ => SIMP_Const 0 end | N.pos p1 =>
        match pos_log2opt p1 with None => SIMP_Pow e1 e2 | Some m =>
          simpl_shiftl (SIMP_Const 1) (simpl_mul (SIMP_Const m) e2)
        end
      end
    end
  | _ => SIMP_Pow e1 e2
  end.

(** Eqb simplification **)

Definition simpl_eqb mvt e1 e2 :=
  let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
  if orb match ohi1 with None => false | Some hi1 => hi1 <? lo2 end
         match ohi2 with None => false | Some hi2 => hi2 <? lo1 end then SIMP_Bool false
  else if match ohi1,ohi2 with Some hi1,Some hi2 => andb (andb (lo1 =? hi1) (lo2 =? hi2)) (lo1 =? lo2)
                             | _,_ => false end then SIMP_Bool true else
  match e1 with
  | SIMP_Const 0 =>
    match e2 with SIMP_Mod (SIMP_Sub (SIMP_Add e2a e2b) e2c) e2d =>
      if andb (sastN_eq e2a e2d) (andb (sastN_lt mvt (SIMP_Const 0) e2a) (andb (sastN_lt mvt e2b e2a) (sastN_lt mvt e2c e2a)))
      then SIMP_Eqb e2b e2c else SIMP_Eqb e1 e2
    | _ => SIMP_Eqb e1 e2
    end
  | _ => SIMP_Eqb e1 e2
  end.

(** Ltb simplification **)

Definition simpl_ltb mvt e1 e2 :=
  let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
  if match ohi1 with None => false | Some hi1 => hi1 <? lo2 end then SIMP_Bool true
  else if match ohi2 with None => false | Some hi2 => hi2 <=? lo1 end then SIMP_Bool false
  else SIMP_Ltb e1 e2.

(** BAnd simplification **)

Definition simpl_band e1 e2 :=
  if sastB_eq e1 e2 then e1 else
  match e1 with SIMP_Bool b1 => if b1 then e2 else e1
  | _ => match e2 with SIMP_Bool b2 => if b2 then e1 else e2
         | _ => SIMP_BAnd e1 e2
         end
  end.

(** LAnd simplification without converting land-to-mod (so it can be used non-circularly within mod simplification) **)

Definition simpl_land_const f e1 n2 :=
  match e1 with SIMP_Const n1 => SIMP_Const (N.land n1 n2) | _ =>
    match n2 with 0 => SIMP_Const 0 | N.pos p2 => f e1 p2 end
  end.

Definition simpl_land' f e1 e2 :=
  match e2 with SIMP_Const n2 => simpl_land_const f e1 n2 | _ =>
    match e1 with SIMP_Const n1 => simpl_land_const f e2 n1 | _ =>
      if sastN_eq e1 e2 then e1 else SIMP_LAnd e1 e2
    end
  end.

Definition simpl_land_nomod := simpl_land' (fun e1 p2 => SIMP_LAnd e1 (SIMP_Const (N.pos p2))).

(** Mod simplification **)

Definition simpl_mod_core mvt e1 e2 :=
  let (lo1,ohi1) := simpl_bounds mvt e1 in let (lo2,ohi2) := simpl_bounds mvt e2 in
  if match ohi1 with None => false | Some hi1 => hi1 <? lo2 end then e1 else
  match match ohi2 with None => None | Some hi2 =>
          match hi2 with 0 => Some e1 | _ =>
            if lo2 =? hi2 then
              if lo2 =? 1 then Some (SIMP_Const 0) else
                match ohi1 with
                | Some hi1 => if lo1 =? hi1 then Some (SIMP_Const (lo1 mod lo2)) else None
                | _ => None end
            else None
          end
        end
  with Some e => e | None =>
    match e1,e2 with SIMP_Mod e (SIMP_Const (N.pos p1)), SIMP_Const (N.pos p2) =>
      let (lo,hi) := match (p1 ?= p2)%positive with Gt => (p2,p1) | _ => (p1,p2) end in
      match N.pos_div_eucl hi (N.pos lo) with (_,0) => SIMP_Mod e (SIMP_Const (N.pos lo)) | _ => SIMP_Mod e1 e2 end
    | _,_ => SIMP_Mod e1 e2
    end
  end.

Definition least_multiple_of_pow2_ge m n :=
  match N.div_eucl m (N.shiftl 1 n) with (_,0) => m | (q,_) => N.shiftl 1 n * N.succ q end.

Definition simpl_ite_sameN f e1 e2 := if sastN_eq e1 e2 then e1 else f e1 e2.

Fixpoint simpl_under_modpow2 mvt e n {struct e} :=
  match n with 0 => SIMP_Const 0 | _ =>
    match e with
    | SIMP_Const n1 => SIMP_Const (n1 mod (N.shiftl 1 n))
    | SIMP_Add e1 e2 => simpl_add (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_Sub e1 e2 =>
      match simpl_bounds mvt e2 with (_,None) => e | (_,Some hi2) =>
        let (lo1,ohi1) := simpl_bounds mvt e1 in
        if lo1 <? hi2 then e else
        let e2' := simpl_under_modpow2 mvt e2 n in
        match simpl_bounds mvt e2' with (_,None) => e | (_,Some hi2') =>
          let e1' := simpl_under_modpow2 mvt e1 n in
          let (lo1',ohi1') := simpl_bounds mvt e1' in
          simpl_sub mvt (simpl_add (SIMP_Const (least_multiple_of_pow2_ge (hi2' - lo1') n)) e1') e2'
        end
      end
    | SIMP_Mul e1 e2 => simpl_mul (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_Mod e1 e2 => if multiple_of_pow2 mvt e2 n then simpl_under_modpow2 mvt e1 n else e
    | SIMP_LAnd e1 e2 =>
      match match e1 with SIMP_Const n1 => Some n1 | _ => None end with Some n1 =>
        simpl_land_nomod (SIMP_Const (n1 mod N.shiftl 1 n)) (simpl_under_modpow2 mvt e2 (N.min (N.size n1) n))
      | None => match match e2 with SIMP_Const n2 => Some n2 | _ => None end with Some n2 =>
                  simpl_land_nomod (simpl_under_modpow2 mvt e1 (N.min (N.size n2) n)) (SIMP_Const (n2 mod N.shiftl 1 n))
                | None => simpl_land_nomod (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
             end
      end
    | SIMP_LOr e1 e2 => simpl_lor (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_Xor e1 e2 => simpl_xor (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_ShiftR e1 e2 => match simpl_bounds mvt e2 with (_, Some hi2) => simpl_shiftr mvt (simpl_under_modpow2 mvt e1 (n+hi2)) e2 | _ => e end
    | SIMP_ShiftL e1 e2 => simpl_shiftl (simpl_under_modpow2 mvt e1 (n - fst (simpl_bounds mvt e2))) e2
    | SIMP_IteNN e0 e1 e2 => simpl_ite_sameN (SIMP_IteNN e0) (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_IteBN e0 e1 e2 => simpl_ite_sameN (SIMP_IteBN e0) (simpl_under_modpow2 mvt e1 n) (simpl_under_modpow2 mvt e2 n)
    | SIMP_GetMem en len m a =>
      match en with BigE => e | LittleE =>
        match N.div_eucl n Mb with (_,N.pos _) => e | (q,0) =>
          match m with SIMP_MVar (Npos id) _ _ _ _ =>
            match mvt_lookup mvt id with MVMem _ (Some _) => simpl_getmem mvt en (N.min len q) m a | _ => e end
          | _ => e
          end
        end
      end
    | SIMP_Pow _ _ (* SIMP_Pow should already have been simplified to SIMP_ShiftL when possible, so ignore here *)
    | SIMP_NVar _ _ _ _ _ | SIMP_Popcount _ | SIMP_Parity8 _ | SIMP_App _ _ => e
    end
  end.

Definition simpl_mod mvt e1 e2 :=
  simpl_mod_core mvt
    match e2 with SIMP_Const (N.pos p2) =>
      match pos_log2opt p2 with None => e1 | Some n2 => simpl_under_modpow2 mvt e1 n2 end
    | _ => e1
    end e2.

(** And simplification with and-to-mod conversion: (x & (2^y-1)) = (x mod 2^y) **)

Fixpoint pos_is_ones p :=
  match p with xH => true | xO _ => false | xI p => pos_is_ones p end.

Definition simpl_and2mod mvt e1 p2 :=
  if pos_is_ones p2 then simpl_mod mvt e1 (SIMP_Const (N.pos (Pos.succ p2)))
  else SIMP_LAnd (simpl_under_modpow2 mvt e1 (N.size (N.pos p2))) (SIMP_Const (N.pos p2)).

Definition simpl_land mvt := simpl_land' (simpl_and2mod mvt).

(** Ite simplification **)

Inductive sastNB_typ : Set := SastN | SastB.
Inductive sastNBM_typ : Set := NB2NBM (t:sastNB_typ) | SastM.
Definition sastNB t := match t with SastN => sastN | SastB => sastB end.
Definition sastNBM t := match t with NB2NBM t' => sastNB t' | SastM => sastM end.

Definition sastNB_eq {t1 t2} : sastNB t1 -> sastNB t2 -> bool :=
  match t1,t2 with
  | SastN,SastN => sastN_eq
  | SastB,SastB => sastB_eq
  | _,_ => fun _ _ => false
  end.

Definition sastNBM_eq {t} : sastNBM t -> sastNBM t -> bool :=
  match t with NB2NBM SastN => sastN_eq | NB2NBM SastB => sastB_eq | SastM => sastM_eq end.

Definition ite_parts {t} : sastNBM t -> option (sigT sastNB * (sastNBM t * sastNBM t)) :=
  match t with
  | NB2NBM SastN =>
    fun e0 => match e0 with
    | SIMP_IteNN e0 e1 e2 => Some (existT _ SastN e0, (e1,e2))
    | SIMP_IteBN e0 e1 e2 => Some (existT _ SastB e0, (e1,e2))
    | _ => None
    end
  | NB2NBM SastB =>
    fun e0 => match e0 with
    | SIMP_IteNB e0 e1 e2 => Some (existT _ SastN e0, (e1,e2))
    | SIMP_IteBB e0 e1 e2 => Some (existT _ SastB e0, (e1,e2))
    | _ => None
    end
  | SastM =>
    fun e0 => match e0 with
    | SIMP_IteNM e0 e1 e2 => Some (existT _ SastN e0, (e1,e2))
    | SIMP_IteBM e0 e1 e2 => Some (existT _ SastB e0, (e1,e2))
    | _ => None
    end
  end.

Definition make_ite t t' : sastNB t -> sastNBM t' -> sastNBM t' -> sastNBM t' :=
  match t' with
  | NB2NBM SastN => match t with SastN => SIMP_IteNN | SastB => SIMP_IteBN end
  | NB2NBM SastB => match t with SastN => SIMP_IteNB | SastB => SIMP_IteBB end
  | SastM => match t with SastN => SIMP_IteNM | SastB => SIMP_IteBM end
  end.

Definition simpl_static_branch {t} mvt : sastNB t -> option bool :=
  match t with
  | SastN => fun e0 : sastNB SastN =>
             match simpl_bounds mvt e0 with (N.pos _,_) => Some true
                                          | (_,Some 0) => Some false
                                          | _ => None
              end
  | SastB => fun e0 : sastNB SastB =>
             match e0 with SIMP_Bool b => Some b | _ => None end
  end.

(* Simplify SASTs of the form:  if (if e0 then e0a else e0b) then e1 else e2
   when e0a and e0b are statically known. *)
Definition simpl_ite_combine {x y z} mvt (e0:sastNB x) (e0a e0b:sastNB y) (e1 e2:sastNBM z) :=
  match simpl_static_branch mvt e0a with
  | None => make_ite y z (make_ite x (NB2NBM y) e0 e0a e0b) e1 e2
  | Some b0a =>
    match simpl_static_branch mvt e0b with
    | None => make_ite y z (make_ite x (NB2NBM y) e0 e0a e0b) e1 e2
    | Some b0b =>
      match b0a,b0b with
      | true,true => e1
      | false,false => e2
      | true,false => make_ite x z e0 e1 e2
      | false,true => make_ite x z e0 e2 e1
      end
    end
  end.

(* Perform three kinds of simplification:
   (1) if _ then e else e --> e
   (2) if e0 then e1 else e2 --> e1 or e2 (when e0 is statically known)
   (3) if (if e0 then e0a else e0b) then e1 else e2 --> if e0 then _ else _
       (when e0a and e0b are statically known) *)
Definition simpl_ite t t' mvt (e0:sastNB t) (e1 e2:sastNBM t') : sastNBM t' :=
  if sastNBM_eq e1 e2 then e1 else
  match simpl_static_branch mvt e0 with Some b0 => if b0 then e1 else e2 | None =>
    match @ite_parts (NB2NBM t) e0 with
    | None => make_ite t t' e0 e1 e2
    | Some (existT _ e0ct e0c,(e0a,e0b)) => simpl_ite_combine mvt e0c e0a e0b e1 e2
    end
  end.


(* Main dispatcher functions for simplifier routines: *)

Definition simplN_dispatch mvt e :=
  match e with
  | SIMP_Const _ | SIMP_NVar _ _ _ _ _ => e
  | SIMP_Add e1 e2 => simpl_add e1 e2
  | SIMP_Sub e1 e2 => simpl_sub mvt e1 e2
  | SIMP_Mul e1 e2 => simpl_mul e1 e2
  | SIMP_Mod e1 e2 => simpl_mod mvt e1 e2
  | SIMP_Pow e1 e2 => simpl_pow mvt e1 e2
  | SIMP_LAnd e1 e2 => simpl_land mvt e1 e2
  | SIMP_LOr e1 e2 => simpl_lor e1 e2
  | SIMP_Xor e1 e2 => simpl_xor e1 e2
  | SIMP_ShiftR e1 e2 => simpl_shiftr mvt e1 e2
  | SIMP_ShiftL e1 e2 => simpl_shiftl e1 e2
  | SIMP_Popcount _ => e
  | SIMP_Parity8 _ => e
  | SIMP_GetMem en len m a => simpl_getmem mvt en len m a
  | SIMP_App m a => simpl_getmem mvt LittleE 1 m a
  | SIMP_IteNN e0 e1 e2 => simpl_ite SastN (NB2NBM SastN) mvt e0 e1 e2
  | SIMP_IteBN e0 e1 e2 => simpl_ite SastB (NB2NBM SastN) mvt e0 e1 e2
  end.

Definition simplB_dispatch mvt e :=
  match e with
  | SIMP_Bool _ | SIMP_BVar _ _ _ => e
  | SIMP_Eqb e1 e2 => simpl_eqb mvt e1 e2
  | SIMP_Ltb e1 e2 => simpl_ltb mvt e1 e2
  | SIMP_BAnd e1 e2 => simpl_band e1 e2
  | SIMP_IteNB e0 e1 e2 => simpl_ite SastN (NB2NBM SastB) mvt e0 e1 e2
  | SIMP_IteBB e0 e1 e2 => simpl_ite SastB (NB2NBM SastB) mvt e0 e1 e2
  end.

Definition simplM_dispatch mvt e :=
  match e with
  | SIMP_MVar _ _ _ _ _ => e
  | SIMP_SetMem en len m a n => e
  | SIMP_IteNM e0 e1 e2 => simpl_ite SastN SastM mvt e0 e1 e2
  | SIMP_IteBM e0 e1 e2 => simpl_ite SastB SastM mvt e0 e1 e2
  end.

Definition simpl_dispatch {t} : metavar_tree -> sastNBM t -> sastNBM t :=
  match t with NB2NBM SastN => simplN_dispatch
             | NB2NBM SastB => simplB_dispatch
             | SastM => simplM_dispatch
  end.


(* Special simplification routines for ternary (ite) expressions appearing in
   the _arguments_ of unary and binary operations.  Such operations are distributed
   inside the branches of the ternary if doing so leads to a simplification in
   both branches (usually eliminating the operation).  Example:
      (if e then 1 else 2) + 1 --> (if e then 2 else 3)
 *)

(* uop (if e0 then e1:t else e2:t) : t' --> if e0 then (uop e1) else (uop e2) : t' *)
Definition simpl_uop_ite' {t t'} (uop: sastNBM t -> sastNBM t') mvt (e:sastNBM t) :=
  match ite_parts e with None => None | Some (existT _ t0 e0, (e1,e2)) =>
    let e1' := simpl_dispatch mvt (uop e1) in if sastNBM_eq (uop e1) e1' then None else
    let e2' := simpl_dispatch mvt (uop e2) in if sastNBM_eq (uop e2) e2' then None else
    Some (make_ite t0 t' e0 e1' e2')
  end.

(* (1) bop (if e then e1a else e2b) (if e then e2a else e2b) --> if e then (bop e1a e2a) else (bop e1b e2b)
   (2) bop (if e1c then e1a else e1b) e2 --> if e1c then (bop e1a e2) else (bop e1b e2)
   (3) bop e1 (if e2c then e2a else e2b) --> if e2c then (bop e1 e2a) else (bop e1 e2b) *)
Definition simpl_bop_ite' {t1 t2 t'} (bop: sastNBM t1 -> sastNBM t2 -> sastNBM t') mvt e1 e2 :=
  match ite_parts e1 with
  | None => simpl_uop_ite' (bop e1) mvt e2
  | Some (existT _ t1c e1c, (e1a,e1b)) =>
    match ite_parts e2 with
    | None => simpl_uop_ite' (fun a => bop a e2) mvt e1
    | Some (existT _ t2c e2c, (e2a,e2b)) =>
      if sastNB_eq e1c e2c then Some (make_ite t1c t' e1c (simpl_dispatch mvt (bop e1a e2a)) (simpl_dispatch mvt (bop e1b e2b)))
      else match simpl_uop_ite' (bop e1) mvt e2 with
      | None => simpl_uop_ite' (fun a => bop a e2) mvt e1
      | e' => e'
      end
    end
  end.

Definition simpl_uop_ite {t t'} (uop: sastNBM t -> sastNBM t') mvt e :=
  match simpl_uop_ite' uop mvt e with None => uop e | Some e' => e' end.

Definition simpl_bop_ite {t1 t2 t'} (bop: sastNBM t1 -> sastNBM t2 -> sastNBM t') mvt e1 e2 :=
  match simpl_bop_ite' bop mvt e1 e2 with None => bop e1 e2 | Some e' => e' end.

Local Ltac Sast_of_typ t :=
  match t with sastN => constr:(NB2NBM SastN) | sastB => constr:(NB2NBM SastB) | sastM => constr:(SastM) end.

Local Ltac make_simpl_ite tac :=
  match goal with
  | [ mvt:metavar_tree |- ?t1 -> ?t2 -> ?t' ] =>
    let s' := Sast_of_typ t' in let s2 := Sast_of_typ t2 in let s1 := Sast_of_typ t1 in
    let e1 := fresh "e" in let e2 := fresh "e" in intros e1 e2;
    refine (@simpl_bop_ite s1 s2 s' _ mvt e1 e2); change (t1 -> t2 -> t'); clear e1 e2;
    let e3 := fresh "e" in let e4 := fresh "e" in intros e3 e4; tac; [exact e3|exact e4]
  | [ mvt:metavar_tree |- ?t -> ?t' ] =>
    let s' := Sast_of_typ t' in let s := Sast_of_typ t in
    let e1 := fresh "e" in intro e;
    refine (@simpl_uop_ite t t' _ mvt e1); change (t -> t'); clear e1;
    let e2 := fresh "e" in intro e2; tac; exact e2
  | [ |- ?t -> _ ] => intro; lazymatch goal with [ x:t |- _ ] => make_simpl_ite ltac:(tac;(only 1:exact x)) end
  end.

Definition simpl_iteN (mvt:metavar_tree) (e:sastN) : sastN.
  case e; revgoals; only 1-2: (intros; exact e);
  let ctrs := numgoals in do ctrs let n := numgoals in only 1:
  solve [ make_simpl_ite ltac:(constructor n) | intros; exact e ].
Defined.

Definition simpl_iteB (mvt:metavar_tree) (e:sastB) : sastB.
  case e; revgoals; only 1-2: (intros; exact e);
  let ctrs := numgoals in do ctrs let n := numgoals in only 1:
  solve [ make_simpl_ite ltac:(constructor n) | intros; exact e ].
Defined.

Definition simpl_iteM (mvt:metavar_tree) (e:sastM) : sastM.
  case e; revgoals; only 1-2: (intros; exact e);
  let ctrs := numgoals in do ctrs let n := numgoals in only 1:
  solve [ make_simpl_ite ltac:(constructor n) | intros; exact e ].
Defined.


(* Simplification main recursion (bottom-up strategy) *)

Fixpoint simpl_sastN (mvt:metavar_tree) (e:sastN) {struct e} : sastN
    with simpl_sastB (mvt:metavar_tree) (e:sastB) {struct e} : sastB
    with simpl_sastM (mvt:metavar_tree) (e:sastM) {struct e} : sastM.

  1: refine (simpl_iteN mvt (simplN_dispatch mvt _)).
  2: refine (simpl_iteB mvt (simplB_dispatch mvt _)).
  3: refine (simpl_iteM mvt (simplM_dispatch mvt _)).
  all: gen_mutual_recursion ltac:(first [ apply (simpl_sastN mvt) | apply (simpl_sastB mvt) | apply (simpl_sastM mvt) ]) e.
  all: intros; exact e.
Defined.
Arguments simpl_sastN mvt !e /.
Arguments simpl_sastB mvt !e /.
Arguments simpl_sastM mvt !e /.

Fixpoint sastS_remove_var v e :=
  match e with
  | SIMP_SVar _ _ => e
  | SIMP_Update s v0 u u' => if v0 == v then sastS_remove_var v s else SIMP_Update (sastS_remove_var v s) v0 u u'
  end.

Fixpoint simpl_sastS e :=
  match e with
  | SIMP_SVar _ _ => e
  | SIMP_Update s v u u' => SIMP_Update (sastS_remove_var v (simpl_sastS s)) v u u'
  end.

Definition simpl_zstore (_:var) := VaN N0 N0.

Fixpoint sastS_find_var v e :=
  match e with
  | SIMP_SVar _ _ => e
  | SIMP_Update s v0 u u' => if v == v0 then SIMP_Update (SIMP_SVar simpl_zstore simpl_zstore) v0 u u' else sastS_find_var v s
  end.

Fixpoint simpl_sastV {A} (t:sastV A) {struct t} : sastV A :=
  match t with
  | SIMP_RetV f f' => SIMP_RetV f f'
  | SIMP_BindV t1 s v => SIMP_BindV (simpl_sastV t1) (sastS_find_var v s) v
  | SIMP_BindS t1 s => SIMP_BindS (simpl_sastV t1) (simpl_sastS s)
  end.

Fixpoint simpl_sastU {A} mvt (t:sastU A) {struct t} : sastU A :=
  match t with
  | SIMP_RetU f f' => SIMP_RetU f f'
  | SIMP_BindN t1 t2 w => SIMP_BindN (simpl_sastU mvt t1) (simpl_sastN mvt t2) w
  | SIMP_BindM t1 t2 mw => SIMP_BindM (simpl_sastU mvt t1) (simpl_sastM mvt t2) mw
  end.


(*** BACK END: OUTPUT ROUTINES ***)

(* After simplification of the SAST, the SAST must be transformed back into a
   Coq expression.  Writing a function to do so is essentially the same as
   defining the denotational semantics of SASTs, except that we must prevent
   tactics like vm_compute from attempting to expand the primitive operator
   that each SAST constructor denotes (which usually results in huge terms
   that are unreadable and can even crash Coq).  We also purposely convert
   some constants as more readable expressions (e.g., constant 4294967296 is
   instead output as the (more readable) expression 2^32). *)

Definition simpl_out_const (noe: forall op, noe_setop_typsig op) n :=
  match n with 0 => 0 | N.pos p =>
    match pos_log2opt p with None => N.pos p | Some n => if n <? 7 then N.pos p else noe NOE_POW 2 n end
  end.
Arguments simpl_out_const noe n / : simpl nomatch.

Fixpoint simpl_outN (noe: forall op, noe_setop_typsig op) mvt e {struct e} : N :=
  match e with
  | SIMP_NVar id n _ _ _ =>
      match id with N0 => n | Npos id =>
        match mvt_lookup mvt id with MVNum n' _ => n' | _ => N0 end
      end
  | SIMP_Const n => simpl_out_const noe n
  | SIMP_Add e1 e2 => noe NOE_ADD (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Sub e1 e2 => noe NOE_SUB (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Mul e1 e2 => noe NOE_MUL (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Mod e1 e2 => noe NOE_MOD (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Pow e1 e2 => noe NOE_POW (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_LAnd e1 e2 => noe NOE_AND (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_LOr e1 e2 => noe NOE_OR (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Xor e1 e2 => noe NOE_XOR (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_ShiftR e1 e2 => noe NOE_SHR (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_ShiftL e1 e2 => noe NOE_SHL (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Popcount e1 => noe NOE_POPCOUNT (simpl_outN noe mvt e1)
  | SIMP_Parity8 e1 => noe NOE_PARITY8 (simpl_outN noe mvt e1)
  | SIMP_GetMem en len m a => (if len =? 1 then id else noe NOE_GET en len) (simpl_outM noe mvt m) (simpl_outN noe mvt a)
  | SIMP_App m a => (simpl_outM noe mvt m) (simpl_outN noe mvt a)
  | SIMP_IteNN e0 e1 e2 => if simpl_outN noe mvt e0 then simpl_outN noe mvt e2 else simpl_outN noe mvt e1
  | SIMP_IteBN e0 e1 e2 => if simpl_outB noe mvt e0 then simpl_outN noe mvt e1 else simpl_outN noe mvt e2
  end
with simpl_outB (noe: forall op, noe_setop_typsig op) mvt e {struct e} : bool :=
  match e with
  | SIMP_BVar id b _ =>
      match id with N0 => b | Npos id =>
        match mvt_lookup mvt id with MVBool b' => b' | _ => true end
      end
  | SIMP_Bool b => b
  | SIMP_Eqb e1 e2 => noe NOE_EQB (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_Ltb e1 e2 => noe NOE_LTB (simpl_outN noe mvt e1) (simpl_outN noe mvt e2)
  | SIMP_BAnd e1 e2 => noe NOE_BAND (simpl_outB noe mvt e1) (simpl_outB noe mvt e2)
  | SIMP_IteNB e0 e1 e2 => if simpl_outN noe mvt e0 then simpl_outB noe mvt e2 else simpl_outB noe mvt e1
  | SIMP_IteBB e0 e1 e2 => if simpl_outB noe mvt e0 then simpl_outB noe mvt e1 else simpl_outB noe mvt e2
  end
with simpl_outM (noe: forall op, noe_setop_typsig op) mvt e {struct e} : addr -> N :=
  match e with
  | SIMP_MVar id m _ _ _ =>
      match id with N0 => m | Npos id =>
        match mvt_lookup mvt id with MVMem m' _ => m' | _ => zeromem end
      end
  | SIMP_SetMem en len m a n => noe NOE_SET en len (simpl_outM noe mvt m) (simpl_outN noe mvt a) (simpl_outN noe mvt n)
  | SIMP_IteNM e0 e1 e2 => if simpl_outN noe mvt e0 then simpl_outM noe mvt e2 else simpl_outM noe mvt e1
  | SIMP_IteBM e0 e1 e2 => if simpl_outB noe mvt e0 then simpl_outM noe mvt e1 else simpl_outM noe mvt e2
  end.

Fixpoint simpl_outS (noe: forall op, noe_typop_typsig op) e :=
  match e with
  | SIMP_SVar s _ => s
  | SIMP_Update s v u _ => noe NOE_UPD (simpl_outS noe s) v u
  end.

Fixpoint simpl_outV {A} (noe: forall op, noe_typop_typsig op) (t: sastV A) : A :=
  match t with
  | SIMP_RetV f _ => f
  | SIMP_BindV t1 t2 v => simpl_outV noe t1
      (match t2 with
       | SIMP_SVar s _ => s
       | SIMP_Update s0 v0 u _ => update (simpl_outS noe s0) v0 u
       end v)
  | SIMP_BindS t1 t2 => simpl_outV noe t1 (simpl_outS noe t2)
  end.

Fixpoint simpl_outU {A} noe mvt (t: sastU A) : A :=
  match t with
  | SIMP_RetU f _ => f
  | SIMP_BindN t1 t2 w => simpl_outU noe mvt t1 (VaN (simpl_outN noe mvt t2) w)
  | SIMP_BindM t1 t2 mw => simpl_outU noe mvt t1 (VaM (simpl_outM noe mvt t2) mw)
  end.

Definition simpl_N u := match u with VaN n _ => n | VaM _ _ => N0 end.
Definition simpl_exit u := Exit (simpl_N u).
Definition simpl_MemAcc P h s u := MemAcc P h s (simpl_N u).
Definition simpl_if (u:value) (q1 q2:stmt) := if simpl_N u then q1 else q2.

End PSIMPL_DEFS_V1_1.



(* The exported interface of the simplifier includes all the definitions from
   PSIMPL_DEFS_* above, plus definitions of the tactics invoked by PSimplifier
   (see Picinae_simplifier_base.v), along with type signatures of any theorems
   those tactics apply. *)

Module Type PICINAE_SIMPLIFIER_V1_1
  (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL).

Import IL.
Import TIL.
Import FIL.
Include PSIMPL_DEFS_V1_1 IL TIL FIL.

Parameter simplify_sastN_hyp:
  forall (x e:N) (noe: forall op, noe_setop_typsig op) (mvt:metavar_tree) (t:sastN)
         (NOE: noe = noe_setop) (H': e = eval_sastN mvt t) (H: x = e),
  x = simpl_outN noe mvt (simpl_sastN mvt t).
Parameter simplify_sastB_hyp:
  forall (x e:bool) (noe: forall op, noe_setop_typsig op) (mvt:metavar_tree) (t:sastB)
         (NOE: noe = noe_setop) (H': e = eval_sastB mvt t) (H: x = e),
  x = simpl_outB noe mvt (simpl_sastB mvt t).
Parameter simplify_sastM_hyp:
  forall (x e: addr -> N) (noe: forall op, noe_setop_typsig op) (mvt:metavar_tree) (t:sastM)
         (NOE: noe = noe_setop) (H': e = eval_sastM mvt t) (H: x = e),
  x = simpl_outM noe mvt (simpl_sastM mvt t).
Parameter simplify_sastV_hyp:
  forall {P:Prop} (noe: forall op, noe_typop_typsig op) (t:sastV Prop)
    (NOE: noe = noe_typop) (H': P = eval_sastV t) (H:P),
  simpl_outV noe (simpl_sastV t).
Parameter simplify_sastU_hyp:
  forall {P:Prop} (noe: forall op, noe_setop_typsig op) (mvt:metavar_tree) (t:sastU Prop)
    (NOE: noe = noe_setop) (H': P = eval_sastU mvt t) (H:P),
  simpl_outU noe mvt (simpl_sastU mvt t).
Parameter simplify_sastV_goal:
  forall {P:Prop} (noe: forall op, noe_typop_typsig op) (t:sastV Prop)
    (G': simpl_outV noe (simpl_sastV t)) (NOE: noe = noe_typop) (H': P = eval_sastV t),
  P.
Parameter simplify_sastU_goal:
  forall {P:Prop} (noe: forall op, noe_setop_typsig op) (mvt:metavar_tree) (t:sastU Prop)
    (G': simpl_outU noe mvt (simpl_sastU mvt t)) (NOE: noe = noe_setop) (H': P = eval_sastU mvt t),
  P.

Parameter N_shiftl1_pow2: forall {n w:N} (H: n < N.shiftl 1 w), n < 2^w.
Parameter simpl_if_if: forall (b:bool) (q1 q2:stmt),
  (if (if b then 1 else N0) then q1 else q2) = (if b then q2 else q1).
Parameter simpl_if_not_if:
  forall (b:bool) (q1 q2:stmt),
  (if (N.lnot (if b then 1 else N0) 1) then q1 else q2) = (if b then q1 else q2).




(*** FRONT END: PARSING ***)

(* The following tactics recursively parse Coq expressions and yield SASTs with
   equivalent denotations.  Since we cannot prove these correct in general (and
   an incorrect implementation results in an error at proof-time that users are
   unlikely to comprehend), these tactic implementations are delicate.  Each case
   must yield an SAST whose denotation Coq sees as "obviously" equal to the
   original (i.e., it unifies with the original term via only Coq's basic term
   reduction strategies).

   While we cannot prove general correctness (since Coq checks tactic output at
   application-time not definition-time), we can at least spot-check the tactic
   implementation.  If you add a case to this definition, please also add a case
   to the spot-checker that follows it! *)

Local Ltac sastN_gen n :=
  let rec mvar_or_const m :=
    lazymatch m with
    | N0 => uconstr:(SIMP_Const n)
    | Npos ?p => mvar_or_const p
    | xI ?p => mvar_or_const p
    | xO ?p => mvar_or_const p
    | xH => uconstr:(SIMP_Const n)
    | _ => uconstr:(SIMP_NVar N0 n SIMP_UBND N0 SIMP_UBND)
    end
  in lazymatch n with
  | N.add ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Add t1 t2)
  | N.sub ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Sub t1 t2)
  | N.mul ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Mul t1 t2)
  | N.modulo ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Mod t1 t2)
  | N.land ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_LAnd t1 t2)
  | N.lor ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_LOr t1 t2)
  | N.lxor ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Xor t1 t2)
  | N.shiftr ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_ShiftR t1 t2)
  | N.shiftl ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_ShiftL t1 t2)
  | N.pow ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Pow t1 t2)
  | (match ?n0 with N0 => ?n2 | N.pos _ => ?n1 end) =>
      let t0 := sastN_gen n0 in let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_IteNN t0 t1 t2)
  | (match ?b with true => ?n1 | false => ?n2 end) =>
      let t0 := sastB_gen b in let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_IteBN t0 t1 t2)
  | getmem ?en ?len ?m ?a => let t1 := sastM_gen m in let t2 := sastN_gen a in uconstr:(SIMP_GetMem en len t1 t2)
  | popcount ?n1 => let t := sastN_gen n1 in uconstr:(SIMP_Popcount t)
  | N.lnot ((N.lxor (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr ?n1 4) ?n1) 2)
                                      (N.lxor (N.shiftr ?n1 4) ?n1)) 1)
                    (N.lxor (N.shiftr (N.lxor (N.shiftr ?n1 4) ?n1) 2)
                            (N.lxor (N.shiftr ?n1 4) ?n1))) mod 2^1) 1 =>
      let t := sastN_gen n1 in uconstr:(SIMP_Parity8 t)
  | ?m ?a => lazymatch type of m with addr -> N =>
               let t1 := sastM_gen m in let t2 := sastN_gen a in uconstr:(SIMP_App t1 t2)
             | _ => mvar_or_const n
             end
  | _ => mvar_or_const n
  end
with sastB_gen b :=
  lazymatch b with
  | N.eqb ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Eqb t1 t2)
  | N.ltb ?n1 ?n2 => let t1 := sastN_gen n1 in let t2 := sastN_gen n2 in uconstr:(SIMP_Ltb t1 t2)
  | andb ?b1 ?b2 => let t1 := sastB_gen b1 in let t2 := sastB_gen b2 in uconstr:(SIMP_BAnd t1 t2)
  | (match ?n with N0 => ?b2 | N.pos _ => ?b1 end) =>
      let t0 := sastN_gen n in let t1 := sastB_gen b1 in let t2 := sastB_gen b2 in uconstr:(SIMP_IteNB t0 t1 t2)
  | (match ?b1 with true => ?b2 | false => ?b3 end) =>
      let t1 := sastB_gen b1 in let t2 := sastB_gen b2 in let t3 := sastB_gen b3 in uconstr:(SIMP_IteBB t1 t2 t3)
  | _ => uconstr:(SIMP_BVar N0 b true)
  end
with sastM_gen m :=
  lazymatch m with
  | setmem ?en ?len ?m ?a ?n => let t1 := sastM_gen m in let t2 := sastN_gen a in let t3 := sastN_gen n in
                                uconstr:(SIMP_SetMem en len t1 t2 t3)
  | (match ?n with N0 => ?m2 | N.pos _ => ?m1 end) =>
      let t0 := sastN_gen n in let t1 := sastM_gen m1 in let t2 := sastM_gen m2 in uconstr:(SIMP_IteNM t0 t1 t2)
  | (match ?b with true => ?m1 | false => ?m2 end) =>
      let t0 := sastB_gen b in let t1 := sastM_gen m1 in let t2 := sastM_gen m2 in uconstr:(SIMP_IteBM t0 t1 t2)
  | _ => uconstr:(SIMP_MVar N0 m None zeromem None)
  end.

(* The following unnamed theorem spot-checks the front end parser by testing whether
   Coq indeed unifies its output with its input, for each basic input expression.
   If you add a new SAST constructor and extend the front end above to parse it,
   please add a check for it in the proof below! *)

Section CheckFrontEnd.

  Local Ltac check e := lazymatch type of e with
  | N       => let t := sastN_gen e in unify (eval_sastN (make_mvtN t) t) e
  | bool    => let t := sastB_gen e in unify (eval_sastB (make_mvtB t) t) e
  | addr->N => let t := sastM_gen e in unify (eval_sastM (make_mvtM t) t) e
  | ?t => fail "cannot parse type" t
  end.

  Goal forall (n1 n2 n3 n4:N) (b1 b2 b3:bool) (en:endianness) (m1 m2:addr->N), True.
  Proof.
    intros.

    (* numeric SAST checks *)
    check (n1).
    check (N.add n1 n2).
    check (N.sub n1 n2).
    check (N.mul n1 n2).
    check (N.modulo n1 n2).
    check (N.land n1 n2).
    check (N.lor n1 n2).
    check (N.lxor n1 n2).
    check (N.shiftr n1 n2).
    check (N.shiftl n1 n2).
    check (N.pow 2 n2).
    check (if n1 then n2 else n3).
    check (if b1 then n1 else n2).
    check (getmem en n1 m1 n2).
    check (popcount n1).
    check (parity8 n1).
    check (N.lnot ((N.lxor (N.shiftr (N.lxor (N.shiftr (N.lxor (N.shiftr n1 4) n1) 2)
                                             (N.lxor (N.shiftr n1 4) n1)) 1)
                           (N.lxor (N.shiftr (N.lxor (N.shiftr n1 4) n1) 2)
                                   (N.lxor (N.shiftr n1 4) n1))) mod 2^1) 1).
    check (m1 n1).

    (* boolean SAST checks *)
    check (b1).
    check (n1 =? n2).
    check (n1 <? n2).
    check (andb b1 b2).
    check (if n1 then b1 else b2).
    check (if b1 then b2 else b3).

    (* memory SAST checks *)
    check (m1).
    check (setmem en n1 m1 n2 n3).
    check (if n1 then m1 else m2).
    check (if b1 then m1 else m2).

    all: let g := numgoals in guard g=1; solve [ exact I ].
  Abort. (* Don't actually add the unnamed theorem to the module type. *)

End CheckFrontEnd.

(* The following tactics accept Coq terms as input and return SAST terms.  The
   returned term is untyped since it contains Coq existential variables.  It must
   therefore be used in a tactic that can introduce existentials to the proof
   context (e.g., epose or refine). *)

Local Ltac sastS_gen _s :=
  lazymatch _s with
  | update ?s0 ?v ?_u => let t := sastS_gen s0 in uconstr:(SIMP_Update t v ?[?u] _u)
  | _ => uconstr:(SIMP_SVar ?[?s] _s)
  end.

Local Ltac sastV_gen e :=
  lazymatch e with
  | context [ @update var value ?eq ?s ?v ?u ?v' ] => lazymatch eval pattern (@update var value eq s v u v') in e with ?f _ =>
      let f' := sastV_gen f in let t := sastS_gen (@update var value eq s v u) in uconstr:(SIMP_BindV f' t v')
    end
  | context [ @update var value ?eq ?s ?v ?u ] => lazymatch eval pattern (@update var value eq s v u) in e with ?f _ =>
      let f' := sastV_gen f in let t := sastS_gen (@update var value eq s v u) in uconstr:(SIMP_BindS f' t)
    end
  | _ => uconstr:(SIMP_RetV ?[?f] e)
  end.

Local Ltac sastU_gen e :=
  let rec mark_simpl e :=
    lazymatch e with
    | context c [ exec_stmt ?h ?s (if ?n then ?q1 else ?q2) ?s' ?x ] =>
      let e' := context c [ exec_stmt h s (simpl_if (VaN n 1) q1 q2) s' x ] in mark_simpl e'
    | context c [ Exit ?a ] =>
      let e' := context c [ simpl_exit (VaN a 1) ] in mark_simpl e'
    | context c [ MemAcc ?P ?h ?s ?a ] =>
      let e' := context c [ simpl_MemAcc P h s (VaN a 1) ] in mark_simpl e'
    | _ => e
    end in
  let rec to_ast e :=
    lazymatch e with
    | context [ VaN ?n (N.pos ?w) ] => lazymatch eval pattern (VaN n (N.pos w)) in e with ?f _ =>
        let f' := to_ast f in let t := sastN_gen n in uconstr:(SIMP_BindN f' t (N.pos w))
      end
    | context [ VaM ?m (N.pos ?mw) ] => lazymatch eval pattern (VaM m (N.pos mw)) in e with ?f _ =>
        let f' := to_ast f in let t := sastM_gen m in uconstr:(SIMP_BindM f' t (N.pos mw))
      end
    | _ => uconstr:(SIMP_RetU ?[?f] e)
    end in
  let e' := mark_simpl e in to_ast e'.

(* The populate_var_ids accepts an SAST generated by the tactics above, which
   assign all metavars identifiers of zero, and search them for common metavar
   subterms, to which each is assigned a unique, common, non-zero identifier.
   It also scans the proof context for any proofs of boundedness (for numeric
   metavars) or well-typedness (for memory metavars) that can be added to
   their arguments to aid in later simplification. *)

Local Ltac pos_log2_pow2 p :=
  lazymatch p with
  | xH => uconstr:(N0)
  | xO ?q => let n := pos_log2_pow2 q in uconstr:(N.succ n)
  end.

Local Ltac populate_var_ids id t :=
  lazymatch t with
  | context [ SIMP_NVar N0 ?_n SIMP_UBND N0 SIMP_UBND ] =>
    let id' := (eval cbv in (N.succ id)) in
    let x := match goal with
    | [ H: _n < 2^?w |- _ ] =>
      uconstr:(SIMP_NVar id' ?[?n] (SIMP_BND w ?[?BND]) _n (SIMP_BND w H))
    | [ H: _n < N.shiftl 1 ?w |- _ ] =>
      uconstr:(SIMP_NVar id' ?[?n] (SIMP_BND w ?[?BND]) _n (SIMP_BND w (N_shiftl1_pow2 H)))
    | [ H: _n < N.pos ?p |- _ ] =>
      let m := pos_log2_pow2 p in let w := (eval cbv in m) in
      uconstr:(SIMP_NVar id' ?[?n] (SIMP_BND w ?[?BND]) _n (SIMP_BND w H))
    | [ H: ?s ?v = VaN _n ?w, M: models ?c ?s |- _ ] =>
      let a := constr:(@SIMP_BND _n w (models_regsize v M H)) in
      uconstr:(SIMP_NVar id' ?[?n] (SIMP_BND w ?[?BND]) _n a)
    | _ => uconstr:(SIMP_NVar id' ?[?n] SIMP_UBND _n SIMP_UBND)
    end in
    lazymatch eval pattern (SIMP_NVar N0 _n SIMP_UBND N0 SIMP_UBND) in t with ?f _ =>
      let t' := populate_var_ids id' f in uconstr:(t' x)
    end
  | context [ SIMP_BVar N0 ?_b true ] =>
    let id' := (eval cbv in (N.succ id)) in
    lazymatch eval pattern (SIMP_BVar N0 _b true) in t with ?f _ =>
      let t' := populate_var_ids id' f in uconstr:(t' (SIMP_BVar id' ?[?b] _b))
    end
  | context [ SIMP_MVar N0 ?_m None zeromem None ] =>
    let id' := (eval cbv in (N.succ id)) in
    let x := match goal with
    | [ H: welltyped_memory _m |- _ ] =>
      uconstr:(SIMP_MVar id' ?[?m] (Some ?[?WTM]) _m (Some H))
    | [ H: ?s ?v = VaM _m ?mw, M: models ?c ?s |- _ ] =>
      let a := constr:(@Some (welltyped_memory _m) (models_wtm v M H)) in
      uconstr:(SIMP_MVar id' ?[?m] (Some ?[?WTM]) _m a)
    | _ => uconstr:(SIMP_MVar id' ?[?m] None _m None)
    end in
    lazymatch eval pattern (SIMP_MVar N0 _m None zeromem None) in t with ?f _ =>
      let t' := populate_var_ids id' f in uconstr:(t' x)
    end
  | _ => uconstr:(t) end.

Local Ltac psimp_verify_frontend :=
  cbv [ eval_sastV eval_sastS eval_sastU eval_sastN eval_sastB eval_sastM mvt_lookup simpl_N simpl_exit simpl_MemAcc simpl_if parity8 ];
  lazymatch goal with
  | |- ?t = ?t => exact_no_check (eq_refl t)
  | |- ?t1 = ?t2 => (* DEBUG *)
    idtac "***** frontend verification needing optimization *****";
    idtac "T1:" t1; idtac "T2:" t2;
    reflexivity
  end.

Local Ltac psimpl_hyp_with _simpl_evars _make_mvt _simplify_sast_hyp t H :=
  let t2 := eval lazy [t simpl_evarsN simpl_evarsB simpl_evarsM] in (_simpl_evars t) in
  let mvt := eval compute in (_make_mvt t2) in
  eapply (_simplify_sast_hyp _ _ _ mvt t2) in H;
  [ compute in H
  | unify t t2; reflexivity
  | psimp_verify_frontend ].

Local Ltac psimplN_hyp := psimpl_hyp_with simpl_evarsN make_mvtN simplify_sastN_hyp.
Local Ltac psimplB_hyp := psimpl_hyp_with simpl_evarsB make_mvtB simplify_sastB_hyp.
Local Ltac psimplM_hyp := psimpl_hyp_with simpl_evarsM make_mvtM simplify_sastM_hyp.

Local Ltac psimplV_hyp t H :=
  let t2 := eval lazy [t simpl_evarsV simpl_evarsS] in (simpl_evarsV t) in
  eapply (simplify_sastV_hyp _ t2) in H;
  [ compute in H
  | unify t t2; reflexivity
  | psimp_verify_frontend ].
Local Ltac psimplV_goal t :=
  let t2 := eval lazy [t simpl_evarsV simpl_evarsS] in (simpl_evarsV t) in
  eapply (simplify_sastV_goal _ t2);
  [ compute
  | unify t t2; reflexivity
  | psimp_verify_frontend ].
Local Ltac psimplU_hyp t H :=
  let t2 := eval lazy [t simpl_evarsU simpl_evarsN simpl_evarsB simpl_evarsM] in (simpl_evarsU t) in
  let mvt := eval compute in (make_mvtU t2) in
  eapply (simplify_sastU_hyp _ mvt t2) in H;
  [ compute in H
  | unify t t2; reflexivity
  | psimp_verify_frontend ].
Local Ltac psimplU_goal t :=
  let t2 := eval lazy [t simpl_evarsU simpl_evarsN simpl_evarsB simpl_evarsM] in (simpl_evarsU t) in
  let mvt := eval compute in (make_mvtU t2) in
  eapply (simplify_sastU_goal _ mvt t2);
  [ compute
  | unify t t2; reflexivity
  | psimp_verify_frontend ].

Local Ltac psimplNBM_exhyp H := cbv beta match delta [noe_setop] in H.
Local Ltac psimplNBM_exgoal := cbv beta match delta [noe_setop].
Local Ltac psimplV_exhyp H := cbv beta match delta [noe_typop] in H.
Local Ltac psimplV_exgoal := cbv beta match delta [noe_typop].
Local Ltac psimplU_exhyp H :=
  cbv beta match delta [noe_setop simpl_N simpl_exit simpl_MemAcc simpl_if] in H;
  rewrite 1?simpl_if_if, 1?simpl_if_not_if in H.
Local Ltac psimplU_exgoal :=
  cbv beta match delta [noe_setop simpl_N simpl_exit simpl_MemAcc simpl_if];
  rewrite 1?simpl_if_if, 1?simpl_if_not_if.

Ltac PSimplifier tac :=
  lazymatch tac with
  | PSIMPL_GENN => sastN_gen
  | PSIMPL_GENB => sastB_gen
  | PSIMPL_GENM => sastM_gen
  | PSIMPL_GENV => sastV_gen
  | PSIMPL_GENU => sastU_gen
  | PSIMPL_POPULATE_VAR_IDS => populate_var_ids
  | PSIMPL_N_HYP => psimplN_hyp
  | PSIMPL_B_HYP => psimplB_hyp
  | PSIMPL_M_HYP => psimplM_hyp
  | PSIMPL_V_HYP => psimplV_hyp
  | PSIMPL_V_GOAL => psimplV_goal
  | PSIMPL_U_HYP => psimplU_hyp
  | PSIMPL_U_GOAL => psimplU_goal
  | PSIMPL_EXHYP_N => psimplNBM_exhyp
  | PSIMPL_EXGOAL_N => psimplNBM_exgoal
  | PSIMPL_EXHYP_B => psimplNBM_exhyp
  | PSIMPL_EXGOAL_B => psimplNBM_exgoal
  | PSIMPL_EXHYP_M => psimplNBM_exhyp
  | PSIMPL_EXGOAL_M => psimplNBM_exgoal
  | PSIMPL_EXHYP_V => psimplV_exhyp
  | PSIMPL_EXGOAL_V => psimplV_exgoal
  | PSIMPL_EXHYP_U => psimplU_exhyp
  | PSIMPL_EXGOAL_U => psimplU_exgoal
  end.

End PICINAE_SIMPLIFIER_V1_1.



(* The module definition proves the theorems declared in PICINAE_SIMPLIFIER_*,
   which entails proving soundness of all the simplification procedures defined
   in PSIMPL_DEFS_*.  (There is no need to restate the tactic definitions,
   since those are drawn from the module type when the module is loaded and Coq
   doesn't require that the module body reiterate them.) *)

Module Picinae_Simplifier_v1_1
  (IL: PICINAE_IL) (TIL: PICINAE_STATICS IL) (FIL: PICINAE_FINTERP IL TIL) : PICINAE_SIMPLIFIER_V1_1 IL TIL FIL.

Import IL.
Import TIL.
Import FIL.
Include PSIMPL_DEFS_V1_1 IL TIL FIL.
Module PTheory := PicinaeTheory IL.
Import PTheory.


(* Proof of soundness for SAST-equivalence algorithm *)

Theorem endianness_eq_sound:
  forall en1 en2, endianness_eq en1 en2 = true -> en1 = en2.
Proof.
  destruct en1, en2; first [ reflexivity | discriminate ].
Qed.

Theorem sast_eq_sound:
  forall f,
    (forall e1 e2 (AEQ: sastN_eq e1 e2 = true), eval_sastN f e1 = eval_sastN f e2) /\
    (forall e1 e2 (AEQ: sastB_eq e1 e2 = true), eval_sastB f e1 = eval_sastB f e2) /\
    (forall e1 e2 (AEQ: sastM_eq e1 e2 = true), eval_sastM f e1 = eval_sastM f e2).
Proof.
  intro. apply sast_mind; intros;
  match type of AEQ with sastN_eq _ ?e = true => destruct e; try discriminate AEQ
                       | sastB_eq _ ?e = true => destruct e; try discriminate AEQ
                       | sastM_eq _ ?e = true => destruct e; try discriminate AEQ end;
  solve
  [ destruct id as [|id]; [|destruct id0 as [|id0]];
    [ discriminate.. | apply Pos.eqb_eq in AEQ; subst id0; reflexivity ]
  | simpl in AEQ |- *; repeat (apply andb_prop in AEQ; destruct AEQ as [? AEQ]);
    repeat match goal with

    (* NOTE: For each type of SAST constructor argument, include a case here that
       proves soundness of its equality decision procedure: *)
    | [ H: endianness_eq _ _ = true |- _ ] => apply endianness_eq_sound in H
    | [ H: N.eqb _ _ = true |- _ ] => apply N.eqb_eq in H
    | [ H: Bool.eqb _ _ = true |- _ ] => apply Bool.eqb_prop in H

    | [ IH: forall e, _ -> _ = _ |- _ ] => erewrite IH by eassumption; clear IH
    end;
    subst; reflexivity
  ].
Qed.

Definition sastN_eq_sound f := proj1 (sast_eq_sound f).
Definition sastB_eq_sound f := proj1 (proj2 (sast_eq_sound f)).
Definition sastM_eq_sound f := proj2 (proj2 (sast_eq_sound f)).

(* Proof of soundness for SAST bounds algorithm *)

Lemma N_mod_0_r: forall n, n mod 0 = n.
Proof. destruct n; reflexivity. Qed.

Lemma N_mod_le: forall m n, m mod n <= m.
Proof. destruct n. rewrite N_mod_0_r. reflexivity. apply N.mod_le. discriminate. Qed.

Lemma N_size_injle: forall m n, m <= n -> N.size m <= N.size n.
Proof.
  intros. destruct m as [|m]. apply N.le_0_l. destruct n as [|n].
    apply N.le_0_r in H. rewrite H. reflexivity.
    rewrite !N.size_log2 by discriminate. apply (proj1 (N.succ_le_mono _ _)), N.log2_le_mono, H.
Qed.

Theorem simpl_bounds_sound:
  forall mvt e, match simpl_bounds mvt e with (lo,ohi) =>
    lo <= eval_sastN mvt e /\ match ohi with None => True | Some hi => eval_sastN mvt e <= hi end
  end.
Proof.
  induction e; simpl;
  try destruct (simpl_bounds mvt e1) as (lo1,ohi1); try destruct (simpl_bounds mvt e2) as (lo2,ohi2).

  (* NVar *)
  destruct id as [|id]. split. apply N.le_0_l. exact I.
  split. apply N.le_0_l. destruct (mvt_lookup mvt id); try exact I. destruct bnd.
    exact I.
    rewrite N.ones_equiv. apply N.lt_le_pred. assumption.

  (* Const *)
  split; reflexivity.

  (* Add *) split.
  apply N.add_le_mono. apply IHe1. apply IHe2.
  destruct ohi1; [|exact I]. destruct ohi2; [|exact I]. apply N.add_le_mono. apply IHe1. apply IHe2.

  (* Sub *) split.
  destruct ohi2.
    etransitivity. apply N.sub_le_mono_r, IHe1. apply N.sub_le_mono_l, IHe2.
    apply N.le_0_l.
  destruct ohi1.
    etransitivity. apply N.sub_le_mono_r, IHe1. apply N.sub_le_mono_l, IHe2.
    exact I.

  (* Mul *) split.
  apply N.mul_le_mono. apply IHe1. apply IHe2.
  destruct ohi1; [|exact I]. destruct ohi2; [|exact I]. apply N.mul_le_mono. apply IHe1. apply IHe2.

  (* Mod *)
  destruct lo2 as [|lo2].
    split. apply N.le_0_l. destruct ohi1 as [hi1|]; [|exact I]. etransitivity.
      apply N_mod_le.
      apply IHe1.
    destruct ohi1 as [hi1|]; split.
      destruct (_<?_) eqn:H.
        rewrite N.mod_small. apply IHe1. eapply N.le_lt_trans. apply IHe1. eapply N.lt_le_trans.
          apply N.ltb_lt, H.
          apply IHe2.
        apply N.le_0_l.
      destruct ohi2 as [hi2|].
        apply N.min_glb.
          etransitivity. apply N_mod_le. apply IHe1.
          eapply N.lt_le_pred, N.lt_le_trans.
            eapply N.mod_lt, N.neq_0_lt_0, N.lt_le_trans; [|apply IHe2]. reflexivity.
            apply IHe2.
        etransitivity. apply N_mod_le. apply IHe1.
      apply N.le_0_l.
      destruct ohi2 as [hi2|]; [|exact I]. eapply N.lt_le_pred, N.lt_le_trans.
        eapply N.mod_lt, N.neq_0_lt_0, N.lt_le_trans; [|apply IHe2]. reflexivity.
        apply IHe2.

  (* Pow *)
  destruct lo1; split.
    apply N.le_0_l.
    destruct ohi1 as [hi1|]; destruct ohi2 as [hi2|]; simpl; try exact I. destruct (eval_sastN mvt e1).
      destruct (eval_sastN mvt e2). apply N.le_max_l. rewrite N.pow_0_l. apply N.le_0_l. discriminate.
      etransitivity; [|apply N.le_max_r]. apply N.pow_le_mono. discriminate. apply IHe1. apply IHe2.
    apply N.pow_le_mono. discriminate. apply IHe1. apply IHe2.
    destruct ohi1 as [hi1|]; [|exact I]. destruct ohi2 as [hi2|]; [|exact I]. apply N.pow_le_mono.
      eapply N.neq_0_lt_0, N.lt_le_trans; [|apply IHe1]. reflexivity.
      apply IHe1.
      apply IHe2.

  (* And, Or, Xor *)
  1-3: split; [ apply N.le_0_l | destruct ohi1 as [hi1|]; [destruct ohi2 as [hi2|]; [|exact I] | exact I] ].
  1-3: rewrite N.ones_equiv; apply N.lt_le_pred.
  destruct (N.min_dec (N.size hi1) (N.size hi2)).
    rewrite e. eapply land_bound, N.le_lt_trans. apply IHe1. apply N.size_gt.
    rewrite e, N.land_comm. eapply land_bound, N.le_lt_trans. apply IHe2. apply N.size_gt.
  1-2: first [ apply lor_bound | apply lxor_bound ];
       (destruct (N.le_ge_cases hi1 hi2); [ rewrite (N.max_r _ _ (N_size_injle _ _ H)) | rewrite (N.max_l _ _ (N_size_injle _ _ H)) ]);
       (eapply N.le_lt_trans; [ first [ apply IHe1 | apply IHe2 ] | first [ apply N.size_gt | eapply N.le_lt_trans; [ apply H | apply N.size_gt ] ] ]).

  (* ShiftR *)
  destruct ohi2 as [hi2|]; (split; [|destruct ohi1 as [hi1|]; [|exact I]]); simpl; rewrite !N.shiftr_div_pow2; first
  [ apply N.le_0_l
  | etransitivity;
    [ apply N.div_le_mono; [ apply N.pow_nonzero; discriminate | apply IHe1 ]
    | apply N.div_le_compat_l; split; [ apply Nlt_0_pow2 | apply N.pow_le_mono_r; [ discriminate | apply IHe2 ] ] ] ].

  (* ShiftL *) split.
  rewrite !N.shiftl_mul_pow2. apply N.mul_le_mono.
    apply IHe1.
    apply N.pow_le_mono_r. discriminate. apply IHe2.
  destruct ohi1 as [hi1|]; [|exact I]. destruct ohi2 as [hi2|]; [|exact I]. simpl. rewrite !N.shiftl_mul_pow2. apply N.mul_le_mono.
    apply IHe1.
    apply N.pow_le_mono_r. discriminate. apply IHe2.

  (* Popcount *)
  split.
    apply N.le_0_l.
    destruct simpl_bounds as (lo,[hi|]).
      simpl. etransitivity. apply popcount_bound. apply N_size_injle, IHe.
      exact I.

  (* Parity8 *)
  split.
    apply N.le_0_l.
    apply (N.lt_succ_r _ 1), (lxor_bound 1). apply N.mod_lt. discriminate. reflexivity.

  (* GetMem *)
  split. apply N.le_0_l. destruct m as [[|id] ? ? ? ?| | |]; try exact I.
  simpl. destruct (mvt_lookup mvt id) as [| |? [wtm1|]]; try exact I.
  rewrite N.ones_equiv. apply N.lt_le_pred, getmem_bound, wtm1.

  (* App *)
  split. apply N.le_0_l. destruct m as [[|id] ? ? ? ?| | |]; try exact I.
  simpl. destruct (mvt_lookup mvt id) as [| |? [wtm1|]]; try exact I.
  rewrite N.ones_equiv. apply N.lt_le_pred, wtm1.

  (* IteNN *)
  destruct (simpl_bounds mvt e3) as (lo3,ohi3). split.
    destruct (eval_sastN mvt e1).
      etransitivity; [|apply IHe3]. apply N.le_min_r.
      etransitivity; [|apply IHe2]. apply N.le_min_l.
    destruct ohi2; [|exact I]. destruct ohi3; [|exact I]. simpl. destruct (eval_sastN mvt e1).
      etransitivity. apply IHe3. apply N.le_max_r.
      etransitivity. apply IHe2. apply N.le_max_l.

  (* IteBN *)
  destruct (simpl_bounds mvt e3) as (lo3,ohi3). split.
    destruct (eval_sastB mvt e1).
      etransitivity; [|apply IHe1]. apply N.le_min_l.
      etransitivity; [|apply IHe2]. apply N.le_min_r.
    destruct ohi2; [|exact I]. destruct ohi3; [|exact I]. simpl. destruct (eval_sastB mvt e1).
      etransitivity. apply IHe1. apply N.le_max_l.
      etransitivity. apply IHe2. apply N.le_max_r.
Qed.

Corollary sastN_le_sound:
  forall mvt e1 e2, sastN_le mvt e1 e2 = true -> eval_sastN mvt e1 <= eval_sastN mvt e2.
Proof.
  unfold sastN_le. intros.
  assert (SB1:=simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,[hi1|]); [|discriminate].
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).
  etransitivity. apply SB1. etransitivity. apply N.leb_le, H. apply SB2.
Qed.

Corollary sastN_lt_sound:
  forall mvt e1 e2, sastN_lt mvt e1 e2 = true -> eval_sastN mvt e1 < eval_sastN mvt e2.
Proof.
  unfold sastN_lt. intros.
  assert (SB1:=simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,[hi1|]); [|discriminate].
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).
  eapply N.le_lt_trans. apply SB1. eapply N.lt_le_trans. apply N.ltb_lt, H. apply SB2.
Qed.

(* Proof of soundness for multiple_of_pow2 decision algorithm *)

Theorem pos_log2opt_sound:
  forall p n, pos_log2opt p = Some n -> N.pos p = 2^n.
Proof.
  induction p; intros.
    discriminate.
    simpl in H. destruct pos_log2opt as [m|]; [|discriminate]. inversion H. rewrite N.pow_succ_r'. rewrite <- IHp; reflexivity.
    inversion H. reflexivity.
Qed.

Lemma mop2_land_sound:
  forall n n1 n2, N.land (2^n * n1) n2 = 2^n * (N.land n1 (N.shiftr n2 n)).
Proof.
  intros.
  do 2 rewrite N.mul_comm, <- N.shiftl_mul_pow2.
  rewrite N.shiftl_land, <- N.ldiff_ones_r.
  apply N.bits_inj. intro i. rewrite !N.land_spec, N.ldiff_spec. destruct (N.le_gt_cases n i).
    rewrite N.ones_spec_high, Bool.andb_true_r by assumption. reflexivity.
    rewrite N.shiftl_spec_low by assumption. reflexivity.
Qed.

Theorem mop2_sound:
  forall mvt e n, multiple_of_pow2 mvt e n = true -> exists m, eval_sastN mvt e = 2^n * m.
Proof.
  induction e; try rename n into n1; intro n; intros;
  (destruct n as [|p]; [eexists; rewrite N.mul_1_l; reflexivity | ]);
  simpl eval_sastN; try first
  [ discriminate
  | simpl multiple_of_pow2 in H; apply andb_prop in H; specialize (IHe1 (N.pos p) (proj1 H)); specialize (IHe2 (N.pos p) (proj2 H));
    destruct IHe1 as [m1 H1]; destruct IHe2 as [m2 H2]
  | simpl multiple_of_pow2 in H; apply Bool.orb_prop in H ].

  (* Const *)
  destruct n1.
    exists 0. rewrite N.mul_0_r. reflexivity.
    assert (H1:=pos_log2opt_sound p0). simpl in H. destruct (pos_log2opt p0).
      exists (2^(n-N.pos p)). rewrite (H1 _ (eq_refl _)), <- N.pow_add_r, N.add_sub_assoc.
        rewrite N.add_comm, N.add_sub. reflexivity.
        apply N.leb_le, H.
      discriminate.

  (* Add *)
  exists (m1+m2). rewrite H1, H2, <- N.mul_add_distr_l. reflexivity.

  (* Sub *)
  exists (m1-m2). rewrite H1, H2, <- N.mul_sub_distr_l. reflexivity.

  (* Mul *)
  destruct H; [|rewrite N.mul_comm].
    specialize (IHe1 _ H). destruct IHe1 as [m1 H1]. eexists (m1*_). rewrite H1, N.mul_assoc. reflexivity.
    specialize (IHe2 _ H). destruct IHe2 as [m2 H2]. eexists (m2*_). rewrite H2, N.mul_assoc. reflexivity.

  (* Mod *)
  exists (m1 mod m2). rewrite H1, H2. destruct m2.
    rewrite N.mul_0_r, !N_mod_0_r. reflexivity.
    rewrite N.mul_mod_distr_l. reflexivity. discriminate. apply N.pow_nonzero. discriminate.

  (* Pow *)
  cbn [multiple_of_pow2] in H. destruct e1; try discriminate. destruct n as [|p1]. discriminate.
  destruct (pos_log2opt p1) as [m|] eqn:LOG; [|discriminate]. apply pos_log2opt_sound in LOG.
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as ([|lo2],ohi2). discriminate.
  assert (REM:=N.div_eucl_spec m (N.pos p)). destruct (N.div_eucl m (N.pos p)) as ([|q],[|r]); try discriminate.
  cbn [eval_sastN]. rewrite <- (N.mul_1_r (N.pos p)), LOG, REM, N.add_0_r, <- N.pow_mul_r, <- N.mul_assoc.
  exists (2^(N.pos p * N.pred (N.pos q * eval_sastN mvt e2))).
  rewrite <- N.pow_add_r, <- N.mul_add_distr_l, N.add_1_l, N.succ_pred. reflexivity.
  apply N.neq_mul_0. split. discriminate. eapply N.neq_0_lt_0, N.lt_le_trans; [|apply SB2]. reflexivity.

  (* LAnd *)
  destruct H.
    specialize (IHe1 _ H). destruct IHe1 as [m1 H1]. rewrite H1. eexists. apply mop2_land_sound.
    specialize (IHe2 _ H). destruct IHe2 as [m2 H2]. rewrite H2, N.land_comm. eexists. apply mop2_land_sound.

  (* LOr *)
  exists (N.lor m1 m2). rewrite H1, H2, !(N.mul_comm (2^_)), <- !N.shiftl_mul_pow2, N.shiftl_lor. reflexivity.

  (* Xor *)
  exists (N.lxor m1 m2). rewrite H1, H2, !(N.mul_comm (2^_)), <- !N.shiftl_mul_pow2, N.shiftl_lxor. reflexivity.

  (* ShiftR *)
  destruct e2; try discriminate. specialize (IHe1 _ H). destruct IHe1 as [m1 H1]. exists m1. simpl eval_sastN. rewrite H1.
  rewrite N.shiftr_div_pow2, N.pow_add_r, <- N.mul_assoc, (N.mul_comm _ m1), N.mul_assoc. apply N.div_mul, N.pow_nonzero. discriminate.

  (* ShiftL *)
  specialize (IHe1 _ H). destruct IHe1 as [m1 H1].
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).
  rewrite H1, N.shiftl_mul_pow2, <- N.mul_assoc, (N.mul_comm m1), N.mul_assoc, <- N.pow_add_r. unfold fst.
  destruct (N.le_gt_cases lo2 (N.pos p)).
    rewrite <- N.add_sub_swap by assumption. rewrite <- N.add_sub_assoc, N.pow_add_r, <- N.mul_assoc by apply SB2. eexists. reflexivity.
    rewrite (proj2 (N.sub_0_le _ _)).
      rewrite N.add_0_l, <- (N.add_sub (eval_sastN mvt e2) (N.pos p)), N.add_comm, <- N.add_sub_assoc.
        rewrite N.pow_add_r, <- N.mul_assoc. eexists. reflexivity.
        transitivity lo2. apply N.lt_le_incl. assumption. apply SB2.
      apply N.lt_le_incl. assumption.

  (* IteNN *)
  simpl in H. apply andb_prop in H. destruct (eval_sastN mvt e1).
    apply IHe3, H.
    apply IHe2, H.

  (* IteBN *)
  destruct (eval_sastB mvt e1); eexists; eassumption.
Qed.



(*** SOUNDNESS PROOFS FOR MAIN SIMPLIFICATION LOGIC ***)

(* Simplification is arranged a set of functions, one for each top-level SAST
   constructor.  For each constructor's simplification algorithm we must prove
   that the denotation of the simplified SAST returned by the function equals
   the denotation of the original SAST.

   In order to ease the burden of updating these proofs for typical new
   simplification strategies, it turns out to be useful to have some specialized
   tactics on hand.  Simplifier code tends to have the following structure:

     match e1 with
     | Constructor1 => ...
     | _ => match e2 with
            | Constructor2 => ...
            | _ => <default>
            end
     end

   If e1 matches Constructor1, or if e1 doesn't match Constructor1 but e2 matches
   Constructor2, then we can perform certain simplifications; but otherwise we
   return an less simplified <default> SAST (which might incorporate e1 and/or e2
   unmodified).  Proofs about such code must typically destruct e1 and then e2 to
   reach the default case.  This yields an exponential number of proof goals that
   all have roughly identical proofs that the <default> case works.  While one can
   solve all the duplicate cases via lemmas or tactic automation, doing so is
   tedious, slow, and requires needlessly complex updates to the proof when new
   simplifications are introduced.

   As a better alternative, we here introduce tactics that automatically, recursively
   find anything being matched, destruct it, but in a way that introduces only one
   subgoal for the default case.  The main tactics are:

   * destruct_matches: recursively destruct anything being matched until there are no
     match expressions left in the goal

   * destruct_matches_def <constr>: same as destruct_matches, except coalesce into a
     single common subgoal all subgoals for which the destruct returns the same proof
     goal as it does for constructor <constr>.  For example, specifying any
     constructor other than Constructor1 or Constructor2 yields 3 subgoals for the
     sample code above instead of O(c^d) subgoals (where e1's and e2's types have
     O(c) total constructors and d is the nesting depth of the match expression). *)

Local Ltac grab_matcharg v :=
  match goal with |- context [ match ?a with _ => _ end ] =>
    let tmp := fresh in pose (tmp := a);
    repeat (change a with tmp at 1; lazymatch goal with |- context [ match tmp with _ => _ end ] => fail | _ => idtac end);
    set (v := a) at 1;
    subst tmp
  end.

Local Ltac destruct_match :=
  let va := fresh in
  grab_matcharg va;
  let Heqm := fresh "Heqm" in destruct va eqn:Heqm;
  subst va; try rewrite Heqm in *;
  revert Heqm.

Local Ltac destruct_match_def def :=
  let va := fresh in
  grab_matcharg va;
  let Hdef := fresh in let Heqm := fresh "Heqm" in
  unshelve eenough (Hdef:_); swap 1 2;
  [ destruct va eqn:Heqm;
    try (let x := fresh in set (x := def) in Heqm at 1; exact Hdef)
  | tryif exact True then gfail "default case not found" else idtac
  | ];
  [ first [ exact Hdef | clear Hdef; subst va; try rewrite Heqm in *; revert Heqm ] ..
  | subst va; try reflexivity ].

Local Ltac goal_injections :=
  try lazymatch goal with |- ?P -> _ => first
  [ discriminate 1
  | injection 1 as; subst; goal_injections
  | lazymatch P with
    | context [ match _ with _ => _ end ] => intro; lazymatch goal with [ H: _ |- _ ] => goal_injections; revert H end
    | _ => intro; goal_injections
    end ]
  end.

Local Ltac destruct_matches :=
  destruct_match;
  goal_injections;
  first
  [ lazymatch goal with [ |- _ = None -> _ ] => intro; try destruct_matches end
  | try destruct_matches ].

Local Ltac destruct_matches_def def :=
  first [ destruct_match_def def | destruct_match ];
  goal_injections;
  first
  [ lazymatch goal with [ |- _ = None -> _ ] => intro; try destruct_matches_def def end
  | try destruct_matches_def def ].

Create HintDb picinae_simpl.

(* Addition simplification soundness *)

Theorem simpl_add_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_add e1 e2) = eval_sastN mvt (SIMP_Add e1 e2).
Proof.
  symmetry. unfold simpl_add. destruct_matches_def SIMP_NVar; try reflexivity.
    apply N.add_assoc.
    symmetry. apply N.add_assoc.
    apply N.add_0_r.
Qed.
Local Hint Resolve simpl_add_sound : picinae_simpl.

(* Subtraction simplification soundness *)

Theorem simpl_sub_sound:
  forall mvt e1 e2, eval_sastN mvt (simpl_sub mvt e1 e2) = eval_sastN mvt (SIMP_Sub e1 e2).
Proof.
  symmetry. unfold simpl_sub. destruct_matches_def SIMP_NVar; try reflexivity.
    apply (sastN_eq_sound mvt) in Heqm. simpl. rewrite Heqm. apply N.sub_diag.

    apply N.sub_0_r.

    apply (sastN_eq_sound mvt) in Heqm2. simpl. rewrite Heqm2. apply N.add_sub.

    simpl. rewrite simpl_add_sound. simpl.
    apply andb_prop in Heqm3. destruct Heqm3 as [H1 H2].
    apply sastN_le_sound in H1. apply sastN_le_sound in H2. simpl in H2.
    apply N2Z.inj. rewrite N2Z.inj_sub by apply H2.
    rewrite N2Z.inj_sub by apply H1.
    rewrite Z.sub_sub_distr, <- Z.add_sub_swap, <- N2Z.inj_add, <- N2Z.inj_sub.
      reflexivity.
      apply N.le_sub_le_add_r, H2.
Qed.
Local Hint Resolve simpl_sub_sound : picinae_simpl.

(* Multiplication simplification soundness *)

Theorem simpl_mul_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_mul e1 e2) = eval_sastN mvt (SIMP_Mul e1 e2).
Proof.
  symmetry. unfold simpl_mul. destruct_matches_def SIMP_NVar; try reflexivity.
    apply N.leb_le, N.le_1_r in Heqm0. destruct Heqm0 as [H|H]. discriminate. rewrite H. apply N.mul_1_l.
    apply N.mul_0_r.
    apply N.leb_le, N.le_1_r in Heqm0. destruct Heqm0 as [H|H]. discriminate. rewrite H. apply N.mul_1_r.
Qed.
Local Hint Resolve simpl_mul_sound : picinae_simpl.

(* Logical-or simplification soundness *)

Theorem simpl_lor_sound:
  forall mvt e1 e2, eval_sastN mvt (simpl_lor e1 e2) = eval_sastN mvt (SIMP_LOr e1 e2).
Proof.
  symmetry. unfold simpl_lor. destruct_matches_def SIMP_NVar; try reflexivity.
    apply (sastN_eq_sound mvt) in Heqm. simpl. rewrite Heqm. apply N.lor_diag.
    apply N.lor_0_r.
Qed.
Local Hint Resolve simpl_lor_sound : picinae_simpl.

(* Logical-xor simplification soundness *)

Theorem simpl_xor_sound:
  forall mvt e1 e2, eval_sastN mvt (simpl_xor e1 e2) = eval_sastN mvt (SIMP_Xor e1 e2).
Proof.
  symmetry. unfold simpl_xor. destruct_matches_def SIMP_NVar; try reflexivity.
    apply (sastN_eq_sound mvt) in Heqm. simpl. rewrite Heqm. apply N.lxor_nilpotent.
    apply N.lxor_0_r.
Qed.
Local Hint Resolve simpl_xor_sound : picinae_simpl.

(* Memory-read (getmem) simplification soundness *)

Theorem simpl_getmem_len_sound:
  forall mvt en len m a, eval_sastN mvt (simpl_getmem_len en len m a) = eval_sastN mvt (SIMP_GetMem en len m a).
Proof.
  intros. destruct len as [|len]. reflexivity.
  destruct len; try reflexivity.
  symmetry. apply getmem_1.
Qed.

Theorem simpl_getmem_sound:
  forall mvt en len a m,
  eval_sastN mvt (simpl_getmem mvt en len m a) = eval_sastN mvt (SIMP_GetMem en len m a).
Proof.
  induction m; intros; simpl; try solve [ apply simpl_getmem_len_sound ].
  destruct (andb _ _) eqn:H; [|clear H].

    apply andb_prop in H. destruct H as [EEQ H]. apply endianness_eq_sound in EEQ. subst en0.
    apply andb_prop in H. destruct H as [LEN AEQ]. apply N.eqb_eq in LEN. subst len0.
    apply (sastN_eq_sound mvt) in AEQ.
    rewrite <- AEQ, getmem_setmem. destruct len; reflexivity.

    destruct (sastN_le _ _ a0) eqn:ALE; [|clear ALE].
      apply sastN_le_sound in ALE. rewrite getmem_frame_low by apply ALE. apply IHm.
      destruct (sastN_le _ _ a) eqn:ALE; [|clear ALE].
        apply sastN_le_sound in ALE. rewrite getmem_frame_high by apply ALE. apply IHm.
        apply simpl_getmem_len_sound.
Qed.
Local Hint Resolve simpl_getmem_sound : picinae_simpl.

Theorem simpl_app_sound:
  forall mvt a m,
  eval_sastN mvt (simpl_getmem mvt LittleE 1 m a) = eval_sastN mvt (SIMP_App m a).
Proof.
  intros. etransitivity. apply simpl_getmem_sound. apply getmem_1.
Qed.
Local Hint Resolve simpl_app_sound : picinae_simpl.

(* Logical-shiftr simplification soundness *)

Theorem simpl_shiftr_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_shiftr mvt e1 e2) = eval_sastN mvt (SIMP_ShiftR e1 e2).
Proof.
  symmetry. unfold simpl_shiftr.
  assert (SB := simpl_bounds_sound mvt (SIMP_ShiftR e1 e2)).
  destruct simpl_bounds as (lo,ohi). destruct (match ohi with Some 0 => _ | _ => _ end) eqn:H.
    destruct ohi as [[|hi]|]; try discriminate. apply proj2, N.le_0_r in SB. apply SB.
    clear lo ohi SB H. destruct_matches_def SIMP_NVar; try reflexivity.
      rewrite simpl_getmem_len_sound. cbn [eval_sastN]. rewrite simpl_add_sound. replace (N.pos p) with (Mb*n0).
        cbn [eval_sastN]. apply shiftr_getmem. simpl. rewrite Heqm5. assumption.
        assert (DIV := N.div_eucl_spec (N.pos p) Mb). rewrite Heqm7, N.add_0_r in DIV. symmetry. exact DIV.
      apply N.shiftr_0_l.
Qed.
Local Hint Resolve simpl_shiftr_sound : picinae_simpl.

(* Logical-shiftl simplification soundness *)

Theorem simpl_shiftl_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_shiftl e1 e2) = eval_sastN mvt (SIMP_ShiftL e1 e2).
Proof.
  symmetry. unfold simpl_shiftl. destruct_matches_def SIMP_NVar; try reflexivity.
    apply N.shiftl_0_r.
Qed.
Local Hint Resolve simpl_shiftl_sound : picinae_simpl.

(* Exponentiation (pow) simplification soundness *)

Theorem simpl_pow_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_pow mvt e1 e2) = eval_sastN mvt (SIMP_Pow e1 e2).
Proof.
  intros. unfold simpl_pow. destruct_matches_def SIMP_NVar; try reflexivity.

    assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as ([|lo2],ohi2).
      discriminate.
      symmetry. eapply N.pow_0_l, N.neq_0_lt_0, N.lt_le_trans; [|apply SB2]. reflexivity.

    destruct (pos_log2opt p) eqn:H in Heqm2; [|discriminate]. apply pos_log2opt_sound in H.
    rewrite simpl_shiftl_sound. cbn [eval_sastN]. rewrite simpl_mul_sound. cbn [eval_sastN].
    rewrite H, <- N.pow_mul_r, N.shiftl_mul_pow2. inversion Heqm2. apply N.mul_1_l.
Qed.
Local Hint Resolve simpl_pow_sound : picinae_simpl.

(* Equality-test (eqb) simplification soundness *)

Theorem simpl_eqb_sound:
  forall mvt e1 e2,
  eval_sastB mvt (simpl_eqb mvt e1 e2) = eval_sastB mvt (SIMP_Eqb e1 e2).
Proof.
  intros. unfold simpl_eqb.
  assert (SB1:=simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,ohi1).
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).

  destruct (orb _ _) eqn:H.
  symmetry. simpl. apply N.eqb_neq. apply Bool.orb_prop in H. destruct H.
    destruct ohi1 as [hi1|]; [|discriminate H]. eapply N.lt_neq, N.le_lt_trans.
      apply SB1.
      eapply N.lt_le_trans. apply N.ltb_lt, H. apply SB2.
    destruct ohi2 as [hi2|]; [|discriminate H]. eapply not_eq_sym, N.lt_neq, N.le_lt_trans.
      apply SB2.
      eapply N.lt_le_trans. apply N.ltb_lt, H. apply SB1.

  clear H. destruct (match ohi1 with None => _ | _ => _ end) eqn:H.
  symmetry. simpl. apply N.eqb_eq.
  destruct ohi1 as [hi1|]; [|discriminate]. destruct ohi2 as [hi2|]; [|discriminate].
  do 2 (apply andb_prop in H; destruct H as [H H0]; apply N.eqb_eq in H0; subst).
  apply N.eqb_eq in H. subst hi2.
  apply N.le_antisymm; transitivity hi1; first [ apply SB1 | apply SB2].

  clear H. destruct_matches_def SIMP_NVar; try reflexivity.
  subst. rename Heqm4 into H'. clear - H'.
  repeat (apply andb_prop in H'; destruct H' as [?H H']).
  apply (sastN_eq_sound mvt) in H.
  apply sastN_lt_sound in H0. apply sastN_lt_sound in H1. apply sastN_lt_sound in H'.
  cbn [ andb eval_sastB eval_sastN ]. rewrite <- H.
  rewrite N.eqb_compare. destruct (_ ?= _) eqn:H2.

    apply N.compare_eq in H2. rewrite H2. rewrite N.add_sub, N.mod_same.
      reflexivity.
      apply N.neq_0_lt_0. assumption.

    rewrite N.mod_small.
      rewrite (proj2 (N.eqb_neq _ _)). reflexivity. apply N.neq_sym, N.sub_gt. eapply N.lt_le_trans.
        eassumption.
        apply N.le_add_r.
      eapply N.add_lt_mono_r. rewrite N.sub_add.
        apply N.add_lt_mono_l. apply -> N.compare_lt_iff. exact H2.
        apply N.lt_le_incl, N.lt_lt_add_r. assumption.

    rewrite <- N.add_sub_assoc by apply N.lt_le_incl, N.compare_gt_iff, H2.
    rewrite <- N.add_mod_idemp_l, N.mod_same by apply N.neq_0_lt_0, H0.
    rewrite N.add_0_l, N.mod_small.
      rewrite (proj2 (N.eqb_neq _ _)). reflexivity. apply N.neq_sym, N.sub_gt, N.compare_gt_iff, H2.
      eapply N.le_lt_trans. apply N.le_sub_l. assumption.
Qed.
Local Hint Resolve simpl_eqb_sound : picinae_simpl.

(* Less-than-test (ltb) simplification soundness *)

Theorem simpl_ltb_sound:
  forall mvt e1 e2,
  eval_sastB mvt (simpl_ltb mvt e1 e2) = eval_sastB mvt (SIMP_Ltb e1 e2).
Proof.
  intros. unfold simpl_ltb.
  assert (SB1:=simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,ohi1).
  assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).
  destruct_matches; try reflexivity.
    destruct ohi1 as [hi1|]; [|discriminate]. apply N.ltb_lt in Heqm0. simpl. rewrite (proj2 (N.ltb_lt _ _)).
      reflexivity.
      eapply N.le_lt_trans. apply SB1. eapply N.lt_le_trans; [|apply SB2]. assumption.
    destruct ohi2 as [hi2|]; [|discriminate]. apply N.leb_le in Heqm2. simpl. rewrite (proj2 (N.ltb_ge _ _)).
      reflexivity.
      etransitivity. apply SB2. etransitivity; [|apply SB1]. assumption.
    symmetry. simpl. apply N.ltb_ge. etransitivity. apply SB2. etransitivity. apply N.leb_le, Heqm2. apply SB1.
Qed.
Local Hint Resolve simpl_ltb_sound : picinae_simpl.

(* Boolean-and (BAnd) simplification soundness *)

Theorem simpl_band_sound:
  forall mvt e1 e2,
  eval_sastB mvt (simpl_band e1 e2) = eval_sastB mvt (SIMP_BAnd e1 e2).
Proof.
  symmetry. unfold simpl_band. destruct_matches_def SIMP_BVar; try reflexivity.
    simpl. rewrite (sastB_eq_sound _ _ _ Heqm). apply Bool.andb_diag.
    apply Bool.andb_true_r.
    apply Bool.andb_false_r.
Qed.
Local Hint Resolve simpl_band_sound : picinae_simpl.

(* Logical-and (without conversion to mod) simplification soundness *)

Theorem simpl_land_const_sound:
  forall f mvt e1 n2 (H: forall p, eval_sastN mvt (f e1 p) = eval_sastN mvt (SIMP_LAnd e1 (SIMP_Const (N.pos p)))),
  eval_sastN mvt (simpl_land_const f e1 n2) = eval_sastN mvt (SIMP_LAnd e1 (SIMP_Const n2)).
Proof.
  symmetry. unfold simpl_land_const. destruct_matches_def SIMP_NVar; try reflexivity.
    apply N.land_0_r.
    symmetry. apply H.
Qed.

Theorem simpl_land'_sound:
  forall mvt f e1 e2
    (H: forall p, eval_sastN mvt (f e1 p) = eval_sastN mvt (SIMP_LAnd e1 (SIMP_Const (N.pos p))) /\
                  eval_sastN mvt (f e2 p) = eval_sastN mvt (SIMP_LAnd e2 (SIMP_Const (N.pos p)))),
  eval_sastN mvt (simpl_land' f e1 e2) = eval_sastN mvt (SIMP_LAnd e1 e2).
Proof.
  intros. unfold simpl_land'. destruct_matches_def SIMP_NVar; try reflexivity.
    apply simpl_land_const_sound, H.
    rewrite simpl_land_const_sound by apply H. simpl. apply N.land_comm.
    apply (sastN_eq_sound mvt) in Heqm.
      simpl. rewrite Heqm. symmetry. apply N.land_diag.
Qed.

Corollary simpl_land_nomod_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_land_nomod e1 e2) = eval_sastN mvt (SIMP_LAnd e1 e2).
Proof.
  intros. apply (simpl_land'_sound mvt). split; reflexivity.
Qed.

(* Modulo simplification soundness *)

Lemma N_le_le_eq:
  forall m n, m <= n <= m -> n = m.
Proof.
  intros. destruct (N.lt_total n m); [|destruct H0].
    contradict H0. apply N.le_ngt, H.
    assumption.
    contradict H0. apply N.le_ngt, H.
Qed.

Lemma N_mod_1_r: forall n, n mod 1 = 0.
Proof.
  intro. assert (H := N.mod_lt n 1). destruct (n mod 1).
    reflexivity.
    exfalso. apply (N.ltb_nlt (N.pos p) 1).
      destruct p; reflexivity.
      apply H. discriminate.
Qed.

Lemma dbl_mod:
  forall n p1 p2 pmin pmax d
    (H1: match (p1 ?= p2)%positive with Gt => (p2,p1) | _ => (p1,p2) end = (pmin,pmax))
    (H2: N.pos_div_eucl pmax (N.pos pmin) = (d,0)),
  n mod N.pos pmin = (n mod N.pos p1) mod N.pos p2.
Proof.
  intros.
  eassert (H3 := N.pos_div_eucl_spec _ _). rewrite H2, N.add_0_r in H3. clear H2.
  destruct d as [|d]. discriminate H3. simpl in H3. inversion H3. clear H3. subst pmax.
  match type of H1 with ?x = _ => assert (x=(p2,p1) \/ x=(p1,p2)) end.
    destruct (_ ?= _)%positive; (left + right); reflexivity.
  symmetry. destruct H; rewrite H in H1; inversion H1; clear.
    change (N.pos (_*_)) with (N.pos d * N.pos pmin). rewrite N.mul_comm, N.mod_mul_r, N.mul_comm, N.mod_add;
    [ apply N.mod_mod | ..]; discriminate 1.
    apply N.mod_small. eapply (N.lt_le_trans _ (1*_)).
      rewrite N.mul_1_l. apply N.mod_lt. discriminate 1.
      change (N.pos (_*_)) with (N.pos d * N.pos pmin). apply N.mul_le_mono.
        destruct d; discriminate 1.
        reflexivity.
Qed.

Theorem simpl_mod_core_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_mod_core mvt e1 e2) = eval_sastN mvt (SIMP_Mod e1 e2).
Proof.
  symmetry. unfold simpl_mod_core.

  assert (SB1 := simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,ohi1).
  assert (SB2 := simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2).

  destruct_matches_def SIMP_NVar; try reflexivity; simpl;
  try solve [ symmetry; eapply dbl_mod; [|eassumption]; rewrite Heqm7; reflexivity ];
  repeat match goal with [ H: (_ =? _) = true |- _ ] => apply N.eqb_eq in H; first [ rewrite <- H in * | rewrite H in * ]
                       | [ H: (_ <? _) = true |- _ ] => apply N.ltb_lt in H
                       | [ H: ?n <= _ <= ?n |- _ ] => apply N_le_le_eq in H; rewrite H in *
  end.
    eapply N.mod_small, N.le_lt_trans. apply SB1. eapply N.lt_le_trans. eassumption. apply SB2.
    apply proj2, N.le_0_r in SB2. rewrite SB2. apply N_mod_0_r.
    apply N.mod_1_r.
    reflexivity.
    apply proj2, N.le_0_r in SB2. rewrite SB2. apply N_mod_0_r.
    apply N.mod_1_r.
Qed.

Lemma lmop2ge_is_ge:
  forall m n, m <= least_multiple_of_pow2_ge m n.
Proof.
  intros. unfold least_multiple_of_pow2_ge, N.div_eucl.
  destruct m as [|m]. reflexivity.
  rewrite N.shiftl_1_l. destruct (2^n) as [|p] eqn:H1. contradict H1. apply N.pow_nonzero. discriminate.
  assert (H2:=N.pos_div_eucl_spec m (N.pos p)). assert (H3:=N.pos_div_eucl_remainder m (N.pos p)).
  destruct (N.pos_div_eucl _ _) as (q,[|r]) eqn:DIV. reflexivity.
  rewrite H2, N.mul_succ_r, N.mul_comm. apply N.add_le_mono_l, N.lt_le_incl, H3. discriminate.
Qed.

Lemma lmop2ge_is_pow2n:
  forall m n, exists x, least_multiple_of_pow2_ge m n = x * 2^n.
Proof.
  intros. unfold least_multiple_of_pow2_ge, N.div_eucl.
  destruct m as [|m]. exists 0. reflexivity.
  rewrite N.shiftl_1_l. destruct (2^n) as [|p] eqn:H1. contradict H1. apply N.pow_nonzero. discriminate.
  assert (H2:=N.pos_div_eucl_spec m (N.pos p)). assert (H3:=N.pos_div_eucl_remainder m (N.pos p)).
  destruct (N.pos_div_eucl _ _) as (q,[|r]) eqn:DIV. exists q. rewrite H2. apply N.add_0_r.
  exists (N.succ q). apply N.mul_comm.
Qed.

Theorem simpl_under_modpow2_sound:
  forall mvt e n,
  (eval_sastN mvt (simpl_under_modpow2 mvt e n)) mod 2^n = (eval_sastN mvt e) mod 2^n.
Proof.
  induction e; try rename n into n1; intro n; intros;
  ( destruct n as [|n]; [ rewrite !N.mod_1_r; reflexivity | try reflexivity] ).

    (* Const *)
    unfold simpl_under_modpow2. rewrite N.shiftl_mul_pow2, N.mul_1_l.
    simpl. apply N.mod_mod. discriminate.

    (* Add *)
    simpl. rewrite simpl_add_sound. simpl.
    rewrite N.add_mod, IHe1, IHe2, <- N.add_mod by discriminate 1.
    reflexivity.

    (* Sub *)
    unfold simpl_under_modpow2; fold simpl_under_modpow2.
    assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,[hi2|]); [|reflexivity].
    assert (SB1:=simpl_bounds_sound mvt e1). destruct (simpl_bounds mvt e1) as (lo1,ohi1).
    destruct (_<?_) eqn:LE; [reflexivity|]. apply N.ltb_ge in LE.
    assert (SB2':=simpl_bounds_sound mvt (simpl_under_modpow2 mvt e2 (N.pos n))). destruct (simpl_bounds _ _) as (lo2',[hi2'|]); [|reflexivity].
    assert (SB1':=simpl_bounds_sound mvt (simpl_under_modpow2 mvt e1 (N.pos n))). destruct (simpl_bounds _ _) as (lo1',ohi2').
    rewrite (simpl_sub_sound mvt _ _).

      cbn [ eval_sastN ]. rewrite simpl_add_sound. cbn [ eval_sastN ]. apply N2Z.inj.
      rewrite !N2Z.inj_mod by (apply N.pow_nonzero; discriminate). rewrite !N2Z.inj_sub, N2Z.inj_add.

        rewrite <- Z.add_sub_assoc, <- Z.add_mod_idemp_r, Zminus_mod by apply N2Z_pow2_nonzero.
        rewrite <- !N2Z.inj_mod by (apply N.pow_nonzero; discriminate).
        rewrite IHe1, IHe2.
        rewrite !N2Z.inj_mod by (apply N.pow_nonzero; discriminate). rewrite <- Zminus_mod.
        rewrite Z.add_mod_idemp_r by apply N2Z_pow2_nonzero.
        assert (H:=lmop2ge_is_pow2n (hi2' - lo1') (N.pos n)). destruct H as [x H]. rewrite H.
        rewrite N2Z.inj_mul, Z.add_comm, Z.mod_add by apply N2Z_pow2_nonzero.
        reflexivity.

        etransitivity. apply SB2. etransitivity. apply LE. apply SB1.

        etransitivity. apply SB2'. etransitivity; [|apply N.add_le_mono_l, SB1']. destruct (N.le_ge_cases lo1' hi2').
          rewrite <- (N.sub_add lo1' hi2' H) at 1. apply N.add_le_mono_r, lmop2ge_is_ge.
          etransitivity. apply H. rewrite N.add_comm. apply N.le_add_r.

    (* Mul *)
    simpl. rewrite simpl_mul_sound. simpl.
    rewrite N.mul_mod, IHe1, IHe2, <- N.mul_mod by discriminate 1.
    reflexivity.

    (* Mod *)
    simpl. destruct multiple_of_pow2 eqn:MP2; [|reflexivity].
    apply mop2_sound in MP2. destruct MP2 as [m2 H2]. rewrite H2, IHe1. destruct m2.
      rewrite N.mul_0_r, N_mod_0_r. reflexivity.
      rewrite N.mod_mul_r, N.mul_comm, N.mod_add, N.mod_mod by (try apply N.pow_nonzero; discriminate). reflexivity.

    (* And *)
    cbn [simpl_under_modpow2]. rewrite !N.shiftl_mul_pow2, !N.mul_1_l.
    destruct (match e1 with SIMP_Const _ => _ | _ => _ end) eqn:H.

      destruct e1; try discriminate. inversion H. subst n0. clear H. rewrite (simpl_land_nomod_sound mvt).
      cbn [eval_sastN]. rewrite N.land_comm, land_mod_min, IHe2, (N.land_comm n1).
        rewrite <- land_mod_min, N_land_mod_pow2_moveout.
        apply N.mod_mod, N.pow_nonzero. discriminate.

      clear H. destruct (match e2 with SIMP_Const _ => _ | _ => _ end) eqn:H.

        destruct e2; try discriminate. inversion H. subst n0. clear H. rewrite (simpl_land_nomod_sound mvt).
        cbn [eval_sastN]. rewrite land_mod_min, IHe1.
          rewrite <- land_mod_min, N_land_mod_pow2_moveout.
          apply N.mod_mod, N.pow_nonzero. discriminate.

        rewrite (simpl_land_nomod_sound mvt).
        cbn [eval_sastN]. rewrite N_land_mod_pow2, IHe1, IHe2. symmetry. apply N_land_mod_pow2.

    (* Or *)
    simpl simpl_under_modpow2. rewrite (simpl_lor_sound mvt).
    simpl eval_sastN. rewrite N_lor_mod_pow2, IHe1, IHe2. symmetry. apply N_lor_mod_pow2.

    (* Xor *)
    simpl simpl_under_modpow2. erewrite simpl_xor_sound.
    simpl eval_sastN. rewrite N_lxor_mod_pow2, IHe1, IHe2. symmetry. apply N_lxor_mod_pow2.

    (* ShiftR *)
    remember (N.pos n) as pn. simpl. rewrite Heqpn at 1.
    assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,[hi2|]); [|reflexivity].
    rewrite simpl_shiftr_sound, <- N.land_ones. erewrite <- (N.add_sub pn _) at 2.
    simpl. rewrite <- N.ones_div_pow2, <- N.shiftr_div_pow2, <- N.shiftr_land by (rewrite N.add_comm; apply N.le_add_r).
    rewrite N.land_ones, <- (N.min_r (pn+hi2) (pn+eval_sastN _ _)), <- N_mod_mod_pow2_min, IHe1,
            N_mod_mod_pow2_min, N.min_r by apply N.add_le_mono_l, SB2.
    rewrite <- N.land_ones, N.shiftr_land, (N.shiftr_div_pow2 (N.ones _)), N.ones_div_pow2
         by (rewrite N.add_comm; apply N.le_add_r).
    rewrite N.add_sub. apply N.land_ones.

    (* ShiftL *)
    remember (N.pos n) as pn. simpl. rewrite Heqpn at 1.
    assert (SB2:=simpl_bounds_sound mvt e2). destruct (simpl_bounds mvt e2) as (lo2,ohi2). unfold fst.
    rewrite simpl_shiftl_sound. simpl. rewrite !N.shiftl_mul_pow2. destruct (N.le_ge_cases (eval_sastN mvt e2) pn).

      erewrite <- (N.sub_add _ pn H) at 2. rewrite N.pow_add_r.
      rewrite N.mul_mod_distr_r by (apply N.pow_nonzero; discriminate).
      replace (pn - eval_sastN mvt e2) with (N.min (pn - lo2) (pn - eval_sastN mvt e2)) by
        apply N.min_r, N.sub_le_mono_l, SB2.
      rewrite <- N_mod_mod_pow2_min, IHe1.
      rewrite N_mod_mod_pow2_min, N.min_r by apply N.sub_le_mono_l, SB2.
      rewrite <- N.mul_mod_distr_r by (apply N.pow_nonzero; discriminate).
      rewrite <- N.pow_add_r, N.sub_add by assumption. reflexivity.

      rewrite <- (N.sub_add _ _ H).
      rewrite N.pow_add_r, !N.mul_assoc, !N.mod_mul by (apply N.pow_nonzero; discriminate).
      reflexivity.

  (* GetMem *)
  remember (N.pos n) as pn. simpl. rewrite Heqpn at 1.
  destruct en. reflexivity.
  assert (DIV:=N.div_eucl_spec pn Mb). destruct (N.div_eucl pn Mb) as (q,[|r]); [|reflexivity].
  destruct m; [|reflexivity..].
  destruct id as [|id]. reflexivity.
  destruct (mvt_lookup mvt id) as [| |? [wtm0|]] eqn:H; try reflexivity.
  simpl. rewrite H, simpl_getmem_len_sound. simpl. rewrite H.
  rewrite N.add_0_r in DIV. rewrite DIV. rewrite N.mod_small.
    symmetry. apply getmem_mod. assumption.
    eapply N.lt_le_trans.
      apply getmem_bound. assumption.
      apply N.pow_le_mono_r. discriminate. apply N.mul_le_mono_l, N.le_min_r.

  (* IteNN *)
  simpl. unfold simpl_ite_sameN. destruct sastN_eq eqn:EQ.
    destruct (eval_sastN _ e1).
      rewrite (sastN_eq_sound _ _ _ EQ). apply IHe3.
      apply IHe2.
    simpl. destruct (eval_sastN _ e1). apply IHe3. apply IHe2.

  (* IteBN *)
  simpl. unfold simpl_ite_sameN. destruct sastN_eq eqn:EQ.
    destruct (eval_sastB _ e1).
      apply IHe1.
      rewrite (sastN_eq_sound _ _ _ EQ). apply IHe2.
    simpl. destruct (eval_sastB _ e1). apply IHe1. apply IHe2.
Qed.

Theorem simpl_mod_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_mod mvt e1 e2) = eval_sastN mvt (SIMP_Mod e1 e2).
Proof.
  intros.
  destruct e2; try apply simpl_mod_core_sound.
  destruct n. apply simpl_mod_core_sound.
  unfold simpl_mod. destruct (pos_log2opt p) eqn:H.
    rewrite (pos_log2opt_sound _ _ H), simpl_mod_core_sound. eapply simpl_under_modpow2_sound.
    apply simpl_mod_core_sound.
Qed.
Local Hint Resolve simpl_mod_sound : picinae_simpl.

(* Logical-and (with conversion to modulo) simplification soundness *)

Lemma landr_ones_mod:
  forall p n (H: pos_is_ones p = true),
  N.land n (N.pos p) = n mod N.pos (Pos.succ p).
Proof.
  intros.
  assert (H1: exists x, N.pos p = N.pred (2^x)). induction p.
    destruct (IHp H) as [y H2]. exists (N.succ y).
      rewrite <- N.ones_equiv, <- N.add_1_l, N.ones_add, <- N.succ_double_spec, N.ones_equiv, <- H2. reflexivity.
    discriminate H.
    exists 1. reflexivity.
  destruct H1 as [x H1]. change (N.pos (Pos.succ p)) with (N.succ (N.pos p)). rewrite H1.
  rewrite N.succ_pred, <- N.ones_equiv by (apply N.pow_nonzero; discriminate 1).
  apply N.land_ones.
Qed.

Theorem simpl_land_sound:
  forall mvt e1 e2,
  eval_sastN mvt (simpl_land mvt e1 e2) = eval_sastN mvt (SIMP_LAnd e1 e2).
Proof.
  intros. apply (simpl_land'_sound mvt).
  intros. unfold simpl_and2mod. destruct (pos_is_ones p) eqn:H.

    erewrite !simpl_mod_sound. split; symmetry; apply landr_ones_mod, H.

    generalize (N.pos p). clear p H. intro p.
    simpl. rewrite <- (N.mod_small p (2^(N.size p))) at 2 5 by apply N.size_gt.
    rewrite <- N.land_ones, (N.land_comm p), !N.land_assoc, !N.land_ones.
    rewrite !(simpl_under_modpow2_sound mvt).
    rewrite <- !N.land_ones, <- !N.land_assoc, (N.land_comm (N.ones _)).
    rewrite N.land_ones, N.mod_small by apply N.size_gt.
    split; reflexivity.
Qed.
Local Hint Resolve simpl_land_sound : picinae_simpl.

(* Ternary operator (ite) soundness *)

Definition sastNB_dtyp t := match t with SastN => N | SastB => bool end.
Definition sastNBM_dtyp t := match t with NB2NBM t' => sastNB_dtyp t' | SastM => addr->N end.
Definition eval_sastNB {t} : metavar_tree -> sastNB t -> sastNB_dtyp t :=
  match t with SastN => eval_sastN | SastB => eval_sastB end.
Definition eval_sastNBM {t} : metavar_tree -> sastNBM t -> sastNBM_dtyp t :=
  match t with NB2NBM t' => @eval_sastNB t' | SastM => eval_sastM end.
Definition ternary {t T} (mvt:metavar_tree) (e0:sastNB t) (e1 e2 : T) :=
  match t return (sastNB t -> T) with
  | SastN => fun e => if eval_sastN mvt e then e2 else e1
  | SastB => fun e => if eval_sastB mvt e then e1 else e2
  end e0.

Theorem sastNB_eq_sound:
  forall {t1 t2} mvt e1 e2 (EQ: @sastNB_eq t1 t2 e1 e2 = true),
  existT sastNB_dtyp t1 (eval_sastNB mvt e1) = existT sastNB_dtyp t2 (eval_sastNB mvt e2).
Proof.
  intros. destruct t1,t2; try discriminate; simpl.
    rewrite (sastN_eq_sound _ _ _ EQ). reflexivity.
    rewrite (sastB_eq_sound _ _ _ EQ). reflexivity.
Qed.

Theorem sastNBM_eq_sound:
  forall f t e1 e2 (EQ: @sastNBM_eq t e1 e2 = true),
  eval_sastNBM f e1 = eval_sastNBM f e2.
Proof.
  intros. destruct t. destruct t.
    apply sastN_eq_sound. exact EQ.
    apply sastB_eq_sound. exact EQ.
    apply sastM_eq_sound. exact EQ.
Qed.

Lemma ternary_cases:
  forall {t} mvt (e0:sastNB t),
  (forall T (e1 e2:T), ternary mvt e0 e1 e2 = e1) \/ (forall T (e1 e2:T), ternary mvt e0 e1 e2 = e2).
Proof.
  intros. unfold ternary. destruct t, (_ mvt e0); constructor; reflexivity.
Qed.

Lemma ternary_distr:
  forall {A B t} (f:A->B) mvt (e0:sastNB t) (e1 e2:A),
  f (ternary mvt e0 e1 e2) = ternary mvt e0 (f e1) (f e2).
Proof.
  intros. destruct (ternary_cases mvt e0) as [H|H]; rewrite !H; reflexivity.
Qed.

Lemma ternary_distr2:
  forall {A B C t} (f:A->B->C) mvt (e0:sastNB t) (e1a e1b:A) (e2a e2b:B),
  f (ternary mvt e0 e1a e1b) (ternary mvt e0 e2a e2b) = ternary mvt e0 (f e1a e2a) (f e1b e2b).
Proof.
  intros. destruct (ternary_cases mvt e0) as [H|H]; rewrite !H; reflexivity.
Qed.

Lemma ternary_same:
  forall {t T} mvt (e0:sastNB t) (e:T),
  ternary mvt e0 e e = e.
Proof.
  intros. destruct (ternary_cases mvt e0) as [H|H]; rewrite !H; reflexivity.
Qed.

Lemma ternary_eval:
  forall {t T} mvt (e0:sastNB t) (e1 e2:T),
  ternary mvt e0 e1 e2 = if match t return (sastNB_dtyp t -> bool) with
                            | SastN => N.leb 1 | SastB => fun b => b
                            end (eval_sastNB mvt e0) then e1 else e2.
Proof.
  intros. unfold ternary. destruct t; simpl; destruct (_ mvt e0); try reflexivity.
  destruct p; reflexivity.
Qed.

Module DecidableSet_NB <: Eqdep_dec.DecidableSet.
  Definition U := sastNB_typ.
  Theorem eq_dec: forall x y:U, {x=y}+{x<>y}.
    decide equality.
  Qed.
End DecidableSet_NB.
Module DecidableEqDepSet_NB := Eqdep_dec.DecidableEqDepSet DecidableSet_NB.

Lemma invert_ite_parts:
  forall t t' e0 e0' (e1 e2 e1' e2': sastNBM t'),
  Some (existT sastNB t e0, (e1,e2)) = Some (existT sastNB t e0', (e1',e2')) ->
  e0=e0' /\ e1=e1' /\ e2=e2'.
Proof.
  intros. inversion H. repeat split.
  inversion_sigma. subst. erewrite (DecidableEqDepSet_NB.UIP_refl _ _). reflexivity.
Qed.

Theorem eval_ite_parts:
  forall {t t' e e0 e1 e2} mvt (H: @ite_parts t' e = Some (existT _ t e0, (e1,e2))),
  eval_sastNBM mvt e = eval_sastNBM mvt (ternary mvt e0 e1 e2).
Proof.
  intros. rewrite ternary_distr. destruct t' as [[|]|]; destruct e; try discriminate H;
  destruct t; try discriminate H;
  apply invert_ite_parts in H; destruct H as [? [? ?]]; subst; reflexivity.
Qed.

Theorem eval_make_ite:
  forall t t' e0 e1 e2 mvt,
  eval_sastNBM mvt (make_ite t t' e0 e1 e2) = eval_sastNBM mvt (ternary mvt e0 e1 e2).
Proof.
  intros. rewrite ternary_distr. destruct t' as [[|]|]; destruct t; reflexivity.
Qed.

Theorem simpl_static_branch_sound:
  forall {t mvt} {e0:sastNB t} {b} (SSB: simpl_static_branch mvt e0 = Some b)
         T (e1 e2:T),
  ternary mvt e0 e1 e2 = if b then e1 else e2.
Proof.
  unfold ternary, simpl_static_branch. intros. destruct t.
    assert (SBS:=simpl_bounds_sound mvt e0). destruct simpl_bounds as [[|lo] ohi].
      destruct ohi as [[|hi]|]; [|discriminate..].
        inversion SSB. destruct (eval_sastN mvt e0). reflexivity. apply proj2 in SBS. contradiction.
      inversion SSB. destruct ohi as [hi|]; (destruct (eval_sastN mvt e0);
      [ apply proj1 in SBS; contradiction
      | reflexivity ]).
    destruct e0; try discriminate SSB. inversion SSB. reflexivity.
Qed.

Lemma ternary_make_ite:
  forall t1 t2 T mvt (e0:sastNB t1) (e1 e2:sastNB t2) (x y:T),
  ternary mvt (make_ite t1 (NB2NBM t2) e0 e1 e2) x y = ternary mvt (ternary mvt e0 e1 e2) x y.
Proof.
  intros. unfold make_ite, ternary. destruct t1, t2;
  simpl; destruct (_ mvt e0); reflexivity.
Qed.

Theorem simpl_ite_combine_sound:
  forall t1 t2 t3 mvt (e0:sastNB t1) (e0a e0b:sastNB t2) (e1 e2:sastNBM t3),
  eval_sastNBM mvt (simpl_ite_combine mvt e0 e0a e0b e1 e2) =
  eval_sastNBM mvt (ternary mvt (ternary mvt e0 e0a e0b) e1 e2).
Proof.
  unfold simpl_ite_combine. intros. destruct (simpl_static_branch mvt e0a) eqn:SSB1.
    destruct (simpl_static_branch mvt e0b) eqn:SSB2.

      rewrite <- (simpl_static_branch_sound SSB1), <- !(simpl_static_branch_sound SSB2).
      rewrite ternary_distr, !(ternary_distr (eval_sastNBM mvt)), !eval_make_ite.
      destruct (ternary_cases mvt e0) as [H|H]; rewrite !H, !ternary_same; reflexivity.

      rewrite eval_make_ite, ternary_make_ite. reflexivity.
    rewrite eval_make_ite, ternary_make_ite. reflexivity.
Qed.

Theorem simpl_ite_sound:
  forall t t' mvt (e0:sastNB t) (e1 e2:sastNBM t'),
  eval_sastNBM mvt (simpl_ite t t' mvt e0 e1 e2) =
  ternary mvt e0 (eval_sastNBM mvt e1) (eval_sastNBM mvt e2).
Proof.
  intros. rewrite <- ternary_distr. unfold simpl_ite. destruct (sastNBM_eq e1 e2) eqn:EQ.
    rewrite ternary_distr, <- (sastNBM_eq_sound mvt _ _ _ EQ), ternary_same. reflexivity.
    destruct simpl_static_branch eqn:SSB.
      rewrite (simpl_static_branch_sound SSB). reflexivity.
      destruct ite_parts as [[[e0ct e0c] [e0a e0b]]|] eqn:ITEP.

        rewrite simpl_ite_combine_sound, (ternary_eval mvt e0 e1 e2).
        change (@eval_sastNB t) with (@eval_sastNBM (NB2NBM t)). rewrite (eval_ite_parts mvt ITEP).
        simpl (@eval_sastNBM (NB2NBM t)). rewrite <- ternary_eval. reflexivity.

        apply eval_make_ite.
Qed.
Local Hint Extern 0 (_ _ (simpl_ite ?t ?t' _ _ _ _) = _) => apply (simpl_ite_sound t t') : picinae_simpl.


(* Soundness of main simplification dispatcher functions *)

(* Implementation note:  If you have changed the simplifier code causing one of
   the next three proofs to fail, you need to add a hint to the picinae_simpl
   database as follows:
      Local Hint Resolve my_soundness_theorem : picinae_simpl.
   where my_soundness_theorem has the form:
      forall mvt <args>, eval_sastT mvt (my_simplifier mvt <args>) = eval_sastT mvt (SIMP_* <args>)
   where SIMP_* is the SAST constructor being simplified, my_simplifier is the
   simplifier function that simplifies it, T is the return type (N, B, or M),
   and <args> are any constructor arguments.

   For examples of this regimen, see any examples of "Local Hint Resolve" in
   the proof collection above. *)

Theorem simplN_dispatch_sound:
  forall mvt e,
  eval_sastN mvt (simplN_dispatch mvt e) = eval_sastN mvt e.
Proof with (trivial with picinae_simpl).
  intros. destruct e; unfold simplN_dispatch...
Qed.

Theorem simplB_dispatch_sound:
  forall mvt e,
  eval_sastB mvt (simplB_dispatch mvt e) = eval_sastB mvt e.
Proof with (trivial with picinae_simpl).
  intros. destruct e; unfold simplB_dispatch...
Qed.

Theorem simplM_dispatch_sound:
  forall mvt e,
  eval_sastM mvt (simplM_dispatch mvt e) = eval_sastM mvt e.
Proof with (trivial with picinae_simpl).
  intros. destruct e; unfold simplM_dispatch...
Qed.

Corollary simpl_dispatch_sound:
  forall t mvt (e:sastNBM t), eval_sastNBM mvt (simpl_dispatch mvt e) = eval_sastNBM mvt e.
Proof.
  intros. repeat destruct t.
    apply simplN_dispatch_sound.
    apply simplB_dispatch_sound.
    apply simplM_dispatch_sound.
Qed.


(* Soundness of ternary-argument simplifier functions *)

Theorem simpl_uop_ite'_sound:
  forall t t' (uop: sastNBM t -> sastNBM t') mvt e e'
    (TRANS: forall e1 e1', eval_sastNBM mvt e1 = eval_sastNBM mvt e1' ->
                           eval_sastNBM mvt (uop e1) = eval_sastNBM mvt (uop e1'))
    (H: simpl_uop_ite' uop mvt e = Some e'),
  eval_sastNBM mvt (uop e) = eval_sastNBM mvt e'.
Proof.
  unfold simpl_uop_ite'. intros. destruct ite_parts as [[[e0t e0] [e1 e2]]|] eqn:ITEP; [|discriminate].
  repeat (destruct sastNBM_eq; [discriminate|]). inversion_clear H.
  rewrite eval_make_ite, <- ternary_distr, simpl_dispatch_sound, <- ternary_distr.
  apply TRANS, (eval_ite_parts mvt ITEP).
Qed.

Theorem simpl_bop_ite'_sound:
  forall t1 t2 t' (bop: sastNBM t1 -> sastNBM t2 -> sastNBM t') mvt e1 e2 e'
    (TRANS: forall e1 e1' e2 e2', eval_sastNBM mvt e1 = eval_sastNBM mvt e1' ->
                                  eval_sastNBM mvt e2 = eval_sastNBM mvt e2' ->
            eval_sastNBM mvt (bop e1 e2) = eval_sastNBM mvt (bop e1' e2'))
    (H: simpl_bop_ite' bop mvt e1 e2 = Some e'),
  eval_sastNBM mvt (bop e1 e2) = eval_sastNBM mvt e'.
Proof.
  unfold simpl_bop_ite'. intros. destruct (ite_parts e1) as [[[e1t e1c] [e1a e1b]]|] eqn:ITEP1.
    destruct (ite_parts e2) as [[[e2t e2c] [e2a e2b]]|] eqn:ITEP2.
      destruct sastNB_eq eqn:EQ.

        inversion_clear H. rewrite eval_make_ite, <- ternary_distr, simpl_dispatch_sound, <- ternary_distr2.
        replace (ternary mvt e1c e2a e2b) with (ternary mvt e2c e2a e2b).
          apply TRANS. apply (eval_ite_parts mvt ITEP1). apply (eval_ite_parts mvt ITEP2).
          rewrite !ternary_eval. apply (sastNB_eq_sound mvt) in EQ. dependent rewrite EQ. reflexivity.

        destruct simpl_uop_ite' eqn:SUOP.
          inversion H. subst s. apply simpl_uop_ite'_sound.
            intros. apply TRANS. reflexivity. assumption.
            assumption.
          change (bop e1 e2) with ((fun a => bop a e2) e1). apply simpl_uop_ite'_sound.
            intros. apply TRANS. assumption. reflexivity.
            assumption.
      change (bop e1 e2) with ((fun a => bop a e2) e1). apply simpl_uop_ite'_sound.
        intros. apply TRANS. assumption. reflexivity.
        assumption.
    apply simpl_uop_ite'_sound.
      intros. apply TRANS. reflexivity. assumption.
      assumption.
Qed.

Theorem simpl_uop_ite_sound:
  forall t t' (uop: sastNBM t -> sastNBM t') mvt e
    (TRANS: forall e1 e1', eval_sastNBM mvt e1 = eval_sastNBM mvt e1' ->
                           eval_sastNBM mvt (uop e1) = eval_sastNBM mvt (uop e1')),
  eval_sastNBM mvt (simpl_uop_ite uop mvt e) = eval_sastNBM mvt (uop e).
Proof.
  intros. unfold simpl_uop_ite. destruct simpl_uop_ite' eqn:H.
    symmetry. apply simpl_uop_ite'_sound; assumption.
    reflexivity.
Qed.

Theorem simpl_bop_ite_sound:
  forall t1 t2 t' (bop: sastNBM t1 -> sastNBM t2 -> sastNBM t') mvt e1 e2
    (TRANS: forall e1 e1' e2 e2', eval_sastNBM mvt e1 = eval_sastNBM mvt e1' ->
                                  eval_sastNBM mvt e2 = eval_sastNBM mvt e2' ->
            eval_sastNBM mvt (bop e1 e2) = eval_sastNBM mvt (bop e1' e2')),
  eval_sastNBM mvt (simpl_bop_ite bop mvt e1 e2) = eval_sastNBM mvt (bop e1 e2).
Proof.
  intros. unfold simpl_bop_ite. destruct simpl_bop_ite' eqn:H.
    symmetry. apply simpl_bop_ite'_sound; assumption.
    reflexivity.
Qed.

Local Ltac prove_simpl_iteT_sound := solve
[ reflexivity
| match goal with |- context [ @simpl_bop_ite ?t1 ?t2 ?t' ] => apply (simpl_bop_ite_sound t1 t2 t') end;
  simpl; let H1 := fresh in let H2 := fresh in intros ? ? ? ? H1 H2; rewrite H1,H2; reflexivity
| match goal with |- context [ @simpl_uop_ite ?t ?t' ] => apply (simpl_uop_ite_sound t t') end;
  simpl; let H := fresh in intros ? ? H; rewrite H; reflexivity ].

Theorem simpl_iteN_sound:
  forall mvt e, eval_sastN mvt (simpl_iteN mvt e) = eval_sastN mvt e.
Proof.
  change eval_sastN with (@eval_sastNBM (NB2NBM SastN)).
  destruct e; unfold simpl_iteN; prove_simpl_iteT_sound.
Qed.

Theorem simpl_iteB_sound:
  forall mvt e, eval_sastB mvt (simpl_iteB mvt e) = eval_sastB mvt e.
Proof.
  change eval_sastB with (@eval_sastNBM (NB2NBM SastB)).
  destruct e; unfold simpl_iteB; prove_simpl_iteT_sound.
Qed.

Theorem simpl_iteM_sound:
  forall mvt e, eval_sastM mvt (simpl_iteM mvt e) = eval_sastM mvt e.
Proof.
  change eval_sastM with (@eval_sastNBM SastM).
  destruct e; unfold simpl_iteM; prove_simpl_iteT_sound.
Qed.


(* Soundness of main recursive bottom-up simplification loop: *)

Theorem simpl_sastNBM_sound:
  forall mvt, (forall e, eval_sastN mvt (simpl_sastN mvt e) = eval_sastN mvt e) /\
              (forall e, eval_sastB mvt (simpl_sastB mvt e) = eval_sastB mvt e) /\
              (forall e, eval_sastM mvt (simpl_sastM mvt e) = eval_sastM mvt e).
Proof.
  intro; apply sast_mind; intros;
  cbn - [ simplN_dispatch simplB_dispatch simplM_dispatch eval_sastN eval_sastB eval_sastM ];
  first [ rewrite simpl_iteN_sound, simplN_dispatch_sound
        | rewrite simpl_iteB_sound, simplB_dispatch_sound
        | rewrite simpl_iteM_sound, simplM_dispatch_sound ];
  cbn [ eval_sastN eval_sastB eval_sastM ];
  repeat match goal with [ H: _ = _ |- _ ] => rewrite H; clear H end;
  reflexivity.
Qed.

Definition simpl_sastN_sound mvt := proj1 (simpl_sastNBM_sound mvt).
Definition simpl_sastB_sound mvt := proj1 (proj2 (simpl_sastNBM_sound mvt)).
Definition simpl_sastM_sound mvt := proj2 (proj2 (simpl_sastNBM_sound mvt)).

Theorem simpl_sastU_sound:
  forall {A} mvt (t:sastU A), eval_sastU mvt t = eval_sastU mvt (simpl_sastU mvt t).
Proof.
  induction t; intros; simpl.
    reflexivity.
    rewrite (simpl_sastN_sound mvt), IHt by apply H. reflexivity.
    rewrite (simpl_sastM_sound mvt), IHt by apply H. reflexivity.
Qed.

Theorem sastS_removevar_frame:
  forall e v v', v' <> v -> eval_sastS (sastS_remove_var v e) v' = eval_sastS e v'.
Proof.
  intros. induction e; simpl.
    reflexivity.
    destruct (v0 == v).
      subst v0. rewrite update_frame by assumption. apply IHe.
      simpl. destruct (vareq v' v0).
        subst v0. rewrite !update_updated. reflexivity.
        rewrite !update_frame by assumption. apply IHe.
Qed.

Theorem simpl_sastS_sound:
  forall e, eval_sastS e = eval_sastS (simpl_sastS e).
Proof.
  induction e; intros; simpl.
    reflexivity.
    extensionality v0. destruct (vareq v0 v).
      subst v0. rewrite !update_updated. reflexivity.
      rewrite !update_frame, sastS_removevar_frame by assumption. rewrite IHe by apply H. reflexivity.
Qed.

Theorem sastS_findvar_sound:
  forall v t, eval_sastS t v = eval_sastS (sastS_find_var v t) v.
Proof.
  induction t; intros; simpl.
    reflexivity.
    destruct (v == v0); simpl.
      subst v0. rewrite !update_updated. reflexivity.
      rewrite <- IHt. apply update_frame. assumption.
Qed.

Theorem simpl_sastV_sound:
  forall {A} (t:sastV A), eval_sastV t = eval_sastV (simpl_sastV t).
Proof.
  induction t; intros; simpl.
    reflexivity.
    rewrite IHt, sastS_findvar_sound. reflexivity.
    rewrite IHt, simpl_sastS_sound. reflexivity.
Qed.


(* Soundness of output routines *)

Theorem simpl_out_const_sound:
  forall n, simpl_out_const noe_setop n = n.
Proof.
  destruct n.
    reflexivity.
    unfold simpl_out_const. destruct pos_log2opt eqn:H.
      apply pos_log2opt_sound in H. rewrite H. destruct (_ <? _); reflexivity.
      reflexivity.
Qed.

Theorem simpl_outNBM_sound:
  forall mvt, (forall e, simpl_outN noe_setop mvt e = eval_sastN mvt e) /\
              (forall e, simpl_outB noe_setop mvt e = eval_sastB mvt e) /\
              (forall e, simpl_outM noe_setop mvt e = eval_sastM mvt e).
Proof.
  intro. apply sast_mind; intros; simpl; try rewrite H; try rewrite H0; try rewrite H1; try reflexivity.
    apply simpl_out_const_sound.
    destruct (len =? 1) eqn:H1.
      apply N.eqb_eq in H1. subst len. rewrite getmem_1. reflexivity.
      reflexivity.
Qed.

Definition simpl_outN_sound mvt := proj1 (simpl_outNBM_sound mvt).
Definition simpl_outB_sound mvt := proj1 (proj2 (simpl_outNBM_sound mvt)).
Definition simpl_outM_sound mvt := proj2 (proj2 (simpl_outNBM_sound mvt)).

Theorem simpl_outU_sound:
  forall A mvt (t:sastU A), simpl_outU noe_setop mvt t = eval_sastU mvt t.
Proof.
  induction t; simpl.
    reflexivity.
    rewrite IHt, simpl_outN_sound. reflexivity.
    rewrite IHt, simpl_outM_sound. reflexivity.
Qed.

Theorem simpl_outS_sound:
  forall e, simpl_outS noe_typop e = eval_sastS e.
Proof.
  induction e; intros; simpl.
    reflexivity.
    rewrite IHe. reflexivity.
Qed.

Theorem simpl_outV_sound:
  forall A (t:sastV A), simpl_outV noe_typop t = eval_sastV t.
Proof.
  induction t; simpl.
    reflexivity.
    destruct t0.
      rewrite IHt. reflexivity.
      rewrite IHt, simpl_outS_sound. reflexivity.
    rewrite IHt, simpl_outS_sound. reflexivity.
Qed.


(*** INTERFACE ***)

(* The following theorems simplify a hypothesis or goal containing an SAST
   generated by the front-end parser, yielding subgoals that are solvable
   by reflexivity, and arranging the subgoals in an order amenable to
   unification without uncontrolled expansion by vm_compute and friends. *)

Theorem simplify_sastN_hyp:
  forall {x e} noe mvt t
    (NOE: noe = noe_setop)
    (H': e = eval_sastN mvt t)
    (H: x = e),
  x = simpl_outN noe mvt (simpl_sastN mvt t).
Proof.
  intros. subst noe x e. erewrite simpl_outN_sound, <- simpl_sastN_sound. reflexivity.
Qed.

Theorem simplify_sastB_hyp:
  forall {x e} noe mvt t
    (NOE: noe = noe_setop)
    (H': e = eval_sastB mvt t)
    (H: x = e),
  x = simpl_outB noe mvt (simpl_sastB mvt t).
Proof.
  intros. subst noe x e. erewrite simpl_outB_sound, <- simpl_sastB_sound. reflexivity.
Qed.

Theorem simplify_sastM_hyp:
  forall {x e} noe mvt t
    (NOE: noe = noe_setop)
    (H': e = eval_sastM mvt t)
    (H: x = e),
  x = simpl_outM noe mvt (simpl_sastM mvt t).
Proof.
  intros. subst noe x e. erewrite simpl_outM_sound, <- simpl_sastM_sound. reflexivity.
Qed.

Theorem simplify_sastV_hyp:
  forall {P:Prop} noe (t:sastV Prop)
    (NOE: noe = noe_typop)
    (H': P = eval_sastV t)
    (H:P),
  simpl_outV noe (simpl_sastV t).
Proof.
  intros. subst noe P. rewrite simpl_outV_sound, <- simpl_sastV_sound.
  exact H.
Qed.

Theorem simplify_sastU_hyp:
  forall {P:Prop} noe mvt (t:sastU Prop)
    (NOE: noe = noe_setop)
    (H': P = eval_sastU mvt t)
    (H:P),
  simpl_outU noe mvt (simpl_sastU mvt t).
Proof.
  intros. subst noe P. erewrite simpl_outU_sound, <- simpl_sastU_sound. exact H.
Qed.

Theorem simplify_sastV_goal:
  forall {P:Prop} noe (t:sastV Prop)
    (G': simpl_outV noe (simpl_sastV t))
    (NOE: noe = noe_typop)
    (H': P = eval_sastV t),
  P.
Proof.
  intros. subst noe P. rewrite simpl_sastV_sound.
  rewrite <- simpl_outV_sound. exact G'.
Qed.

Theorem simplify_sastU_goal:
  forall {P:Prop} noe mvt (t:sastU Prop)
    (G': simpl_outU noe mvt (simpl_sastU mvt t))
    (NOE: noe = noe_setop)
    (H': P = eval_sastU mvt t),
  P.
Proof.
  intros. subst noe P. erewrite simpl_sastU_sound.
  rewrite <- simpl_outU_sound. exact G'.
Qed.

(* The following theorems are helpers used by the main ltacs to reduce a few terms
   that fall outside of what the SASTs can parse. *)

Theorem N_shiftl1_pow2 {n w} (H: n < N.shiftl 1 w): n < 2^w.
Proof. rewrite <- N.shiftl_1_l. exact H. Qed.

Theorem simpl_if_if:
  forall (b:bool) (q1 q2:stmt),
  (if (if b then 1 else N0) then q1 else q2) = (if b then q2 else q1).
Proof. intros. destruct b; reflexivity. Qed.

Theorem simpl_if_not_if:
  forall (b:bool) (q1 q2:stmt),
  (if (N.lnot (if b then 1 else N0) 1) then q1 else q2) = (if b then q1 else q2).
Proof. intros. destruct b; reflexivity. Qed.

End Picinae_Simplifier_v1_1.
