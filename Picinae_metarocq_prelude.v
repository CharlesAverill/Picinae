Require Export Picinae_core.
Require Export Picinae_armv7_lifter.
Require Export NArith ZArith.
Open Scope N.

Load MetaRocqPrelude.
Export MRMonadNotation.
From MetaRocq.Utils Require Export bytestring.
Export String.
Open Scope bs.

Definition printQualid (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => tmPrint "Quoted inductive: ";; tmPrint ind;; mib <- (tmQuoteInductive ind.(inductive_mind));; tmPrint mib
  | ConstRef kn => tmPrint "Quoted constant: ";; tmPrint kn;; (tmQuoteConstant kn false) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

(*
  MetaRocq Run (printQualid "endianness").
  MetaRocq Run (printQualid "zxbits").
*)

(* Notations for simplifying common terms. *)
Notation "'_true_'" := (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool"); inductive_ind := 0 |} 0 []).
Notation "'_false_'" := (tConstruct {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool"); inductive_ind := 0 |} 1 []).
Notation "'_N_'" := (tInd {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "N"); inductive_ind := 0 |} []).
Notation "'_Nmodulo_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "modulo") []).
Notation "'_Nadd_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "add") []).
Notation "'_Nsub_'" := (tConst (MPdot (MPfile ["NatDef"; "BinNums"; "Corelib"]) "N", "sub") []).
Notation "'_Nshiftr_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "shiftr") []).
Notation "'_Nshiftl_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "shiftl") []).
Notation "'_Npow_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "pow") []).
Notation "'_zxbits_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "zxbits") []).
Notation "'_xbits_'" := (tConst (MPfile ["Picinae_core"; "Picinae"], "xbits") []).
Notation "'_Z.of_N_'" := (tConst (MPdot (MPfile ["IntDef"; "BinNums"; "Corelib"]) "Z", "of_N") []).
Notation "'_N.eqb_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "eqb") []).
Notation "'_Z.eqb_'" := (tConst (MPdot (MPfile ["IntDef"; "BinNums"; "Corelib"]) "Z", "eqb") []).

Notation "'_Z0_'" := (tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "Z"); inductive_ind := 0 |} 0 []).
Notation "'_Z1_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z1") []).
Notation "'_Z2_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z2") []).
Notation "'_Z3_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z3") []).
Notation "'_Z4_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z4") []).
Notation "'_Z5_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z5") []).
Notation "'_Z6_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z6") []).
Notation "'_Z7_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z7") []).
Notation "'_Z8_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z8") []).
Notation "'_Z9_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z9") []).
Notation "'_Z10_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z10") []).
Notation "'_Z11_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z11") []).
Notation "'_Z12_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z12") []).
Notation "'_Z13_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z13") []).
Notation "'_Z14_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z14") []).
Notation "'_Z15_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z15") []).
Notation "'_Z16_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z16") []).
Notation "'_Z17_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z17") []).
Notation "'_Z18_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z18") []).
Notation "'_Z19_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z19") []).
Notation "'_Z20_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z20") []).
Notation "'_Z21_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z21") []).
Notation "'_Z22_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z22") []).
Notation "'_Z23_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z23") []).
Notation "'_Z24_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z24") []).
Notation "'_Z25_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z25") []).
Notation "'_Z26_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z26") []).
Notation "'_Z27_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z27") []).
Notation "'_Z28_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z28") []).
Notation "'_Z29_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z29") []).
Notation "'_Z30_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z30") []).
Notation "'_Z31_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z31") []).
Notation "'_Z32_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z32") []).
Notation "'_Z4095_'" := (tConst (MPfile ["Picinae_armv7_lifter"; "Picinae"], "Z4095") []).

(* Compute if a quoted term is a constant of type postive/N *)
Fixpoint is_positivequot t :=
  match t with
  | tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "positive"); inductive_ind := 0 |} 2 [] => true
  | tApp (tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "positive"); inductive_ind := 0 |} 0 []) (t'::nil)
  | tApp (tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "positive"); inductive_ind := 0 |} 1 []) (t'::nil) => is_positivequot t'
  | _ => false
  end.

Definition is_Nquot t :=
  match t with
  | tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "N"); inductive_ind := 0 |} 0 [] => true
  | tApp (tConstruct {| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "N"); inductive_ind := 0 |} 1 []) (t'::nil)  => is_positivequot t'
  | _ => false
  end.
Notation "'_Nmind_'" := ({| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "N"); inductive_ind := 0 |}).
Notation "'_0%N_'" := (tConstruct _Nmind_ 0 []).
Notation "'_Npos_'" := (tConstruct _Nmind_ 1 []).
Notation "'_positive_mind_'" := ({| inductive_mind := (MPfile ["BinNums"; "Numbers"; "Corelib"], "positive"); inductive_ind := 0 |}).
Notation "'_xI_'" := (tConstruct _positive_mind_ 0 []).
Notation "'_xO_'" := (tConstruct _positive_mind_ 1 []).
Notation "'_xH_'" := (tConstruct _positive_mind_ 2 []).
Notation "'_xO:' n" := (tApp _xO_ n::nil) (at level 55).
Notation "'_xI:' n" := (tApp _xI_ n::nil) (at level 55).
Notation "'_1%N_'" := (tApp _Npos_ [_xH_]).
Notation "'_2%N_'" := (tApp _Npos_ [tApp _xO_ [_xH_]]).
Notation "'_3%N_'" := (tApp _Npos_ [tApp _xI_ [_xH_]]).
Notation "'_4%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [_xH_]]]).
Notation "'_5%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [_xH_]]]).
Notation "'_6%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [_xH_]]]).
Notation "'_7%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [_xH_]]]).
Notation "'_8%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [_xH_]]]]).
Notation "'_9%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xO_ [_xH_]]]]).
Notation "'_10%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xO_ [_xH_]]]]).
Notation "'_11%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xO_ [_xH_]]]]).
Notation "'_12%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xI_ [_xH_]]]]).
Notation "'_13%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xI_ [_xH_]]]]).
Notation "'_14%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xI_ [_xH_]]]]).
Notation "'_15%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [_xH_]]]]).
Notation "'_16%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]).
Notation "'_17%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]).
Notation "'_18%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]).
Notation "'_19%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]).
Notation "'_20%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xI_ [tApp _xO_ [_xH_]]]]]).
Notation "'_21%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xI_ [tApp _xO_ [_xH_]]]]]).
Notation "'_22%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xI_ [tApp _xO_ [_xH_]]]]]).
Notation "'_23%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xO_ [_xH_]]]]]).
Notation "'_24%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xI_ [_xH_]]]]]).
Notation "'_25%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xO_ [tApp _xI_ [_xH_]]]]]).
Notation "'_26%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xO_ [tApp _xI_ [_xH_]]]]]).
Notation "'_27%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xO_ [tApp _xI_ [_xH_]]]]]).
Notation "'_28%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xI_ [tApp _xI_ [_xH_]]]]]).
Notation "'_29%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xO_ [tApp _xI_ [tApp _xI_ [_xH_]]]]]).
Notation "'_30%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [_xH_]]]]]).
Notation "'_31%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [_xH_]]]]]).
Notation "'_32%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]]).
Compute $quote 64.
Notation "'_64%N_'" := (tApp _Npos_ (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: [_xH_]))))))).
Notation "'_128%N_'" := (tApp _Npos_ (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: [_xH_])))))))).
Notation "'_256%N_'" := (tApp _Npos_ (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: (_xO: [_xH_]))))))))).
(* Notation "'_64%N_'" := (tApp _Npos_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [tApp _xO_ [_xH_]]]]]]]). *)
Notation "'_4095%N_'" := (tApp _Npos_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [tApp _xI_ [_xH_]]]]]]]]]]]]).

Notation "'_exp_mind_'" := ({| inductive_mind := (MPdot (MPfile ["Picinae_armv7"; "Picinae"]) "IL_arm7", "exp"); inductive_ind := 0 |}).
Notation "'_Var_'" := (tConstruct _exp_mind_ 0 []).
Notation "'_Word_'" := (tConstruct _exp_mind_ 1 []).
Notation "'_Load_'" := (tConstruct _exp_mind_ 2 []).
Notation "'_Store_'" := (tConstruct _exp_mind_ 3 []).
Notation "'_BinOp_'" := (tConstruct _exp_mind_ 4 []).
Notation "'_UnOp_'" := (tConstruct _exp_mind_ 5 []).
Notation "'_Cast_'" := (tConstruct _exp_mind_ 6 []).
Notation "'_Let_'" := (tConstruct _exp_mind_ 7 []).
Notation "'_Unknown_'" := (tConstruct _exp_mind_ 8 []).
Notation "'_Ite_'" := (tConstruct _exp_mind_ 9 []).
Notation "'_Extract_'" := (tConstruct _exp_mind_ 10 []).
Notation "'_Concat_'" := (tConstruct _exp_mind_ 11 []).
Notation "'_binop_mind_'" := ( {| inductive_mind := (MPfile ["Picinae_core"; "Picinae"], "binop_typ"); inductive_ind := 0 |}).
Notation "'_OP_PLUS_'" := (tConstruct _binop_mind_ 0 []).
Notation "'_OP_MINUS_'" := (tConstruct _binop_mind_ 1 []).
Notation "'_OP_TIMES_'" := (tConstruct _binop_mind_ 2 []).
Notation "'_OP_DIVIDE_'" := (tConstruct _binop_mind_ 3 []).
Notation "'_OP_SDIVIDE_'" := (tConstruct _binop_mind_ 4 []).
Notation "'_OP_MOD_'" := (tConstruct _binop_mind_ 5 []).
Notation "'_OP_SMOD_'" := (tConstruct _binop_mind_ 6 []).
Notation "'_OP_LSHIFT_'" := (tConstruct _binop_mind_ 7 []).
Notation "'_OP_RSHIFT_'" := (tConstruct _binop_mind_ 8 []).
Notation "'_OP_ARSHIFT_'" := (tConstruct _binop_mind_ 9 []).
Notation "'_OP_AND_'" := (tConstruct _binop_mind_ 10 []).
Notation "'_OP_OR_'" := (tConstruct _binop_mind_ 11 []).
Notation "'_OP_XOR_'" := (tConstruct _binop_mind_ 12 []).
Notation "'_OP_EQ_'" := (tConstruct _binop_mind_ 13 []).
Notation "'_OP_NEQ_'" := (tConstruct _binop_mind_ 14 []).
Notation "'_OP_LT_'" := (tConstruct _binop_mind_ 15 []).
Notation "'_OP_LE_'" := (tConstruct _binop_mind_ 16 []).
Notation "'_OP_SLT_'" := (tConstruct _binop_mind_ 17 []).
Notation "'_OP_SLE_'" := (tConstruct _binop_mind_ 18 []).
Notation "'_BinOp{' bop ';' lhs ';' rhs '}_'" := (tApp _BinOp_ [bop; lhs; rhs]).
Notation "'_Word{' n ',' w '}_'" := (tApp _Word_ [n;w]).
