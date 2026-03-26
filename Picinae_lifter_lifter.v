Require Import Picinae_metarocq_prelude.
Require Import NArith.
Open Scope N.

Compute $quote 5.
(*
Load MetaRocqPrelude.
Import MonadNotation.
From MetaRocq.Utils Require Import bytestring.
Import String.
Open Scope bs.
 *)
Parameter s : store.
Parameter x:N.
Parameter a:addr.


Locate "<-".
Require Import List.
Print map.
Print zxbits.

Print tCase.
Definition nat_id (n:nat) :=
  match n with
  | O => O
  | S n' => n'
  end.
(* tCase : case_info -> predicate term -> term -> list (branch term) -> term
    case_info: { ci_ind : inductive; ci_npar : nat; ci_relevance : relevance}
      inductive: {inductive_mind: kername; inductive_ind: nat}
      relevance: Relevant | Irrelevant
    predicate: {puinst : Instance.t; pparams: list term; pcontext: list aname; preturn: term}
      Instance.t: list Level.t (????)
    branch: { bcontext: list aname; bbody: term }
      aname: binder_annot name

   Just map
 *)
Compute $quote(
fun m P (PO : P 0) (PS : forall n, P (S n)) =>
match m as n return P n with
| 0 => PO
| S n => PS n
end
)%nat.
(*(
tCase
    {|
      ci_ind :=
        {|
          inductive_mind :=
            (MPfile ["Datatypes"; "Init"; "Corelib"], "nat");
          inductive_ind := 0
        |};
      ci_npar := 0;
      ci_relevance := Relevant
    |}
    {|
      puinst := [];
      pparams := [];
      pcontext :=
        [{|
          binder_name := nNamed "n";
          binder_relevance := Relevant
        |}];
      preturn := tApp (tRel 3) [tRel 0]
    |} (tRel 3)
    [{| bcontext := []; bbody := tRel 1 |};
    {|
      bcontext :=
        [{|
            binder_name := nNamed "n";
            binder_relevance := Relevant
          |}];
      bbody := tApp (tRel 1) [tRel 0]
      |}])
*)
Compute $quote nat.
Notation "'_nat_'" := (tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |} []).
Notation "'_natind_'" := ({| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "nat"); inductive_ind := 0 |}).
Compute $quote (fun n => match n with
  | O => O
  | S n' => O
  end).
(*= Lib.tLam "n" _nat_
         (tCase
            {| ci_ind := _natind_; ci_npar := 0; ci_relevance := Relevant |}
            {|
              puinst := [];
              pparams := [];
              pcontext :=
                [{|
                   binder_name := nNamed "n"; binder_relevance := Relevant
                 |}];
              preturn := _nat_
            |} (tRel 0)
            [{| bcontext := []; bbody := tConstruct _natind_ 0 [] |};
             {|
               bcontext :=
                 [{|
                    binder_name := nNamed "n'"; binder_relevance := Relevant
                  |}];
               bbody := tRel 0
             |}])
   : term*)
Compute $quote_rec nat_id.

Inductive color : Set :=
  | Red (c:color): color
  | Blue : color
  | Dark (c:color) : color.

Compute $quote color.
Notation "'_color_'" := (tInd {| inductive_mind := (MPfile ["Picinae_lifter_lifter"; "Picinae"], "color"); inductive_ind := 0 |} []).
Notation "'_colorind_'" := ({| inductive_mind := (MPfile ["Picinae_lifter_lifter"; "Picinae"], "color"); inductive_ind := 0 |}).
(*MetaRocq Run (printQualid "color").*)
Compute $quote (fun c => match c with
                         | Dark c' => Dark c'
                         | Red c' => Red c'
                         | Blue => Blue
                         end
).

Print List.
About map.
Print map.
Fixpoint mapi_ {A B:Type} (f:nat->A->B) (n:nat) (l:list A) : list B :=
  match l with
  | [] => []
  | h::t => f n h :: mapi_ f (Nat.succ n) t
  end.
Definition mapi {A B:Type} (f:nat->A->B) l := mapi_ f 0%nat l.

MetaRocq Run (printQualid "color").

Print mutual_inductive_body.
Print tCase.
Print name.
Search inductive.
Fixpoint tRel_desc (n:nat) :=
  match n with
  | O => [tRel O]
  | S n'=> tRel n :: tRel_desc n'
  end.
Definition inductive_to_case (ind:inductive) : TemplateMonad term:=
  mind <- tmQuoteInductive (inductive_mind ind);;
  match nth_error (ind_bodies mind) (inductive_ind ind) with
  | None => tmFail "inductive index out of bounds"
  | Some indbody => let ctors := ind_ctors indbody in
                    let branches := mapi (fun n c => match cstr_args c with
                                                     | [] => {| bcontext := []; bbody := tConstruct ind n [] |}
                                                     | _::_ => {| bcontext := map decl_name (cstr_args c); bbody := tApp (tConstruct ind n []) (tRel_desc (Nat.pred (length (cstr_args c))))|}
                                                     end) ctors in
                    tmReturn (tCase {| ci_ind := ind; ci_npar := 0; ci_relevance := Relevant |}
                                    {| puinst := []; pparams := []; pcontext := [{| binder_name := nNamed "x"; binder_relevance := Relevant |}]; preturn := (tInd ind []) |}
                                    (tRel 0%nat)
                                    branches)
  end.
Definition qualid_identity (q:qualid) : TemplateMonad unit :=
  glob_ref <- tmLocate1 q ;;
  match glob_ref with
  | IndRef ind => case <- inductive_to_case ind;; tmUnquote (tLambda {| binder_name := nNamed "x"; binder_relevance := Relevant |} (tInd ind []) case) >>= tmPrint
  | _ => tmFail ("["++q++"] not a valid Inductive reference.")
  end.

MetaRocq Run (qualid_identity "term").

(*= Lib.tLam "n" _nat_
         (tCase
            {| ci_ind := _natind_; ci_npar := 0; ci_relevance := Relevant |}
            {|
              puinst := [];
              pparams := [];
              pcontext :=
                [{|
                   binder_name := nNamed "n"; binder_relevance := Relevant
                 |}];
              preturn := _nat_
            |} (tRel 0)
            [{| bcontext := []; bbody := tConstruct _natind_ 0 [] |};
             {|
               bcontext :=
                 [{|
                    binder_name := nNamed "n'"; binder_relevance := Relevant
                  |}];
               bbody := tRel 0
             |}])
   : term*)


Definition constructor_to_branch (tconstr:term) (cb:constructor_body) : branch term :=
  match cstr_args cb with
  | nil =>
  let len := length (cstr_args cb) in
  let bctxt := map decl_name (cstr_args cb) in
  let bbdy := tApp (tConstruct )

       ind_ctors :=
         [{|
            cstr_name := "Red";
            cstr_args :=
              [{|
                 decl_name :=
                   {|
                     binder_name := nNamed "c"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type := tPro "c" (tRel 0) (tRel 1);
            cstr_arity := 1
          |};
          {|
            cstr_name := "Blue";
            cstr_args := [];
            cstr_indices := [];
            cstr_type := tRel 0;
            cstr_arity := 0
          |};
          {|
            cstr_name := "Dark";
            cstr_args :=
              [{|
                 decl_name :=
                   {|
                     binder_name := nNamed "c"; binder_relevance := Relevant
                   |};
                 decl_body := None;
                 decl_type := tRel 0
               |}];
            cstr_indices := [];
            cstr_type := tPro "c" (tRel 0) (tRel 1);
            cstr_arity := 1
          |}];

            [{|
               bcontext :=
                 [{|
                    binder_name := nNamed "c'"; binder_relevance := Relevant
                  |}];
               bbody := tApp (tConstruct _colorind_ 0 []) [tRel 0]
             |}; {| bcontext := []; bbody := tConstruct _colorind_ 1 [] |};
             {|
               bcontext :=
                 [{|
                    binder_name := nNamed "c'"; binder_relevance := Relevant
                  |}];
               bbody := tApp (tConstruct _colorind_ 2 []) [tRel 0]
             |}])

Definition printQualid (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => tmPrint "Quoted inductive: ";; (*tmPrint ind;;*) mib <- (tmQuoteInductive ind.(inductive_mind));; (*tmPrint mib;;*)
    match (ind_bodies mib) with
    | h::nil => let casebody := ind_ctors h in tmPrint casebody
    | _ => tmFail "Could not make identity for mutual inductive type."
    end
  | ConstRef kn => tmPrint "Quoted constant: ";; tmPrint kn;; (tmQuoteConstant kn false) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

MetaRocq Run (printQualid "nat").

Fixpoint monadmap {A B:Type} (f:A->TemplateMonad B) (l:list A) : TemplateMonad (list B) :=
  match l with
  | h::t => fh <- f h;; ft <- monadmap f t;; tmReturn (fh::ft)
  | nil => tmReturn nil
  end.

Time Definition Nify_fn (Nify:term -> TemplateMonad term) (fn:term) (ts:list term): TemplateMonad term :=
  Nts <- monadmap Nify ts ;;
  if fn == _zxbits_ then tmReturn (tApp _xbits_ Nts) else
  if fn == _Z.of_N_ then (match ts with h::nil => Nify h | _ => tmFail "Z.of_N had more than one argument." end) else
  if fn == _Z.eqb_ then tmReturn (tApp _N.eqb_ Nts) else
  match fn with
  | tConst kn _ => _fn_ <- tmQuoteConstant kn true ;;
  tmReturn (tApp fn Nts).

Notation "'_Npow_'" := (tConst (MPdot (MPfile ["BinNatDef"; "NArith"; "Stdlib"]) "N", "pow") []).

Time Definition Nify_fn' (Nify:term -> TemplateMonad term) (fn:term) (ts:list term): TemplateMonad term :=
  Nts <- monadmap Nify ts ;;
  match fn with
  | _Z.of_N_ => match ts with h::nil => Nify h | _ => tmFail "Z.of_N had more than one argument." end
  | _Z.eqb_ => tmReturn (tApp _N.eqb_ Nts)
  | _ => tmReturn (tApp fn Nts)
  end.


Compute $quote (if true then 1 else 2).
Print tCase.
Definition Nify_case (Nify:term -> TemplateMonad term)


Fixpoint Nify t : TemplateMonad term :=
  match t with
  | tApp fn ts => Nify_fn Nify fn ts
      (*| tApp _zxbits_ Zls => Nls <- monadmap Nify Zls ;; tmReturn (tApp _xbits_ Nls)
    (*
  | tApp _zxbits_ (Zx::Zlo::Zhi::nil) => Nx <- Nify Zx ;; Nlo <- Nify Zlo ;; Nhi <- Nify Zhi ;;
      tmReturn (tApp _xbits_ (Nx::Nlo::Nhi::nil))
      *)
  | tApp _Z.of_N_ (n::nil) => tmReturn (Nify n)
  | tApp _Z.eqb_ (Zl::Zr::nil) => tmReturn (tApp _N.eqb_ ((Nify Zl)::(Nify Zr)::nil))
       *)
  | _Z0_ => tmReturn (_0%N_)
  | _Z1_ => tmReturn (_1%N_)
  | _Z2_ => tmReturn (_2%N_)
  | _Z3_ => tmReturn (_3%N_)
  | _Z4_ => tmReturn (_4%N_)
  | _Z5_ => tmReturn (_5%N_)
  | _Z6_ => tmReturn (_6%N_)
  | _Z7_ => tmReturn (_7%N_)
  | _Z8_ => tmReturn (_8%N_)
  | _Z9_ => tmReturn (_9%N_)
  | _Z10_ => tmReturn (_10%N_)
  | _Z11_ => tmReturn (_11%N_)
  | _Z12_ => tmReturn (_12%N_)
  | _Z13_ => tmReturn (_13%N_)
  | _Z14_ => tmReturn (_14%N_)
  | _Z15_ => tmReturn (_15%N_)
  | _Z16_ => tmReturn (_16%N_)
  | _Z17_ => tmReturn (_17%N_)
  | _Z18_ => tmReturn (_18%N_)
  | _Z19_ => tmReturn (_19%N_)
  | _Z20_ => tmReturn (_20%N_)
  | _Z21_ => tmReturn (_21%N_)
  | _Z22_ => tmReturn (_22%N_)
  | _Z23_ => tmReturn (_23%N_)
  | _Z24_ => tmReturn (_24%N_)
  | _Z25_ => tmReturn (_25%N_)
  | _Z26_ => tmReturn (_26%N_)
  | _Z27_ => tmReturn (_27%N_)
  | _Z28_ => tmReturn (_28%N_)
  | _Z29_ => tmReturn (_29%N_)
  | _Z30_ => tmReturn (_30%N_)
  | _Z31_ => tmReturn (_31%N_)
  | _Z32_ => tmReturn (_32%N_)
  | _Z4095_ => tmReturn (_4095%N_)
  | _ => tmReturn (t)
  end.
Locate "=?".

Compute ($quote (zxbits Z1 Z1 Z1)).
Compute Nify ($quote (zxbits Z1 Z1 Z1)).

Compute (is_positivequot ($quote 4%positive)).
Check arm2il : addr -> arm_inst -> stmt.
Check arm_decode : BinNums.Z -> arm_inst.

(* Try to create an arm2il that eliminates intermediate uses of arm_inst everywhere.
   That is a difficult datatype to reify into exp. *)
Timeout 10 Eval hnf in arm2il a (arm_decode (Z.of_N x)).
Eval unfold arm2il, arm_decode2il, arm_decode_64bit_transfer2il, arm_decode_8_16_32bit_transfer2il, arm_decode_b2il, arm_decode_bfx2il, arm_decode_bkpt2il, arm_decode_bl2il, arm_decode_blx_i2il, arm_decode_blx_r2il, arm_decode_branch_block_transfer2il, arm_decode_bx2il, arm_decode_bxj2il, arm_decode_clz2il, arm_decode_coprocessor2il, arm_decode_coproc_m2il, arm_decode_data_i2il, arm_decode_data_misc2il, arm_decode_data_processing2il, arm_decode_data_r2il, arm_decode_data_rd02il, arm_decode_data_rn02il, arm_decode_data_rsr2il, arm_decode_extend2il, arm_decode_extra_load_store2il, arm_decode_extra_ls_i2il, arm_decode_extra_ls_r2il, arm_decode_floating_data_processing2il, arm_decode_halfword_multiply2il, arm_decode_hint2il, arm_decode_hmul2il, arm_decode_load_store2il, arm_decode_ls_i2il,
arm_decode_lsm2il, arm_decode_ls_r2il, arm_decode_media2il, arm_decode_mem_hint_simd2il, arm_decode_misc2il, arm_decode_mov_wt2il, arm_decode_msr_hints2il,
arm_decode_mul2il, arm_decode_multiply2il, arm_decode_packing2il, arm_decode_parallel_add_sub2il, arm_decode_pas2il, arm_decode_pld_i2il, arm_decode_pld_r2il, arm_decode_rev2il, arm_decode_sat2il, arm_decode_saturating_add_sub2il,
arm_decode_signed_multiply2il, arm_decode_simd2il, arm_decode_svc2il, arm_decode_sync_l2il, arm_decode_sync_primitives2il, arm_decode_sync_s2il, arm_decode_unconditional2il, arm_decode_vcmp2il, arm_decode_vcvt_ds2il, arm_decode_vcvt_fpf2il, arm_decode_vcvt_fpi2il, arm_decode_vfp2il,
arm_decode_vfp_other2il, arm_decode_vls2il, arm_decode_vlsm2il, arm_decode_vmov_i2il, arm_decode_vmov_r12il, arm_decode_vmov_r22il, arm_decode_vmrs2il, arm_decode_vreg_ls2il,
arm_decode_vls2il, arm_decode_64bit_transfer2il, arm_decode_8_16_32bit_transfer2il, arm_decode_b2il, arm_decode_bfx2il, arm_decode_bkpt2il, arm_decode_bl2il, arm_decode_blx_i2il, arm_decode_blx_r2il, arm_decode_bx2il, arm_decode_bxj2il, arm_decode_clz2il, arm_decode_data_i2il, arm_decode_extend2il, arm_decode_hint2il, arm_decode_mem_hint_simd2il, arm_decode_mul2il, arm_decode_sat2il, arm_decode_sync_l2il, arm_decode_vlsm2il,
arm_decode_pld_i2il, arm_decode_pld_r2il, arm_decode_simd2il, arm_decode_vmov_r12il, arm_decode_vmov_r22il, arm_decode_vmrs2il
in (arm_decode2il (Z.of_N x) (arm2il a)).
Timeout 10 Eval simpl in (arm_decode2il (Z.of_N x) (arm2il a)).
Goal forall z, z = arm_decode2il (Z.of_N x) (arm2il a).
intros.
unfold arm_decode2il.
unfold arm_decode2il, arm_decode_64bit_transfer2il, arm_decode_8_16_32bit_transfer2il, arm_decode_b2il, arm_decode_bfx2il, arm_decode_bkpt2il, arm_decode_bl2il, arm_decode_blx_i2il, arm_decode_blx_r2il, arm_decode_branch_block_transfer2il, arm_decode_bx2il, arm_decode_bxj2il, arm_decode_clz2il, arm_decode_coprocessor2il, arm_decode_coproc_m2il, arm_decode_data_i2il, arm_decode_data_misc2il, arm_decode_data_processing2il, arm_decode_data_r2il, arm_decode_data_rd02il, arm_decode_data_rn02il, arm_decode_data_rsr2il, arm_decode_extend2il, arm_decode_extra_load_store2il, arm_decode_extra_ls_i2il, arm_decode_extra_ls_r2il, arm_decode_floating_data_processing2il, arm_decode_halfword_multiply2il, arm_decode_hint2il, arm_decode_hmul2il, arm_decode_load_store2il, arm_decode_ls_i2il,
arm_decode_lsm2il, arm_decode_ls_r2il, arm_decode_media2il, arm_decode_mem_hint_simd2il, arm_decode_misc2il, arm_decode_mov_wt2il, arm_decode_msr_hints2il,
arm_decode_mul2il, arm_decode_multiply2il, arm_decode_packing2il, arm_decode_parallel_add_sub2il, arm_decode_pas2il, arm_decode_pld_i2il, arm_decode_pld_r2il, arm_decode_rev2il, arm_decode_sat2il, arm_decode_saturating_add_sub2il,
arm_decode_signed_multiply2il, arm_decode_simd2il, arm_decode_svc2il, arm_decode_sync_l2il, arm_decode_sync_primitives2il, arm_decode_sync_s2il, arm_decode_unconditional2il, arm_decode_vcmp2il, arm_decode_vcvt_ds2il, arm_decode_vcvt_fpf2il, arm_decode_vcvt_fpi2il, arm_decode_vfp2il,
arm_decode_vfp_other2il, arm_decode_vls2il, arm_decode_vlsm2il, arm_decode_vmov_i2il, arm_decode_vmov_r12il, arm_decode_vmov_r22il, arm_decode_vmrs2il, arm_decode_vreg_ls2il,
arm_decode_vls2il, arm_decode_64bit_transfer2il, arm_decode_8_16_32bit_transfer2il, arm_decode_b2il, arm_decode_bfx2il, arm_decode_bkpt2il, arm_decode_bl2il, arm_decode_blx_i2il, arm_decode_blx_r2il, arm_decode_bx2il, arm_decode_bxj2il, arm_decode_clz2il, arm_decode_data_i2il, arm_decode_extend2il, arm_decode_hint2il, arm_decode_mem_hint_simd2il, arm_decode_mul2il, arm_decode_sat2il, arm_decode_sync_l2il, arm_decode_vlsm2il,
arm_decode_pld_i2il, arm_decode_pld_r2il, arm_decode_simd2il, arm_decode_vmov_r12il, arm_decode_vmov_r22il, arm_decode_vmrs2il.
unfold arm2il.
Print Z.of_N.
Abort.

(* Example of zxbits we want to convert to xbits and N
 else
  if (zxbits (Z.of_N x) Z28 Z32 =? Z15)%Z
  then
   if
    (zxbits (zxbits (Z.of_N x) Z20 Z28) Z5 Z8 =? 0)%Z
    || (zxbits (zxbits (Z.of_N x) Z20 Z28) Z5 Z8 =? Z1)%Z
    || (zxbits (zxbits (Z.of_N x) Z20 Z28) Z5 Z8 =? Z2)%Z
    || (zxbits (zxbits (Z.of_N x) Z20 Z28) Z5 Z8 =? Z3)%Z
   then
    if (zxbits (zxbits (Z.of_N x) Z20 Z27) Z4 Z7 =? 0)%Z
    then Move R_PC (Word (a mod 2 ^ 32) 32) $; Exn 4
    else
     if (zxbits (zxbits (Z.of_N x) Z20 Z27) Z4 Z7 =? Z1)%Z
 *)

Print term.

Require Import ZArith.

Locate Z_xbits_nonneg.

  Search Z_xbits.
  Search Z.to_N 0%Z.
Compute arm2il a (arm_decode (Z.of_N x)).
Check arm_prog : store -> addr -> option (N * stmt) .
Print arm_prog.
Print TemplateMonad.
Print term.

Definition printDef (q : qualid): TemplateMonad unit :=
  gref <- tmLocate1 q ;;
  match gref with
  | IndRef ind => mib <- (tmQuoteInductive ind.(inductive_mind));; tmPrint mib
  | ConstRef kn => cstb <- (tmQuoteConstant kn false);; tmPrint cstb
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

Print constant_body.
MetaRocq Run (printDef "xbits").

Compute $quote 1%N.
                     [tApp
                        (tConstruct
                           {|
                             inductive_mind :=
                               (MPfile ["BinNums"; "Numbers"; "Corelib"], "N");
                             inductive_ind := 0
                           |} 1 [])
                        [tApp
                           (tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["BinNums"; "Numbers"; "Corelib"],
                                   "positive");
                                inductive_ind := 0
                              |} 1 [])
                           [tConstruct
                              {|
                                inductive_mind :=
                                  (MPfile ["BinNums"; "Numbers"; "Corelib"],
                                   "positive");
                                inductive_ind := 0
                              |} 2 []]];
Compute printDef "xbits".

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => mib <- (tmQuoteInductive ind.(inductive_mind));; tmPrint mib
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

Compute ($quote arm_prog).
MetaRocq Test Quote arm_prog.
Search arm2il.
