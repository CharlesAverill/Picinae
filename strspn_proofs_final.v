(* Proofs using Picinae for ARM8 Architecture

   Picinae System:
     Copyright (c) 2023 Kevin W. Hamlen
     Computer Science Department
     The University of Texas at Dallas

   These proofs written by:
     Ilan Buzzetti      (Ilan.Buzzetti@UTDallas.edu)
     Shreya Soman       (Shreya.Soman@UTDallas.edu)

   Any use, commercial or otherwise, requires the express permission of
   the author.

   To run this module, first load and compile:
   * Picinae_core
   * Picinae_theory
   * Picinae_finterp
   * Picinae_statics
   * Picinae_armv8_pcode
   * strspn_arm8
   (in that order) and then compile this module using menu option
   Compile->Compile buffer.
 *)

Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_armv8_pcode.
Require Import strspn_arm8.
Require Import strspn_arm8_lemmas_shreya.
Require Import Lia.
Require Import Bool.

(* Only used for bookkeeping *)
Require Import String.

Import ARM8Notations.
Open Scope N.

(* Define post-condition points for strspn: *)
Definition strspn_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1093664872 => true (* UPDATED *)
  | _ => false
  end | _ => false end.

(* The ARM8 lifter creates non-writable code sections. *)
Theorem strspn_nwc: ∀ s2 s1, musl_armv8_a_strspn_armv8 s1 = musl_armv8_a_strspn_armv8 s2.
Proof. reflexivity. Qed.

(* Verify that the lifted IL is type-safe. *)
Theorem strspn_welltyped: welltyped_prog arm8typctx musl_armv8_a_strspn_armv8.
Proof.
  Picinae_typecheck.
Qed.

(* Strspn does not corrupt memory. *)
Theorem strspn_preserves_memory32:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s V_MEM32 = s' V_MEM32).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Strspn does not modify page permissions. *)
Theorem strspn_preserves_readable:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s A_READ = s' A_READ).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Strspn does not corrupt the LR register (call-return safety). *)
Theorem strspn_preserves_lr:
  forall_endstates musl_armv8_a_strspn_armv8 (fun _ s _ s' => s R_LR = s' R_LR).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.


(* acpt string contains all characters of str's i-length prefix.
 *)
Definition post_satis_i (i:N) (m:addr -> N) (str_ptr:addr) (acpt_ptr:addr):=
  ∀j, j < i ->
  (∃ k : N, nilfree m acpt_ptr (k + 1)
    ∧ m Ⓑ[ acpt_ptr ⊕ k ] = m Ⓑ[ str_ptr ⊕ j ]).

(* If the post condition is satisfied for a prefix of length i, and the next character (index i)
   is not zero and in the bitmap then the post condition is satisfied for a prefix of length i+1
 *)
Lemma post_satis_incr :
  ∀ i char mem str_ptr acpt_ptr bitmap_ptr
     (POST:   post_satis_i i mem str_ptr acpt_ptr   )
     (BITMAP: bitarray_str mem bitmap_ptr acpt_ptr  )
     (NEXT:   mem Ⓑ[ str_ptr ⊕ i ] = char            )
     (CHAR_BIT:     bit mem bitmap_ptr char = 1       )
     (CHAR_NOT_NIL: 0 < char                          ),
     post_satis_i (1+i) mem str_ptr acpt_ptr.
Proof.
  intros.
  remember BITMAP as BITMAP2. clear HeqBITMAP2.
  unfold post_satis_i. intros.
  rewrite N.add_1_l, N.lt_succ_r in H.
  rename H into H'.
  destruct (N.lt_trichotomy j i) as [H | [H | Gt]];[ clear H' | clear H' | rewrite N.lt_nge in Gt; contradiction].
    unfold post_satis_i in POST. specialize (POST j). apply POST in H. assumption.
    unfold bitarray_str in BITMAP. specialize (BITMAP char). destruct BITMAP as [H0 _].
    rewrite <-NEXT; apply getmem_bound.
    rewrite CHAR_BIT in H0; destruct H0. apply N.lt_0_1. subst j.
    destruct H0 as [NILFREE CHAR].
    exists x. split.
    assert (H: ∃ j : N, nilfree mem acpt_ptr j ∧ mem Ⓑ[ acpt_ptr ⊕ j ] = char).
      { exists x. split; repeat assumption.
        apply (nilfree_shrink mem acpt_ptr (1+x) x). assumption. lia. }
      rewrite N.add_comm; assumption.
    subst char; assumption.
Qed.

Lemma bitarray_nstr_str :
  ∀ len mem acpt_ptr bitmap_ptr
     (BITNSTR: bitarray_nstr mem bitmap_ptr acpt_ptr len)
     (NIL: mem Ⓑ[ acpt_ptr + len ] = 0),
     bitarray_str mem bitmap_ptr acpt_ptr.
Proof.
unfold bitarray_nstr.
unfold bitarray_str.
intros.
split.
  * intro BIT. apply BITNSTR in BIT. destruct BIT as [j [LEN [NILFREE MEM]]]. exists j. split.
  assumption. rewrite getmem_mod_l. assumption. assumption.
  *
 intro H2; destruct H2 as [j [NILFREE MEM]]. apply BITNSTR. assumption. exists j. split.
  assert (TRI:= N.lt_trichotomy j len). destruct TRI as [LT | [EQ | GT]].
    assumption.
    subst j. unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + len). { lia. } apply NILFREE in H1.
      rewrite NIL in H1. now contradiction H1.
    unfold nilfree in NILFREE. specialize (NILFREE len). assert (H1: len < 1 + j). { lia. } apply NILFREE in H1.
      rewrite  NIL in H1. now contradiction H1.
  split. assumption. rewrite getmem_mod_l in MEM; assumption.
Qed.

(*TODO: put in a section, make pretty, re-format lemma file as well.*)
Definition strspn_invs (m:addr->N) (str_ptr acpt_ptr sp:addr) (acpt_len:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with

  (* 0x4130001c: Entry invariant *)
  |  0x4130001c => Some ( s V_MEM64 = Ⓜm /\ m Ⓨ[ sp ] = 0 /\ s R_X0 = Ⓠstr_ptr 
                          /\ s R_X1 = Ⓠacpt_ptr /\ s R_X2 = Ⓠ (m Ⓑ[ acpt_ptr ]) /\ s R_X3 = Ⓠsp)

  (* 0x41300054: Degenerative Loop (len(acpt)==1) *)
  |  0x41300054 => Some(
(*      ∃ invariant_loc, invariant_loc = "0x41300054"%string -> *)
     ∃ L : N, s V_MEM64 = Ⓜm  /\ s R_X0 = Ⓠstr_ptr /\ s R_X2 = Ⓠ (m Ⓑ[ acpt_ptr ]) /\ s R_X1 = Ⓠ(str_ptr ⊕ L) /\
      m Ⓑ[ acpt_ptr ] ≠ 0 /\ m Ⓑ[ 1 + acpt_ptr ] = 0 /\
      nilfree m str_ptr L /\
      ∀ i : N,  i < L → m Ⓑ[ acpt_ptr ] = m Ⓑ[ str_ptr + i ])

  (* 0x4130002c: Map Maker Loop *)
  |  0x4130002c =>  Some(
(*      ∃ invariant_loc, invariant_loc = "0x4130002c"%string -> *)
     ∃ m' bitmap_ptr L, s R_X3 = Ⓠsp /\ s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(acpt_ptr ⊕ L) /\
      s R_X6 = Ⓠ1 /\
      s V_MEM64 = Ⓜ m' /\
      m' Ⓑ[ acpt_ptr ] ≠ 0 /\ m' Ⓑ[ 1 + acpt_ptr ] ≠ 0 /\
      strlen m' acpt_ptr acpt_len /\ L <= acpt_len /\
      s R_X3 = Ⓠbitmap_ptr ∧ bitarray_nstr m' bitmap_ptr acpt_ptr L /\
      mem_region_unchanged m m' acpt_ptr acpt_len
      /\ m Ⓑ[ acpt_ptr + acpt_len ] = m' Ⓑ[ acpt_ptr + acpt_len ]
      )

  (* 0x41300094: Map Maker->Checker Transition
                 Just turn bitarray_nstr to bitarray_str to make
                 the map checker loop simpler. *)
  |  0x41300094 => Some(
(*      ∃ invariant_loc, invariant_loc = "0x41300094"%string -> *)
     ∃ m' bitmap_ptr L, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(acpt_ptr ⊕ L) /\
      s V_MEM64 = Ⓜ m' /\
      s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m' bitmap_ptr acpt_ptr /\
      mem_region_unchanged m m' acpt_ptr acpt_len
      /\ m Ⓑ[ acpt_ptr + acpt_len ] = m' Ⓑ[ acpt_ptr + acpt_len ])

  (* 0x41300078: Map Checker Loop *)
  |  0x41300078 => Some(
(*      ∃ invariant_loc, invariant_loc = "0x41300078"%string -> *)
     ∃ m' bitmap_ptr L, s R_X0 = Ⓠstr_ptr /\ s R_X1 = Ⓠ(str_ptr ⊕ L) /\
      s V_MEM64 = Ⓜ m' /\
      s R_X3 = Ⓠbitmap_ptr ∧ bitarray_str m' bitmap_ptr acpt_ptr /\
      post_satis_i L m' str_ptr acpt_ptr /\
      nilfree m' str_ptr L /\
      mem_region_unchanged m m' acpt_ptr acpt_len
      /\ m Ⓑ[ acpt_ptr + acpt_len ] = m' Ⓑ[ acpt_ptr + acpt_len ])

  (* 0x41300068: Return Invariant *)
  |  0x41300068 => Some(
     ∃ invariant_loc, invariant_loc = "0x41300068"%string ->
     ∃ L m' , s V_MEM64 = Ⓜ m' /\
      s R_X0 = ⓆL ∧ post_satis_i L m' str_ptr acpt_ptr
                    ∧ ¬ post_satis_i (L+1) m' str_ptr acpt_ptr)
  | _ => None
  end | _ => None end.

(* * * * * * * * * *        ~~ Glossary ~~        * * * * * * * * * -)

  str_ptr : N
      pointer to the string whose prefix is checked
  acpt_ptr : N
      pointer to the string whose characters comprise an OK prefix
  acpt_len : N
      the length of the string starting at acpt_ptr
  s : store
      initial store
  sp : N
      stack pointer
  m : addr -> N
      memory at the start of execution
  t : trace
      execution trace that begins at the entry to the function and
      ends right before the one of the exit points registered in 
      strspn_exit is reach (only one exit point registered)
  s' : store
      the store when exit point x' is reached
  x' : exit
      the exit point that terminates trace t

( * * * * * * * * *         ~~ ~~~~~~~~ ~~        * * * * * * * * * *)
Theorem strspn_partial_correctness:
  ∀ s str_ptr acpt_ptr acpt_len sp m t s' x'
         (* Enter right after "st1" instruction that prepares
            the bitmap. This skips 2 things worth mentioning:
              1) The stackpointer is subtracted 0x20 to make room
                 for the bitmap.
              2) the first character of 'acpt_ptr' is loaded
                 into w2. *)
         (ENTRY: startof t (x',s') = (Addr 0x4130001c,s))
         (MDL: models arm8typctx s)
         (MEM: s V_MEM64 = Ⓜm)
         (STR: s R_X0 = Ⓠstr_ptr)
         (ACPT:  s R_X1 = Ⓠacpt_ptr)
         (ACPT_LEN: strlen m acpt_ptr acpt_len)
         (NO: ~overlap 64 acpt_ptr (N.succ acpt_len) sp 32)
         (SP: s R_X3 = Ⓠsp)
         (* Assume the bitmap addressed by X3 is zero'd because
            the lifted "st1" instruction that does this isn't
            implemented. *)
         (BITMAP: m Ⓨ[ sp ] = 0)
         (CHAR0:  s R_X2 = Ⓠ (m Ⓑ[ acpt_ptr ]))
,
  satisfies_all musl_armv8_a_strspn_armv8 (strspn_invs m str_ptr acpt_ptr sp acpt_len) strspn_exit ((x',s')::t).
Proof.
Local Ltac step := time arm8_step.
intros. unfold satisfies_all.
  apply prove_invs.
  (* Base case: *)
  simpl. rewrite ENTRY. step. repeat (split; try assumption).

  (* Inductive cases *)
  intros.
  eapply startof_prefix in ENTRY; try eassumption.
  eapply preservation_exec_prog in MDL; try (eassumption || apply strspn_welltyped).
  clear - PRE MDL NO ACPT_LEN. rename t1 into t. rename s1 into s.
  (* PRE is the assertion the previous invariant gives us. *)
  destruct_inv 64 PRE.
  destruct PRE as [MEM [BITMAP_0 [STR [ACPT [ACPT_0 BMP]]]]].
  step. step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                   Empty Accept String                       * * *)
  (* * *                     0x41300068: Ret                         * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

    exists "0x41300068"%string. intro LOC.
    apply Neqb_ok in BC.
    exists 0, m. split. assumption. split. reflexivity. split.
    unfold post_satis_i.
    intros. apply N.nlt_0_r in H. contradiction.
    unfold post_satis_i. unfold not. intros.

      specialize (H 0). simpl N.add in H. destruct H. apply N.lt_0_1.
      psimpl in H. assert (Disj:= N.lt_trichotomy x 0). destruct Disj as [Lt | [Eq | Gt]].
      apply N.nlt_0_r in Lt. contradiction.
      subst x. psimpl in H. destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0).
        assert (H:= N.lt_0_1). apply NILFREE in H. psimpl in H. rewrite BC in H. lia.
      destruct H as [NILFREE _]. unfold nilfree in NILFREE. specialize (NILFREE 0). assert (H: 0<1+x). lia.
        apply NILFREE in H. psimpl in H; rewrite BC in H; lia.

  (* 0x4130006c: mov x1, x0 *)
  (*apply N.eqb_neq in BC; remember BC as ACPT_0_NNULL; clear HeqACPT_0_NNULL.*)
  (*Shreya EDIT*)
  apply N.eqb_neq in BC; pose proof BC as ACPT_0_NULL.
  step. step. 
  (* experimenting with how step works *)
  eapply NIStep; [reflexivity|reflexivity|]. 
  let s := fresh "s" in let x := fresh "x" in let XS := fresh "XS" in
  intros s x XS;
  arm8_step_and_simplify XS;
  repeat lazymatch type of XS with
         | s=_ /\ x=_ => destruct XS; subst s x
         | exec_stmt _ (if ?c then _ else _) _ _ =>
             let BC := fresh "BC" in destruct c eqn:BC;
             arm8_step_and_simplify XS
         | exec_stmt _ (N.iter _ _ _) _ _ => fail
         | _ => arm8_step_and_simplify XS
         end;
  try match goal with |- nextinv _ _ _ _ (_ :: ?xs :: ?t) =>
    let t' := fresh t in generalize (xs::t); intro t'; clear t; rename t' into t
  end;
  repeat match goal with [ u:value |- _ ] => clear u
                       | [ n:N |- _ ] => clear n
                       | [ m:addr->N |- _ ] => clear m end;
  try lazymatch goal with |- context [ exitof (N.add ?m ?n) ] => simpl (N.add m n) end;
  try first [ rewrite exitof_none | rewrite exitof_some ].

  step.

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                   Single Character                          * * *)
  (* * *                0x41300054: ldrb w3, [x1]                    * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Loop Iteration 0           * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
    exists 0. apply Neqb_ok in BC0. psimpl; repeat (split; try easy).
    apply nilfree0.
    intros. apply N.nlt_0_r in H. contradiction.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Loop Iteration N           * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  3: {
  destruct PRE as [p [MEM [STR_PTR [ACPT_CHAR_0 [LEN [ACPT_0_NNULL [ACPT_1_NULL [NF PREFIX]]]]]]]].

  step. step. step.
  (* SINGLE CHARACTER: Loop Iteration *)
  step.
  apply Neqb_ok in BC.
  exists (p+1). psimpl.
    repeat (split; try easy).
    apply nilfree_grow; try assumption. now rewrite <-BC in ACPT_0_NNULL.
    intros. destruct (N.lt_trichotomy i p) as [LT | [EQ | GT]].
    apply PREFIX; easy.
    rewrite EQ; easy.
    lia.

  step. step.
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *        Single Character Ret         * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  exists "0x41300068"%string. intro LOC.
  exists p, m. split. reflexivity. split.
  enough (LSMALL: p mod 2 ^ 64 = p); try now rewrite LSMALL. apply N.mod_small.
    apply (nflen_lt m str_ptr p (1+acpt_ptr)); assumption. split.
    unfold post_satis_i. intros. exists 0. split.
      psimpl. unfold nilfree. intros. destruct i.
        psimpl; now symmetry.
        destruct p0; discriminate.
      psimpl. apply PREFIX. assumption.
    unfold post_satis_i. unfold not. intros. apply N.eqb_neq in BC. specialize (H p).
    destruct H as [k [NILFREE NIL]]. lia.
    assert (KZERO: k = 0). { destruct k. reflexivity. unfold nilfree in NILFREE. specialize (NILFREE 1).
      destruct NILFREE; try lia. symmetry; rewrite N.add_comm; assumption.
    }
    rewrite KZERO in NIL; psimpl in NIL. symmetry in NIL. contradiction.
  }

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *                                                             * * *)
  (* * *                       Map Maker                             * * *)
  (* * *                0x4130002c:  ldrb w2, [x1]                   * * *)
  (* * *                0x41300094:  mov  x1,  x0                    * * *)
  (* * *                0x41300078:  ldrb w4, [x1]                   * * *)
  (* * *                                                             * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Map Maker Loop 0           * * *)
  (* * *     0x4130002c:  ldrb w2, [x1]      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  step.
  apply N.eqb_neq in BC. apply N.eqb_neq in BC0.
  (* sp was stored in R_X3 *)
  exists m, sp.
  (* First loop iteration, length should be 0 *)
  exists 0. psimpl.
  do 9 (split; try easy).
  clear - BC BC0 ACPT_LEN ACPT_0_NULL.
  unfold strlen in ACPT_LEN. destruct ACPT_LEN as [NF NULL]. destruct acpt_len; try lia.
  split; try easy.
  split.
  apply bitmap_0_new with (acpt_len:= acpt_len). assumption. all: try assumption.
  split.
  apply mem_eq_region_unchanged.
  reflexivity.
  destruct PRE as [m' [bitmap_ptr [L [SP [STR_PTR [ACPT_L [X6_EQ_1
    [MEM' [ACPT_0_NNULL [ACPT_1_NNULL [STRLEN [L_LT_STRLEN [BITMAP_PTR [BITNSTR ACPT_SAME]]]]]]]]]]]]]].
(*  rewrite MEM' in MEM; inversion MEM as [MEM_EQ]; subst m'; clear MEM; rename MEM' into MEM. *)

  step. step. all: cycle 1.

  step. step. step. step. step. step. step.
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *          Map Maker Loop N           * * *)
  (* * *     0x4130002c:  ldrb w2, [x1]      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  eexists.
  exists bitmap_ptr, (L+1).
  apply N.eqb_neq in BC.
  idtac || clear - BC SP MDL BITNSTR BITMAP_PTR ACPT_1_NNULL ACPT_0_NNULL
    X6_EQ_1 ACPT_L STR_PTR NO ACPT_LEN. clear ACPT_LEN.
  clear tmp tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 tmp9 tmp10 tmp14 tmp15 tmp16 tmp17
    t.

  rewrite BITMAP_PTR in SP; inversion SP; subst sp; clear SP.
  assert (NO': ¬ overlap 64 acpt_ptr acpt_len bitmap_ptr 32)
    by (apply (noverlap_shrink _ acpt_ptr (N.succ acpt_len)); [psimpl;lia | assumption]).

  repeat (
    match goal with
    | [|- bitarray_nstr _ _ _ _] => idtac
(*     | [|- and (not (eq _ 0)) _] => idtac || (split; apply getmem_noverlap) *)
    | _  =>  split; psimpl; try easy
    end
  ).
  rewrite getmem_noverlap; try assumption; try psimpl.
  change acpt_ptr with (0 + acpt_ptr) at 1; rewrite (N.add_comm 0 acpt_ptr).
  apply (noverlap_index_index 64 acpt_ptr acpt_len bitmap_ptr 32 0 1 (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3) 8);
    try (assumption).
    simpl; destruct (N.lt_trichotomy 1 acpt_len) as [Lt | [Eq | Gt]]; try lia.
      destruct acpt_len; try lia. unfold strlen in STRLEN. destruct STRLEN as [NF' ZERO].
      rewrite N.add_0_r in ZERO; contradiction.
    apply msbits_indexed_section_contained.
  (* proving m' (B) [1 + acpt_ptr] <> 0 *)
  rewrite getmem_noverlap; try assumption. rewrite (N.add_comm 1 acpt_ptr).
  apply (noverlap_index_index 64 acpt_ptr acpt_len bitmap_ptr 32); try assumption; try lia.
    idtac || clear - L_LT_STRLEN ACPT_1_NNULL ACPT_0_NNULL STRLEN BC NO.
    simpl. destruct (N.lt_ge_cases acpt_len 2); try assumption.
    (* showing a contradiction if acpt_len < 2 *) {
    destruct acpt_len. unfold strlen in STRLEN; destruct STRLEN as [NF ZERO].
      rewrite N.add_0_r in ZERO; contradiction.
    destruct p; try (destruct p; discriminate).
    unfold strlen in STRLEN. destruct STRLEN as [NF F]; rewrite N.add_comm in F.
    destruct L; try contradiction.
    }
    apply msbits_indexed_section_contained.
  apply nilfree_noverlap.
  change acpt_ptr with (0 + acpt_ptr) at 1; rewrite (N.add_comm 0 acpt_ptr).
  apply (noverlap_index_index 64 acpt_ptr acpt_len bitmap_ptr 32);
    try (assumption || lia); apply msbits_indexed_section_contained.
    unfold strlen in STRLEN; destruct STRLEN as [T _]; assumption.
  rewrite getmem_noverlap. unfold strlen in STRLEN. destruct STRLEN as [NF NULL]. assumption.
  apply noverlap_index_index with (len1:=N.succ acpt_len) (len2:=32); try (assumption || lia).
    apply msbits_indexed_section_contained.
  clear - STRLEN ACPT_1_NNULL ACPT_0_NNULL L_LT_STRLEN BC. unfold strlen in STRLEN.
  destruct (N.lt_trichotomy (1+L) acpt_len) as [Lt | [Eq | Gt]];[apply N.lt_le_incl; assumption | | ].
    now rewrite Eq.
    destruct (N.lt_trichotomy L acpt_len) as [Lt' | [Eq' | Gt']]; try lia. subst L. now destruct STRLEN.
  (* bitarray_nstr_incr *)
  {
  apply bitarray_nstr_str_final with (acpt_len:= acpt_len). all: try assumption.
  }

  change ((m' [Ⓠ
  bitmap_ptr + (m' Ⓑ[ acpt_ptr + L ] >> 6 << 3)
  := 1 << m' Ⓑ[ acpt_ptr + L ] mod 64 .| m' Ⓠ[ bitmap_ptr +
  (m'Ⓑ[ acpt_ptr + L] >>6 <<3)]])) 
  with (changed_mem bitmap_ptr acpt_ptr L m').

  assert(mem_region_unchanged m' (changed_mem bitmap_ptr acpt_ptr L m') acpt_ptr acpt_len).
  {
    apply memory_checker with (m:= m). all: try easy. 
  }
  destruct ACPT_SAME as [ACPT_SAME ACPT_SAME_2].

  unfold mem_region_unchanged.
  intros. 
  specialize (ACPT_SAME i H0). specialize (H i H0). rewrite <- H. assumption.
  
  destruct ACPT_SAME as [ACPT_SAME ACPT_SAME_2].
  {
    assert(LEN_NEQ: L <> acpt_len ).
    unfold strlen in STRLEN. destruct STRLEN.
    assert(L = acpt_len \/ L <> acpt_len). lia.
    destruct H1. rewrite H1 in BC. contradiction. assumption.
    assert(LEN_LT: L < acpt_len). lia.

    rewrite ACPT_SAME_2.
    rewrite getmem_frame. reflexivity.
    apply noverlap_sep.
    apply noverlap_index_index with (len1:= N.succ acpt_len) (len2:= 32) (index1:= acpt_len) (index2:= (m Ⓑ[ acpt_ptr + L ] >> 6 << 3)) (size1:= 1) (size2:= 8) in NO.
    unfold mem_region_unchanged in ACPT_SAME. specialize (ACPT_SAME L LEN_LT). rewrite ACPT_SAME in NO.
    eapply noverlap_symmetry. assumption. lia.
    eapply msbits_indexed_section_contained.

    apply noverlap_sep.
    apply noverlap_index_index with (len1:= N.succ acpt_len) (len2:= 32) (index1:= acpt_len) (index2:= (m Ⓑ[ acpt_ptr + L ] >> 6 << 3)) (size1:= 1) (size2:= 8) in NO.
    unfold mem_region_unchanged in ACPT_SAME. specialize (ACPT_SAME L LEN_LT). rewrite ACPT_SAME in NO.
    assumption. lia.
    eapply msbits_indexed_section_contained.

  }

  all: cycle -1.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *     Maker -> Checker Transition     * * *)
  (* * *      0x41300094:  mov  x1,  x0      * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  eexists. exists bitmap_ptr, L.
  do 3 (split; try easy). split; try easy. split.
  apply bitarray_nstr_str with (len:=L). assumption.
  apply Neqb_ok in BC.
  clear - BC.
  assumption.
  assumption.
  all: cycle 1.

  destruct PRE as [m' [bitmap_ptr [L [STR_PTR [ACPT_L [MEM' [BITMAP_PTR [BITARRAY ACPT_SAME]]]]]]]].
  step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *         Map Checker Loop 0          * * *)
  (* * *      0x41300078:  ldrb w4, [x1]     * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  exists m', bitmap_ptr, 0. psimpl.
  repeat (split; try easy).
  unfold post_satis_i. intros.
  apply N.nlt_0_r in H. contradiction.
  intros i Ilt0; now apply N.nlt_0_r in Ilt0.
  (* * * * * * * * * * * * * * * * * * * * * * * *)

  destruct PRE as [m' [bitmap_ptr [L [STR_PTR [STR_L [MEM' [BITMAP_PTR [BITARRAY_STR [POST [NF ACPT_SAME]]]]]]]]]].
  step. step.

  all: cycle 1.
  step. step. step. step.
  all: cycle 1. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *         Map Checker Loop N          * * *)
  (* * *      0x41300078:  ldrb w4, [x1]     * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  eexists. exists bitmap_ptr, (L+1).
  clear tmp tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 tmp9 tmp10 tmp11 tmp12
    tmp13 tmp14 tmp15 tmp16 tmp17 t.
  apply N.eqb_neq in BC, BC0.
  do 6 (split ; try (psimpl; easy)).
  rewrite N.add_comm. apply post_satis_incr with (char:=m' Ⓑ[ str_ptr + L ]) (bitmap_ptr:=bitmap_ptr);
    try (assumption || rewrite getmem_mod_l; reflexivity).
  apply map_checker_n_helper; assumption.
  destruct (m Ⓑ[ str_ptr + L ]); (congruence || lia).

  rewrite N.add_comm. split. apply nilfree_grow; assumption.
  assumption.
  (* * * * * * * * * * * * * * * * * * * * * * * *)


  step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *        Ret: Checker Found \0        * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  exists "0x41300068"%string. intro LOC_NOW.
  exists L, m'. clear tmp tmp0 tmp1 tmp2 tmp3 t LOC_NOW.
  apply Neqb_ok in BC.
  split. reflexivity.
  split.
    enough (LSMALL: L mod 2 ^ 64 = L); try now rewrite LSMALL. apply N.mod_small.
    apply (nflen_lt m' str_ptr L (str_ptr+L)); assumption. split.

  assumption. 

  unfold post_satis_i. intro.
  specialize (H L). assert (HELP:L < L+1) by lia. apply H in HELP. destruct HELP.
  destruct H0 as [NFAcpt Z]. unfold nilfree in NFAcpt. specialize (NFAcpt x). assert (HELP:x<x+1) by lia; apply NFAcpt in HELP.
  do 2 rewrite getmem_mod_l in Z.  rewrite BC in Z; congruence.

  step. step. step.

  (* * * * * * * * * * * * * * * * * * * * * * * *)
  (* * *   Ret: Checker Found Unlisted Char  * * *)
  (* * * * * * * * * * * * * * * * * * * * * * * *)
  exists "0x41300068"%string. intro LOC_NOW.
  exists L, m'.
  clear tmp tmp0 tmp1 tmp2 tmp3 tmp4 tmp5 tmp6 tmp7 tmp8 tmp9 tmp10 tmp11 tmp12 tmp13 tmp14 tmp15
    tmp16 tmp17 t LOC_NOW Hsv n.
  split. reflexivity.
  apply N.eqb_neq in BC. apply Neqb_ok in BC0.
  split.
  enough (LSMALL: L mod 2 ^ 64 = L); try now rewrite LSMALL. apply N.mod_small.
    unfold strlen in ACPT_LEN; destruct ACPT_LEN as [_ ZERO].
    apply (nflen_lt m' str_ptr L (acpt_ptr+acpt_len)). assumption. 
    unfold mem_region_unchanged in ACPT_SAME. destruct ACPT_SAME as [ACPT_SAME ACPT_SAME2].
    rewrite <- ACPT_SAME2.
     assumption.

  split. assumption.
  
  unfold post_satis_i. intro H. specialize (H L). assert (HELP:L<L+1) by lia; apply H in HELP; clear H. (*; destruct HELP as [k [NF' CHAREQ']].*)
  clear - BITARRAY_STR HELP BC0.
  unfold bitarray_str in BITARRAY_STR. specialize (BITARRAY_STR (m' Ⓑ[ str_ptr + L ])). assert (HELP':= getmem_bound 64 LittleE 1 m' (str_ptr + L )).
  change (2 ^ (IL_arm8.Mb * 1)) with 256 in HELP'.
  apply BITARRAY_STR in HELP'.
  rewrite getmem_mod_l in HELP.
  destruct HELP as [k [HNF HMEQ]]. rewrite N.add_comm in HNF.
  assert (HELP: ∃ j : N, nilfree m' acpt_ptr (1 + j) ∧ m' Ⓑ[ acpt_ptr ⊕ j ] = m' Ⓑ[ str_ptr + L ])
    by (exists k; split; assumption).
  (* end of massage *)
  rewrite <-HELP' in HELP; clear - HELP BC0.
  eapply map_no_value in BC0.
  contradiction.

Qed. 