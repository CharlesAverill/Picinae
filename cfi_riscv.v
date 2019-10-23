Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Picinae_riscv.
Require Import List.

Import RISCVNotations.

(* A CFI policy ascribes the following information to each original instruction:
   (1) an optional "input identifier", which uniquely labels the equivalence
       class of indirect jumps that may target the instruction;
   (2) an "output identifier", which identifies the equivalence class of targets
       to which this instruction is permitted to indirectly jump; and
   (3) a list of permissible "static destinations", which are the relative indexes
       of instructions to which the instruction may directly jump (or fall thru).
   Static destination sets are specified separately from dynamic destination sets
   because the former need not constitute equivalence classes, whereas the latter
   must (for this particular enforcement algorithm). *)
Definition policy := list (option N * (N * list N)).

(* Our rewriter maintains data in the following data structure:
   iid = input identifier (see above), or None if no dynamic jumps may target
         this instruction
   oid = output identifier (see above), which is ignored if this instruction
         is not a dynamic jump
   sd = static destination list for this instruction
   n = original instruction's encoding
   sb = remembers whether we've selected a short (true) or long (false)
        encoding of this instruction after rewriting *)
Inductive instr_data := Data (iid:option N) (oid:N) (sd:list N) (n:N) (sb:bool).



(* Helper functions to encode/decode branch/jump instruction operands: *)

Definition encode_branch_offset o :=
  ((o .& 7) << 9) .| ((o .& 504) << 22) .| ((o .& 512) >> 2) .| ((o .& 1024) << 21).

Definition decode_branch_offset n :=
  ((n >> 9) .& 7) .| ((n >> 22) .& 504) .| ((n << 2) .& 512) .| ((n >> 21) .& 1024).

Definition encode_jump_offset o :=
  ((o .& 511) << 22) .| ((o .& 512) << 11) .| ((o .& 261120) << 2) .| ((o .& 262144) << 13).

Definition decode_jump_offset n :=
  ((n >> 22) .& 511) .| ((n >> 11) .& 512) .| ((n >> 2) .& 261120) .| ((n >> 13) .& 262144).

(* Compute the size of the rewritten instruction block that will replace
   a given instruction during rewriting: *)
Definition newsize d :=
  match d with Data iid _ _ n sb =>
    match iid with None => 0 | Some _ => 1 end +
    (if n .& 127 =? 103 then 11 else 1) +
    (if sb then 0 else 1)
  end.

Fixpoint sumsizes l := fold_left (fun c d => c + newsize d) l 0.

(* Compute the signed relative index for a rewritten branch/jump target.  Inputs are:
   m = min unrepresentable positive index (indexes in range [m,2m) are negative)
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for the instruction being rewritten
   c = count of instructions within rewritten code block d including and following
       the branch/jump instruction within the block whose target operand is being
       computed by newoffset
   l2 = list of data for instructions following this one (in forward order)
   i = relative index of the original destination (to be converted) *)
Definition newoffset m l1 d c l2 i :=
  if i <? m then Z.of_N (c + sumsizes (firstn (N.to_nat i) l2))
            else Z.opp (Z.of_N (newsize d - c + sumsizes (firstn (N.to_nat (1+m-i)) l1))).

(* Initially we conservatively select a long-jump encoding of all rewritten jumps.
   The following function finds jumps whose destinations are near enough to permit
   a short encoding, and shortens them accordingly.  It can potentially be
   called multiple times on its own output to achieve more compression, though usually
   one call finds almost everything that can be shortened. *)
Fixpoint shrink l1 l2 :=
  match l2 with nil => List.rev l1 | ((Data iid oid sd n b) as d)::t => shrink ((Data iid oid sd n (orb b
    (let op := n .& 127 in
     if orb (op =? 99) (op =? 103) then (* remapped branch or guarded jalr *)
       let o := newoffset 1024 l1 d (if op =? 99 then 1 else 2) t (decode_branch_offset n) in
       (andb (-1024 <=? o) (o <? 1024))%Z
     else true (* other instruction (unshrinkable) *)
    )))::l1) t
  end.

(* Generate the tag instruction that implements the "input identifier" in
   the rewritten version of an instruction. *)
Definition newtag d :=
  match d with Data None _ _ _ _ => nil
             | Data (Some iid) _ _ _ _ => ((iid << 12) .| 55)::nil
  end.

(* Generate a rewritten static jump instruction.  Inputs are:
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for instruction being rewritten
   i2 = index of instruction succeeding the one being rewritten
   l2 = list of data for original instructions following this one (in forward order)
   i = original target index of instruction being rewritten *)
Definition newjump l1 d i2 l2 i :=
  let o' := newoffset 262144 l1 d i2 l2 i in
  if (andb (-262144 <=? o') (o' <? 262144))%Z then
    Some ((111 .| encode_jump_offset (Z.to_N (Z.modulo o' 524288)))::nil)
  else None.

(* Generate a rewritten static branch.  Inputs are the same as for newjump.
   If the target is "near" the source, this generates a short-form encoding.
   Otherwise it generates a long encoding that conditionally jumps over a
   long-jump to the target (where the condition is inverted from the original
   instruction being rewritten). *)
Definition newbranch l1 d i2 l2 i :=
  match d with Data _ _ sd n sb =>
    if sb then
      let o' := newoffset 1024 l1 d i2 l2 i in
      if (andb (-1024 <=? o') (o' <? 1024))%Z then
        Some (((n .& 33550463) .| encode_branch_offset (Z.to_N (Z.modulo o' 2048)))::nil)
      else None
    else match newjump l1 d i2 l2 i with None => None | Some j =>
      Some ((n .& 33550463 .^ 4096 .| 1024)::j)
    end
  end.

(* Rewrite an indirect jump.  The guard code reads the code bytes at the impending
   target to see whether there is a tag instruction there that matches this
   instruction's "output identifier".  If not, it jumps to the end of the rewritten
   code segment (where there can be an abort handler or nothing, the latter causing
   a segmentation fault).  Otherwise it jumps to the target. *)
Definition newijump l1 d l2 :=
  match d with Data iid oid sd n sb =>
    let rs1 := (n >> 15) .& 31 in
    let tmp1 := if rs1 =? 31 then 29 else 31 in
    let tmp2 := if rs1 =? 30 then 29 else 30 in
    let tmp3 := if 29 <? rs1 then rs1 else 29 in
    match newbranch l1 (Data iid oid sd (4195 .| (tmp1 << 15) .| (tmp2 << 20)) sb)
                    2 l2 (N.of_nat (List.length l2))
    with None => None | Some br => Some (
      (19 .| (tmp3 << 7) .| (rs1 << 15) .| (n .& 4293918720)):: (* Addi tmp3, rs1, imm *)
      (8195 .| (tmp1 << 7) .| (tmp3 << 15))::                   (* Lw tmp1, tmp3, 0 *)
      (133197843 .| (tmp2 << 7) .| (tmp1 << 15))::              (* Andi tmp2, tmp1, 127 *)
      (6243 .| (tmp2 << 15))::                                  (* Bne tmp2, x0, +16 *)
      (5263379 .| (tmp1 << 7) .| (tmp1 << 15))::                (* Srli tmp1, tmp1, 5 *)
      (51 .| (tmp3 << 7) .| (tmp3 << 15) .| (tmp1 << 20))::     (* Add tmp3, tmp3, tmp1 *)
      (8195 .| (tmp1 << 7) .| (tmp3 << 15))::                   (* Lw tmp1, tmp3, 0 *)
      (55 .| (tmp2 << 7) .| (oid << 12))::                      (* Lui tmp2, out_id *)
      (57696275 .| (tmp2 << 7) .| (tmp2 << 15))::               (* Ori tmp2, tmp2, 55 *)
      (br ++                                                    (* Bne tmp1, tmp2, abort *)
      ((n .& 4095) .| (tmp3 << 15))::nil))                      (* Jalr rd, tmp3, 0 *)
    end
  end.

(* Test membership of a number (N) in a list of numbers. *)
Definition mem := in_dec N.eq_dec.

(* Rewrite an old instruction to a new instruction block.  Inputs:
   l1 = list of data for instructions preceding this one, in reverse order
   d = data for instruction being rewritten
   l2 = list of data for instructions following this one (in forward order) *)
Definition newinstr l1 d l2 :=
  match d with Data _ _ sd n _ => (* sd = policy-permitted static destinations *)
    if n .& 4095 =? 55 then (* Lui r0, ... *)
      if mem 1 sd then Some (16435::nil) else None (* Xor r0, r0, r0 *)
    else let op := n .& 127 in
    if op =? 99 then (* Bcc *)
      let o := decode_branch_offset n in
      if mem 1 sd then if mem o sd then newbranch l1 d 1 l2 (decode_branch_offset n)
      else None else None
    else if op =? 103 then newijump l1 d l2 (* Jalr *)
    else if op =? 111 then (* Jal *)
      let o := decode_jump_offset n in
      if mem n sd then newjump l1 d 1 l2 (decode_jump_offset n) else None
    else
      if mem 1 sd then Some (n::nil) else None
  end.

(* Rewrite all instructions in a code block.
   Called as: newinstrs nil l2
   where l2 is a list of instruction data (see newcode) *)
Fixpoint newinstrs l1 l2 :=
  match l2 with nil => Some nil | d::t =>
    match newinstr l1 d t, newinstrs (d::l1) t with
    | None, _ | _, None => None
    | Some x, Some y => Some ((newtag d ++ x)::y)
    end
  end.

(* Rewrite a code block according to a policy.  Inputs:
   pol = the policy specification
   l = the list of 32-bit numbers that comprises the original code *)
Definition todata x :=
  match x with ((iid,(oid,sd)),n) => Data iid oid sd n false end.
Definition newcode (pol:policy) l :=
  let d := shrink nil (map todata (combine pol l)) in
  if sumsizes d <? 2^30 then newinstrs nil d else None.



(* Now we define "soundness" of a CFI implementation.  Soundness is unavoidably
   parameterized by a (not necessarily one-to-one) mapping from the rewritten
   instructions to the original instructions, since the policy specifies which
   original instructions may flow to which, but the policy must be enforced on
   a different set of (rewritten) instructions.  For our CFI implementation, we
   specify this mapping as the "indexmap" function defined below: *)

Fixpoint indexmap' (l': list (list N)) i' :=
  (match l' with nil => O | b::t =>
     if i' <? length b then O else S (indexmap' t (i' - length b))
   end)%nat.

Definition indexmap pol l i' :=
  match newcode pol l with None => O | Some l' => indexmap' l' i' end.


(* We define "safety" as a proposition on policies satisfied by an
   arbitrary indexmap and rewriter function r: *)

Definition blockboundary (l': list (list N)) i' :=
  exists n, i' = length (concat (firstn n l')).

(* new code jumps to policy-permitted block *)
Definition policytarget (pol:policy) (im: nat -> nat) i i' :=
  match nth_error pol (im i) with
  | Some (_,(oid,sd)) => In (N.of_nat (i' - i)%nat) sd \/
      exists out, nth_error pol (im i') = Some (Some oid,out)
  | None => False
  end.

Definition safety (pol:policy) r im :=
  forall (l: list N) l' h s0 m0 i0 n s s' q i i' x

    (* Assume rewriter r returns rewritten code l' (instead of rejecting or aborting) *)
    (NC: r l = Some l')

    (* Let m0 be the memory contents at program-start *)
    (S0: s0 V_MEM32 = VaM m0 32)

    (* Assume m0 contains the rewritten code starting at address 0 *)
    (CS: forall j n, nth_error (concat l') j = Some n ->
                     getmem LittleE 4 m0 (4 * N.of_nat j) = n)

    (* Assume execution of the new code begins at address i0, which is a block boundary. *)
    (BB: blockboundary l' i0)

    (* Let i be the index of an instruction reached during execution (located at address 4*i). *)
    (XP0: exec_prog h rv_prog (N.of_nat i0) s0 n s (Exit (4 * N.of_nat i)))

    (* Assume the code section is non-writable. *)
    (NWC: forall m w j, s V_MEM32 = VaM m w -> (j < length (concat l'))%nat ->
          getmem LittleE 4 m (4 * N.of_nat j) = getmem LittleE 4 m0 (4 * N.of_nat j))

    (* Assume memory outside the code section is non-executable. *)
    (NXD: forall e w j, s A_EXEC = VaM e w -> (length (concat l') <= j)%nat ->
                        e (4 * N.of_nat j) = N0)

    (* Let q be the IL statement that encodes instruction i. *)
    (LU: rv_prog s (4 * N.of_nat i) = Some (4,q))

    (* Let s' and x be the store and exit state after executing q. *)
    (XS: exec_stmt h s q s' x)

    (* Let i' be the index of the instruction to which q transfers control next. *)
    (EX: exitof (4 * N.of_nat i + 4) x = Exit (4 * N.of_nat i')),

  (* Then either
      (A) i' is in the same block as i (in which case the policy never prohibits it), or
      (B) i' is the start of a block permitted by the policy as a destination of i. *)
  im l i = im l i' \/
  (blockboundary l' i' /\ policytarget pol (im l) i i').



Lemma ebo_bitmask:
  forall o, encode_branch_offset o .& 33550463 = 0.
Proof.
  intro. unfold encode_branch_offset.
  rewrite 3!N.land_lor_distr_l, 3!N.shiftl_land, N.shiftr_land, <- 4!N.land_assoc, 4!N.land_0_r.
  reflexivity.
Qed.

Lemma newinstr_nonnil:
  forall l1 d l2, newinstr l1 d l2 <> Some nil.
Proof.
  intros. destruct d. unfold newinstr.
  destruct (_ =? _). destruct mem; discriminate.
  destruct (_ =? _). repeat (discriminate + destruct mem). unfold newbranch. destruct sb.
    destruct (_ && _)%bool; discriminate.
    destruct (newjump _ _ _ _ _); discriminate.
  destruct (_ =? _). unfold newijump.
    destruct (newbranch _ _ _); discriminate.
  destruct (_ =? _). destruct mem; [|discriminate]. unfold newjump.
    destruct (_ && _)%bool; discriminate.
  destruct mem; discriminate.
Qed.

Lemma skipn_newinstrs:
  forall i l1 l2 l' (NI: newinstrs l1 l2 = Some l'),
  newinstrs (rev (firstn i l2) ++ l1) (skipn i l2) = Some (skipn i l').
Proof.
  induction i; intros.
    exact NI.
    destruct l2 as [|d l2].
      inversion NI; subst. reflexivity.

      simpl in NI. specialize (IHi (d::l1) l2).
      destruct (newinstr l1 d l2), (newinstrs _ _); try discriminate.
      specialize (IHi l0 (eq_refl _)).
      inversion NI; subst. simpl. rewrite <- app_assoc. exact IHi.
Qed.

Lemma nth_skipn:
  forall {A} i (l:list A), nth_error l i = hd_error (skipn i l).
Proof.
  induction i; intros; destruct l; (reflexivity + apply IHi).
Qed.

Lemma skipn_S:
  forall {A} i (l:list A), skipn (S i) l = tl (skipn i l).
Proof.
  induction i; intros.
    reflexivity.
    destruct l. reflexivity. apply IHi.
Qed.

Corollary nth_newinstrs:
  forall l1 l2 l' i (NI: newinstrs l1 l2 = Some l'),
  nth_error l' i = match nth_error l2 i with None => None | Some d =>
    option_map (fun l => newtag d ++ l)
               (newinstr (rev (firstn i l2) ++ l1) d (skipn (S i) l2))
  end.
Proof.
  intros. rewrite 2!nth_skipn, skipn_S. apply (skipn_newinstrs i) in NI.
  destruct (skipn i l2) as [|d l3] eqn:I2.
    inversion NI. reflexivity.
    simpl in *. destruct (newinstr _ d l3).
      destruct (newinstrs _ l3). inversion NI. reflexivity. discriminate.
      discriminate.
Qed.

Lemma indexmap_sum:
  forall l n i (LEN: (n < length l)%nat),
  (indexmap' l (length (concat (firstn n l)) + i) = n + indexmap' (skipn n l) i)%nat.
Proof.
  induction l; intros.
    contradict LEN. apply Nat.nlt_0_r.
    destruct n.
      reflexivity.

      rewrite Nat.add_succ_l, <- IHl by apply lt_S_n, LEN.
      simpl. rewrite app_length, <- Nat.add_assoc.
      rewrite (proj2 (Nat.ltb_ge _ _)) by apply Nat.le_add_r.
      rewrite Nat.add_comm, Nat.add_sub. reflexivity.
Qed.

Lemma find_block:
  forall l i (LT: (i < length (concat l))%nat),
  exists b, (nth_error l (indexmap' l i) = Some b /\
             length (concat (firstn (indexmap' l i) l)) <= i < length (concat (firstn (indexmap' l i) l)) + length b)%nat.
Proof.
  induction l as [|b l]; intros.
    contradict LT. apply Nat.nlt_0_r.
    destruct (Nat.lt_ge_cases i (length b)).
      exists b. simpl. rewrite (proj2 (Nat.ltb_lt _ _) H). repeat split.
        apply Nat.le_0_l.
        rewrite Nat.add_0_l. assumption.
      destruct (IHl (i - length b)%nat) as [b' [H1 [H2 H3]]].
        eapply Nat.add_lt_mono_l. rewrite le_plus_minus_r, <- app_length by assumption. exact LT.
        exists b'. simpl. rewrite (proj2 (Nat.ltb_ge _ _) H). rewrite <- (Nat.add_sub i (length b)) at 3 4. simpl. rewrite Nat.add_comm, app_length. repeat split.
          apply H1.
          rewrite <- Nat.add_sub_assoc by assumption. apply plus_le_compat_l, H2.
          rewrite <- Nat.add_assoc, <- Nat.add_sub_assoc by assumption. apply plus_lt_compat_l, H3.
Qed.

Lemma indexmap_app1:
  forall l1 l2 i (LT: (i < length (concat l1))%nat),
  indexmap' (l1++l2) i = indexmap' l1 i.
Proof.
  induction l1; intros.
    contradict LT. apply Nat.nlt_0_r.
    simpl. destruct (i <? _)%nat eqn:H.
      reflexivity.
      apply f_equal, IHl1. apply <- Nat.add_lt_mono_r. rewrite Nat.sub_add.
        rewrite Nat.add_comm, <- app_length. exact LT.
        apply Nat.ltb_ge, H.
Qed.

Lemma indexmap_app2:
  forall l1 l2 i (LE: (length (concat l1) <= i)%nat),
  (indexmap' (l1++l2) i = length l1 + indexmap' l2 (i - length (concat l1)))%nat.
Proof.
  induction l1; intros.
    rewrite Nat.sub_0_r. reflexivity.
    simpl (indexmap' (_++_) _). simpl length. rewrite (proj2 (Nat.ltb_ge _ _)).
      rewrite IHl1, Nat.add_succ_l, app_length, Nat.sub_add_distr.
        reflexivity.
        apply Nat.le_add_le_sub_l. rewrite <- app_length. exact LE.
      etransitivity. apply Nat.le_add_r. rewrite <- app_length. exact LE.
Qed.

Lemma indexmap_same:
  forall b n l i1 i2
         (BLK: nth_error l n = Some b)
         (LE1: (length (concat (firstn n l)) <= i1)%nat)
         (LE2: (i1 <= i2)%nat)
         (LE3: (i2 < length (concat (firstn n l)) + length b)%nat),
  indexmap' l i1 = indexmap' l i2.
Proof.
  intros.
  rewrite <- (Nat.sub_add (length (concat (firstn n l))) i1) by exact LE1.
  rewrite <- (Nat.sub_add (length (concat (firstn n l))) i2) by (etransitivity; eassumption).
  rewrite 2!(Nat.add_comm (_-_)).
  rewrite 2!indexmap_sum by (apply nth_error_Some; rewrite BLK; discriminate).
  rewrite nth_skipn in BLK. destruct (skipn n l).
    discriminate.
    inversion BLK. subst l0. simpl. rewrite 2!(proj2 (Nat.ltb_lt _ _)).
      reflexivity.
      eapply plus_lt_reg_l. rewrite le_plus_minus_r. exact LE3. etransitivity; eassumption.
      eapply plus_lt_reg_l. rewrite le_plus_minus_r. eapply Nat.le_lt_trans; eassumption. exact LE1.
Qed.

Lemma indexmap_next:
  forall l n b1 b2 (BLK1: nth_error l n = Some b1) (BLK2: nth_error l (S n) = Some b2)
                   (NN1: b1 <> nil) (NN2: b2 <> nil),
  (indexmap' l (length (concat (firstn (S n) l))) = indexmap' l (length (concat (firstn n l))) + 1)%nat.
Proof.
  intros.
  rewrite <- (firstn_skipn n l), 2!firstn_app, 2!firstn_firstn.
  rewrite Nat.min_r, Nat.min_id by apply Nat.le_succ_diag_r.
  rewrite firstn_length_le by (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK1; discriminate).
  rewrite Nat.sub_succ_l, Nat.sub_diag, app_nil_r, concat_app, app_length by reflexivity.
  rewrite indexmap_app2, (Nat.add_comm _ (length _)), Nat.add_sub by apply Nat.le_add_r.
  rewrite indexmap_app2, Nat.sub_diag by reflexivity.
  rewrite nth_skipn in BLK1. rewrite nth_skipn, skipn_S in BLK2.
  destruct (skipn n l). discriminate. inversion BLK1.
  destruct l1. discriminate. inversion BLK2. subst.
  simpl. rewrite app_nil_r, Nat.sub_diag, Nat.ltb_irrefl.
  destruct b1. contradict NN1. reflexivity.
  destruct b2. contradict NN2. reflexivity.
  rewrite (proj2 (Nat.ltb_lt _ _)), (proj2 (Nat.ltb_lt _ _)) by apply Nat.lt_0_succ.
  rewrite Nat.add_0_r. reflexivity.
Qed.

(*
Theorem nth_addrmap:
  forall l a' (LT: (a' < length (concat l))%nat),
    let a := addrmap' l a' in
    exists b, nth_error l a = Some b /\
              concat l = concat (firstn a l) ++ b ++ concat (skipn (S a) l) /\
              (length (concat (firstn a l)) <= a' < length (concat (firstn a l)) + length b)%nat.
Proof.
  intros.
  apply N.compare_lt_iff in LT. rewrite N2Nat.inj_compare, Nat2N.id in LT.
  apply nat_compare_lt, find_block in LT. destruct LT as [n [b [H1 [H2 H3]]]].
  exists b. repeat split.
    subst a. rewrite <- H1. apply f_equal.

  induction l' as [|b l']; intros.
    destruct a'; inversion LT.
    simpl in a. destruct (a' <? _) eqn:TST; subst a.
      exists b. repeat split.
        apply Nat.le_0_l.
        simpl. apply Nat.ltb_lt. rewrite <- TST, Nat.ltb_compare, <- (Nat2N.id (length b)),
          Nat2N.inj_compare, 2!N2Nat.id, N.ltb_compare. reflexivity.
      destruct (IHl' (a' - N.of_nat (length b))) as [b' [H1 [H2 [H3 H4]]]].
        eapply N.add_lt_mono_r. rewrite N.sub_add.
          rewrite N.add_comm, <- Nat2N.inj_add, <- app_length. apply LT.
          apply N.ltb_ge, TST.
        exists b'. rewrite N2Nat.inj_succ. apply N.ltb_ge, N.leb_le in TST. split.
          apply H1.
          split. simpl. rewrite H2, app_assoc. reflexivity.
          simpl. rewrite app_length, <- Nat.add_assoc. split.
            etransitivity.
              apply plus_le_compat_l, H3.
              rewrite N2Nat.inj_sub, Nat2N.id, le_plus_minus_r.
                reflexivity.
                apply Nat.leb_le. rewrite <- TST, Nat.leb_compare, N.leb_compare, N2Nat.inj_compare, Nat2N.id. reflexivity.
            eapply Nat.le_lt_trans; [|apply plus_lt_compat_l, H4].
              rewrite N2Nat.inj_sub, Nat2N.id, le_plus_minus_r.
                reflexivity.
                apply Nat.leb_le. rewrite <- TST, Nat.leb_compare, N.leb_compare, N2Nat.inj_compare, Nat2N.id. reflexivity.
Qed.
*)

Lemma nth_error_last:
  forall A (l:list A), hd_error (rev l) = nth_error l (pred (length l)).
Proof.
  intros. rewrite <- rev_length. rewrite <- (rev_involutive l) at 2.
  generalize (rev l). clear l. intro l. destruct l.
    reflexivity.
    simpl. rewrite nth_error_app2.
      rewrite rev_length, Nat.sub_diag. reflexivity.
      rewrite rev_length. reflexivity.
Qed.

Theorem firstn_last:
  forall A (l:list A) n,
  firstn (S n) l = firstn n l ++ match nth_error l n with None => nil | Some x => x::nil end.
Proof.
  induction l; intros.
    destruct n; reflexivity.
    simpl. destruct n.
      reflexivity.
      rewrite IHl. reflexivity.
Qed.

(*
Theorem addrmap'_succ:
  forall b n l' a
         (BLK: nth_error l' (N.to_nat (addrmap' l' a)) = Some b)
         (IE: nth_error (concat l') (N.to_nat a) = Some n)
         (NL: hd_error (rev b) <> Some n),
  addrmap' l' a = addrmap' l' (a+1).
Proof.
  induction l'; intros.
    discriminate.
    simpl. destruct (_+1 <? _) eqn:LT1.
      rewrite (proj2 (N.ltb_lt a0 _)). reflexivity. etransitivity.
        apply N.lt_succ_diag_r.
        rewrite <- N.add_1_r. apply N.ltb_lt, LT1.
      simpl in BLK. destruct (a0 <? _) eqn:LT0.
        contradict NL. inversion BLK. subst a. rewrite <- IE. simpl. rewrite nth_error_app1.
          replace a0 with (N.of_nat (pred (length b))).
            rewrite Nat2N.id. apply nth_error_last.
            rewrite Nat2N.inj_pred. apply N.le_antisymm.
              apply N.le_pred_le_succ, N.ltb_ge. rewrite <- N.add_1_r. exact LT1.
              apply N.lt_le_pred, N.ltb_lt, LT0.
          apply nat_compare_lt. rewrite <- (Nat2N.id (length b)), <- N2Nat.inj_compare. apply N.compare_lt_iff, N.ltb_lt, LT0.
        rewrite N.add_sub_swap by apply N.ltb_ge, LT0. apply f_equal, IHl'.
          rewrite N2Nat.inj_succ in BLK. exact BLK.
          rewrite N2Nat.inj_sub, Nat2N.id, <- nth_error_app2. exact IE.
          apply nat_compare_le. rewrite <- (Nat2N.id (length a)), <- N2Nat.inj_compare. apply N.compare_le_iff, N.ltb_ge, LT0.
          exact NL.
Qed.
*)

Lemma newinstrs_length:
  forall l2 l1 l', newinstrs l1 l2 = Some l' -> length l' = length l2.
Proof.
  induction l2; intros.
    inversion H. reflexivity.
    simpl in H. destruct (newinstr l1 a l2).
      specialize (IHl2 (a::l1)). destruct (newinstrs (a::l1) l2).
        inversion H. simpl. rewrite IHl2; reflexivity.
        discriminate.
      discriminate.
Qed.

Lemma newcode_nonnil:
  forall ids l l' i b (NC: newcode ids l = Some l')
         (LT: nth_error l' i = Some b),
  b <> nil.
Proof.
  unfold newcode. intros. intro H. subst b.
  destruct (_ <? _); [|discriminate].
  rewrite (nth_newinstrs _ _ _ i NC) in LT.
  destruct (nth_error _ _); [|discriminate].
  destruct (newinstr _ _ _) eqn:NI; [|discriminate].
  eapply newinstr_nonnil. rewrite NI. apply f_equal.
  inversion LT. rewrite H0. apply app_eq_nil in H0. apply H0.
Qed.

Lemma shrink_length:
  forall l2 l1, length (shrink l1 l2) = (length l1 + length l2)%nat.
Proof.
  induction l2; intros.
    rewrite Nat.add_0_r. apply rev_length.
    destruct a. simpl. rewrite IHl2, Nat.add_succ_r. reflexivity.
Qed.

Lemma newcode_length:
  forall ids l l', newcode ids l = Some l' -> length l' = min (length ids) (length l).
Proof.
  unfold newcode. intros.
  destruct (_ <? _); [|discriminate].
  apply newinstrs_length in H.
  rewrite H, shrink_length, map_length.
  apply combine_length.
Qed.

Definition dateq dp :=
  match dp with (Data iid1 oid1 sd1 n1 _, Data iid2 oid2 sd2 n2 _) =>
    Data iid1 oid1 sd1 n1 true = Data iid2 oid2 sd2 n2 true
  end.

Theorem combine_app:
  forall {A} (l1 l2 l3 l4:list A) (LEN: length l1 = length l3),
  combine (l1++l2) (l3++l4) = (combine l1 l3) ++ (combine l2 l4).
Proof.
  induction l1; intros.
    destruct l3. reflexivity. discriminate.
    destruct l3.
      discriminate.
      simpl. rewrite IHl1.
        reflexivity.
        inversion LEN. reflexivity.
Qed.

Theorem combine_nth_error:
  forall {A} (x y:A) (l1 l2:list A) n
         (NTH1: nth_error l1 n = Some x) (NTH2: nth_error l2 n = Some y),
  In (x,y) (combine l1 l2).
Proof.
  induction l1; intros.
    destruct n; discriminate.
    destruct l2.
      destruct n; discriminate.
      destruct n.
        inversion NTH1. inversion NTH2. apply in_eq.
        right. eapply IHl1. apply NTH1. apply NTH2.
Qed.

Theorem rev_combine:
  forall {A} (l1 l2:list A) (LEN: length l1 = length l2),
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  induction l1; intros.
    reflexivity.
    destruct l2.
      destruct (rev (_::_)); reflexivity.
      simpl. inversion LEN. rewrite IHl1, combine_app by (rewrite ?rev_length; assumption). reflexivity.
Qed.

Lemma nth_error_map:
  forall {A B} (f:A->B) (l:list A) n,
  nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  induction l; intros; destruct n; try reflexivity. apply IHl.
Qed.

Lemma nth_error_combine:
  forall {A B} (l1:list A) (l2:list B) n,
  nth_error (combine l1 l2) n = match nth_error l1 n, nth_error l2 n with
                                | Some x, Some y => Some (x,y)
                                | _, _ => None
                                end.
Proof.
  induction l1; intros.
    destruct n; reflexivity.
    destruct l2.
      destruct n. reflexivity. simpl. destruct nth_error; reflexivity.
      destruct n.
        reflexivity.
        simpl. apply IHl1.
Qed.

Theorem shrink_preserves:
  forall l2 l1 l1' (LEN: length l1' = length l1)
         (FA: Forall dateq (combine l1' l1)),
  Forall dateq (combine (rev l1' ++ l2) (shrink l1 l2)).
Proof.
  induction l2; intros.

    rewrite app_nil_r. simpl. rewrite <- rev_combine by exact LEN.
    apply Forall_forall. intros dp IN. eapply Forall_forall. exact FA. apply in_rev. exact IN.

    rewrite <- (rev_involutive (a::l2)) at 1. rewrite <- rev_app_distr. simpl (rev (a::l2)).
    rewrite <- app_assoc. change ((a::nil)++l1') with (a::l1'). rewrite rev_app_distr, rev_involutive.
    destruct a. simpl (shrink _ _). apply IHl2.
      simpl. rewrite LEN. reflexivity.
      apply Forall_cons. reflexivity. exact FA.
Qed.

Theorem strong_induction:
  forall (P:nat->Prop) (IC: forall n1 (IH: forall n0 (DEC: (n0<n1)%nat), P n0), P n1),
  forall n, P n.
Proof.
  refine (well_founded_ind _).
  intro y. induction y; apply Acc_intro; intros x DEC; inversion DEC.
    subst x. assumption.
    apply (Acc_inv IHy). assumption.
Qed.

Lemma squeeze:
  forall n m (LO: (m <= n)%nat) (HI: (n < m+1)%nat),
  n = m.
Proof.
  intros. apply Nat.le_antisymm.
    apply lt_n_Sm_le. rewrite <- Nat.add_1_r. exact HI.
    exact LO.
Qed.

Lemma xbits_lor:
  forall m n i j, xbits (m .| n) i j = xbits m i j .| xbits n i j.
Proof.
  intros. unfold xbits.
  rewrite <- N.land_lor_distr_l, <- N.shiftr_lor.
  reflexivity.
Qed.

Lemma xbits_land:
  forall m n i j, xbits (m .& n) i j = xbits m i j .& xbits n i j.
Proof.
  intros. unfold xbits.
  rewrite <- N.land_assoc, (N.land_comm (N.ones _)), <- (N.land_assoc (n>>i)), N.land_diag, N.land_assoc, <- N.shiftr_land.
  reflexivity.
Qed.

Lemma xbits_shiftl:
  forall n k i j, xbits (n << k) i j = xbits n (i-k) (j-k) << (k-i).
Proof.
  intros. unfold xbits. destruct (N.le_ge_cases k i).
    rewrite N.shiftr_shiftl_r, <- N.sub_add_distr, N.add_sub_assoc, N.add_comm, N.add_sub,
            (proj2 (N.sub_0_le k i) H), N.shiftl_0_r by assumption. reflexivity.

    rewrite (proj2 (N.sub_0_le i k) H), N.shiftr_0_r, N.sub_0_r, N.shiftr_shiftl_l by assumption.
    destruct (N.le_ge_cases k j).

      etransitivity; [|apply N.lor_0_r].
      erewrite N.shiftl_land, <- (N.mod_mul _ (2^_)) by (apply N.pow_nonzero; discriminate).
      rewrite <- N.land_ones, <- N.shiftl_mul_pow2, <- N.land_lor_distr_r.
      rewrite <- N.lxor_lor, <- N.add_nocarry_lxor by
        (rewrite N.land_ones, N.shiftl_mul_pow2; apply N.mod_mul, N.pow_nonzero; discriminate).
      rewrite (N.shiftl_mul_pow2 (N.ones _)), N.mul_comm, <- N.ones_add, N.add_comm.
      rewrite N.add_sub_assoc, N.sub_add by assumption. reflexivity.

      rewrite (proj2 (N.sub_0_le j k) H0), N.land_0_r, N.shiftl_0_l. destruct (N.le_ge_cases i j).
        rewrite N.shiftl_mul_pow2, N.land_ones, <- (N.sub_add j k), <- N.add_sub_assoc, N.pow_add_r,
                N.mul_assoc by assumption. apply N.mod_mul, N.pow_nonzero. discriminate.
        rewrite (proj2 (N.sub_0_le j i)) by assumption. apply N.land_0_r.
Qed.

Lemma xbits_shiftr:
  forall n k i j, xbits (n >> k) i j = xbits n (i+k) (j+k).
Proof.
  intros. unfold xbits.
  rewrite N.shiftr_shiftr, (N.add_comm i k), N.sub_add_distr, N.add_sub.
  reflexivity.
Qed.

Lemma shiftr_land_shiftl:
  forall a b c d, b <= d -> (a>>b) .& c << d = a .& (c << b) << (d-b).
Proof.
  intros.
  rewrite <- (N.lor_ldiff_and (a .& (c<<b)) (N.ones b)), <- N.land_assoc, N.land_ones.
  rewrite (N.shiftl_mul_pow2 c b) at 2.
  rewrite N.mod_mul by (apply N.pow_nonzero; discriminate).
  rewrite N.land_0_r, N.lor_0_r, N.ldiff_ones_r, N.shiftl_shiftl, N.add_comm, N.sub_add by assumption.
  rewrite (N.shiftr_land a), N.shiftr_shiftl_l, N.sub_diag, N.shiftl_0_r; reflexivity.
Qed.

Lemma reencode_branch:
  forall o, let n := encode_branch_offset o in
  (xbits n 8 12 << 1) .| ((xbits n 25 31 << 5) .| ((xbits n 7 8 << 11) .| (xbits n 31 32 << 12))) = (o .& N.ones 11) << 2.
Proof.
  intros. subst n. unfold encode_branch_offset.
  rewrite !xbits_lor, !xbits_shiftl, !xbits_shiftr, !xbits_land.
  rewrite !N.land_0_r, !N.lor_0_r, !N.lor_0_l, !N.shiftl_0_r, N.shiftl_shiftl.
  unfold xbits. rewrite <- !N.land_assoc, !N.land_diag.
  rewrite !shiftr_land_shiftl by discriminate.
  rewrite <- !N.shiftl_lor, <- !N.land_lor_distr_r.
  reflexivity.
Qed.

Lemma exec_stmt_r5branch:
  forall h s e a off s' x
         (XS: exec_stmt h s (r5branch e a off) s' (Some x)),
  x = Exit ((Z.to_N (Z.of_N a + off)) mod 2^32).
Proof.
  unfold r5branch. intros. inversion XS; subst. destruct c.
    inversion XS0.
    inversion XS0; inversion E0; subst. reflexivity.
Qed.

Lemma exec_branch_taken:
  forall h s a n r1 r2 o' s' a'
         (XS: exec_stmt h s (rv2il a (rv_decode_branch n r1 r2 o')) s' (Some (Exit a'))),
  a' = Z.to_N (Z.of_N a + o') mod 2^32.
Proof.
  unfold rv_decode_branch. intros.
  destruct (xbits n 12 15 .| (n .& 256)); [|repeat (destruct p; try solve [ inversion XS ])];
  inversion XS; destruct c; inversion XS0; inversion E0; reflexivity.
Qed.


(* Here's the main theorem to prove: *)
Theorem rewriter_safety: forall pol, safety pol (newcode pol) (indexmap pol).
Proof.
  unfold safety. intros. revert XP0. pattern n. apply strong_induction. intros.
  clear n. rename n1 into n.

  (* Simplify addrmap to addrmap'. *)
  unfold indexmap. rewrite NC.

  (* Infer that current code equals statically rewritten code. *)
  unfold rv_prog in LU.
  destruct (s V_MEM32) as [|m mw]. discriminate. specialize (NWC m mw i (eq_refl _)).
  destruct (s A_EXEC) as [|e ew]. discriminate. specialize (NXD e ew i (eq_refl _)).
  destruct (e (4 * N.of_nat i)). discriminate.
  replace q with (rv_stmt m (4 * N.of_nat i)) in XS by (inversion LU; reflexivity). clear q LU.
  destruct (Nat.le_gt_cases (length (concat l')) i) as [LE|LT].
    apply NXD in LE. discriminate.
  unfold rv_stmt in XS. rewrite NWC in XS by exact LT. clear m mw e ew p NWC NXD.

  (* Derive the metadata (before and after shrink-optimization) used in rewriting. *)
  apply find_block in LT. unfold policytarget. set (j:=indexmap' l' i) in *.
  destruct LT as [b0 [BLK BND]].
  unfold newcode in NC. destruct (sumsizes _ <? _) eqn:SIZ; [|discriminate]. apply N.ltb_lt in SIZ.
  assert (NIS:=nth_newinstrs _ _ _ j NC). rewrite BLK in NIS.
  destruct (nth_error (shrink _ _) _) as [d'|] eqn:DAT'; [|discriminate].
  destruct (newinstr _ d' _) as [b|] eqn:NI; [|discriminate].
  inversion NIS. clear NIS. subst b0.
  destruct (nth_error (map todata (combine pol l)) j) as [d|] eqn:DAT;
  [| contradict DAT; apply nth_error_Some;
     rewrite <- (Nat.add_0_l (length _)); change O with (length (@nil instr_data));
     rewrite <- shrink_length; apply nth_error_Some; rewrite DAT'; discriminate ].
  assert (DEQ: dateq (d,d')). eapply (Forall_forall dateq).
    eapply (shrink_preserves _ nil). reflexivity. apply Forall_nil.
    eapply combine_nth_error.
      simpl. exact DAT.
      exact DAT'.
  destruct d as [iid oid sd1 ie sb1]. destruct d' as [iid' oid' sd' ie' sb].
  inversion DEQ. subst iid' oid' sd' ie'. clear DEQ.
  rewrite nth_error_map, nth_error_combine in DAT.
  destruct (nth_error pol j) as [(iid0,(oid0,sd0))|]; [|discriminate].
  destruct (nth_error l j); [|discriminate].
  inversion DAT; subst. clear DAT.

  (* Obtain the encoding of the rewritten instruction being executed. *)
  destruct (nth_error (concat l') i) as [ie'|] eqn:IE';
  [| contradict IE'; rewrite <- (firstn_skipn j l'); eapply nth_error_Some, Nat.lt_le_trans;
     [ apply BND
     | remember (newtag _ ++ b); rewrite nth_skipn in BLK; destruct (skipn j l');
       [ discriminate
       | inversion BLK; rewrite concat_app, app_length; simpl; rewrite app_length, Nat.add_assoc; apply le_plus_l ]]].
  rewrite (CS i ie' IE') in XS.

  (* If the rewritten code is a tag instruction, it's safe because it falls thru to the same block. *)
  rewrite <- (firstn_skipn j l'), concat_app, nth_error_app2 in IE' by apply BND.
  assert (BLK':=BLK). rewrite nth_skipn in BLK'.
  destruct (Nat.lt_ge_cases i (length (concat (firstn j l')) + length (newtag (Data iid oid sd1 ie sb)))) as [TAG|TAG].
  destruct iid as [iid|]; [|contradict TAG; rewrite Nat.add_0_r; apply le_not_lt, BND].
  rewrite Nat.add_1_r in TAG. rewrite (proj2 (Nat.sub_0_le i _)) in IE' by apply lt_n_Sm_le, TAG.
  destruct (skipn j l'). discriminate. inversion BLK'. subst.
  inversion IE'. subst.
  unfold rv_decode in XS. rewrite N.land_lor_distr_l, 2!N.land_ones, N.shiftl_mul_pow2 in XS.
  change (2^12) with (2^5*2^7) in XS at 1.
  rewrite N.mul_assoc, N.mod_mul, N.lor_0_l in XS by discriminate.
  change (55 mod _) with 55 in XS. unfold rv_decode_op in XS.
  replace (xbits (_ .| 55) 7 12) with 0 in XS by
  ( unfold xbits;
    rewrite N.land_ones, N.shiftr_lor, N.lor_0_r, N.shiftr_div_pow2;
    change (2^12) with (2^5*2^7);
    rewrite N.mul_assoc, N.div_mul, N.mod_mul by discriminate;
    reflexivity ).
  simpl in XS. inversion XS; clear XS; subst.
  replace i' with (i+1)%nat in * by (apply Nat2N.inj, (N.mul_cancel_l _ _ 4);
  [ discriminate
  | rewrite Nat2N.inj_add, N.mul_add_distr_l; inversion EX; assumption ]).
  left. eapply indexmap_same.
    exact BLK.
    apply BND.
    apply Nat.le_add_r.
    rewrite app_length, Nat.add_assoc. apply Nat.add_lt_le_mono.
      rewrite Nat.add_1_r. exact TAG.
      destruct b. contradict NI. apply newinstr_nonnil. apply le_n_S, Nat.le_0_l.

  (* Otherwise the current instruction is in the non-tag portion of the block. *)
  destruct (skipn j l'). discriminate. remember (newtag _) as t. inversion BLK'. clear Heqt BLK'. subst l0.
  simpl in IE'. rewrite nth_error_app1 in IE' by (eapply plus_lt_reg_l; rewrite le_plus_minus_r; apply BND).
  clear l1. rewrite nth_error_app2 in IE' by (eapply plus_le_reg_l; rewrite le_plus_minus_r by apply BND; exact TAG).

  (* If the original code was a tag, the rewritten code falls thru to next block. *)
  unfold newinstr in NI. destruct (ie .& 4095 =? 55) eqn:OP1. right. clear IH.
  destruct (mem 1 sd1) as [IN1|IN1]; [|discriminate].
  inversion NI. clear NI. subst b.
  rewrite app_length, Nat.add_assoc in BND.
  assert (IDX := squeeze i _ TAG (proj2 BND)).
  rewrite IDX in IE' at 1. rewrite <- Nat.sub_add_distr, Nat.sub_diag in IE'.
  inversion IE'. clear IE'. subst ie'.
  inversion XS. clear XS. subst s' x.
  replace i' with (i+1)%nat in * by (apply Nat2N.inj, (N.mul_cancel_l _ _ 4);
  [ discriminate
  | rewrite Nat2N.inj_add, N.mul_add_distr_l; inversion EX; assumption ]).
  split.

    change 1%nat with (length (16435%N::nil)).
    exists (j + 1)%nat.
    rewrite <- (firstn_skipn j l'), IDX, <- Nat.add_assoc, <- 2!app_length.
    rewrite firstn_app, firstn_firstn, Min.min_r by apply le_plus_l.
    rewrite firstn_length, Min.min_l, minus_plus by
      (apply Nat.lt_le_incl, nth_error_Some; rewrite BLK; discriminate).
    rewrite nth_skipn in BLK. destruct (skipn j l'). discriminate. inversion BLK. subst l0.
    rewrite concat_app. simpl. rewrite app_nil_r. reflexivity.

    left. rewrite minus_plus. exact IN1.

  (* If the original code was a branch... *)
  destruct (ie .& 127 =? 99) eqn:OP2.
  destruct (mem 1 sd1) as [IN1|IN1]; [|discriminate].
  destruct (mem _ sd1) as [IN'|IN']; [|discriminate].
  rewrite app_nil_r in NI.
  apply Neqb_ok in OP2.
  destruct sb.

    (* If the branch was preserved by rewriting... *)
    unfold newbranch in NI. set (o' := newoffset _ _ _ _ _ _) in NI.
    destruct (_ && _)%bool eqn:O'BND; [|discriminate].
    inversion NI. clear NI. subst b.
    rewrite app_length, Nat.add_assoc in BND. simpl in BND.
    rewrite (squeeze _ _ TAG (proj2 BND)) in *.
    rewrite <- Nat.sub_add_distr, Nat.sub_diag in IE'.
    right. destruct x as [x|].

      (* If the branch jumps, it's safe because the target was statically checked. *)
      inversion IE'. clear BLK IE'. subst ie'.
      destruct x as [a'|]; [|discriminate].
      unfold rv_decode in XS.
      rewrite N.land_lor_distr_l, <- N.land_assoc in XS.
      change (33550463 .& N.ones 7) with 127 in XS. change (N.ones 7) with (33550463 .& 127) in XS.
      rewrite N.land_assoc, ebo_bitmask, N.lor_0_r, OP2 in XS.
      unfold rv_decode_op in XS.
      rewrite !xbits_lor, !xbits_land, !N.land_0_r, !N.lor_0_l, reencode_branch, N.land_ones in XS.
      change 2048%Z with (2^11)%Z in XS.
      apply exec_branch_taken in XS.
      rewrite (N.mod_small _ (2^11)) in XS by (
        change (2^11) with (Z.to_N (2^11)); apply Z2N.inj_lt; try first
        [ discriminate | apply Z.mod_pos_bound; reflexivity ]).
      admit.

      (* If it falls thru, it's safe because fall-thrus are statically checked. *)
      change 4 with (4*N.of_nat 1) in EX at 2.
      rewrite <- N.mul_add_distr_l, <- Nat2N.inj_add, !(N.mul_comm 4) in EX.
      inversion EX; subst. apply Nmult_reg_r, Nat2N.inj in H0; [|discriminate].
      rewrite <- H0 in *. clear i' H0 EX.
      split.

        exists (S j).
        rewrite firstn_last, BLK, concat_app, concat_cons, 3!app_length.
        rewrite <- (plus_assoc (length t)), plus_assoc.
        reflexivity.

        left. rewrite minus_plus. exact IN1.

    (* If the branch was rewritten to a long-encoded jump... *)
    admit.

  (* TODO: Indirect jumps and security-irrelevant instructions *)
  admit.
Qed.
