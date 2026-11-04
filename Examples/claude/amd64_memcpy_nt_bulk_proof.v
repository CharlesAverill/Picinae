(* SSE2 NT bulk-loop extension, GPT-6.1 Sol, November 2026.
   Same inherited glibc/lifter provenance and projection boundaries as
   amd64_memcpy_nt_head_proof. This file concerns the unchanged actual
   64-iteration two/four-page loops, not the AVX 32-iteration body. *)
Require Import Picinae_amd64 memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memcpy_proof
  amd64_memcpy_loops_proof amd64_memcpy_nt_proof.
Import ListNotations.
Open Scope N.

Definition nt_pages (four:bool):N := if four then 4 else 2.
Definition nt_chunk four := 4096 * nt_pages four.
Definition nt_count four d n := (n-nt_align d) / nt_chunk four.
Definition nt_rest four d n := (n-nt_align d) mod nt_chunk four.
Definition nt_offset four d j i := nt_align d + nt_chunk four*j + 64*i.

Definition nt_saved_page (L M:memory) d s o :=
  M [Ⓧ d+o := L Ⓧ[s+o]]
    [Ⓧ 16+d+o := L Ⓧ[16+s+o]]
    [Ⓧ 32+d+o := L Ⓧ[32+s+o]]
    [Ⓧ 48+d+o := L Ⓧ[48+s+o]].

Lemma nt_saved_page_staged: forall m L M d s n pages a j i q,
  1<=a<=64 -> i<64 -> q<pages -> a+4096*pages*(j+1)<=n ->
  nov d s n -> n<2^64 ->
  cpy m L d s (nt_done pages a j i) ->
  cpy m M d s (nt_staged pages a j i q) ->
  cpy m (nt_saved_page L M d s (a+4096*pages*j+4096*q+64*i)) d s
    (nt_staged pages a j i (q+1)).
Proof.
  intros m L M d s n pages a j i q A I Q B NOV NB C0 C.
  assert (P: 0<pages) by (clear - Q; lia).
  assert (W0: forall x, nt_done pages a j i x -> x<n).
  { intros x H. eapply nt_staged_bound with (q:=0);
    [exact A|exact I|exact P|lia|exact B|]. apply nt_staged_zero. exact H. }
  assert (W: forall x, nt_staged pages a j i q x -> x<n).
  { intros x H. eapply nt_staged_bound;
    [exact A|exact I|exact P|apply N.lt_le_incl; exact Q|exact B|exact H]. }
  set (o:=a+4096*pages*j+4096*q+64*i).
  assert (OB: o+64<=n) by (unfold o; clear - I Q B; nia).
  assert (E: nt_saved_page L M d s o=nt_row M d s o).
  { unfold nt_saved_page, nt_row.
    replace (16+d+o) with (d+o+16) by (clear; lia).
    replace (32+d+o) with (d+o+32) by (clear; lia).
    replace (48+d+o) with (d+o+48) by (clear; lia).
    replace (16+s+o) with (s+o+16) by (clear; lia).
    replace (32+s+o) with (s+o+32) by (clear; lia).
    replace (48+s+o) with (s+o+48) by (clear; lia).
    rewrite (cpy_load m L d s (nt_done pages a j i) n (o+0) 16 (s+o) C0 W0 NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m M d s (nt_staged pages a j i q) n (o+0) 16 (s+o) C W NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m L d s (nt_done pages a j i) n (o+16) 16 (s+o+16) C0 W0 NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m M d s (nt_staged pages a j i q) n (o+16) 16 (s+o+16) C W NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m L d s (nt_done pages a j i) n (o+32) 16 (s+o+32) C0 W0 NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m M d s (nt_staged pages a j i q) n (o+32) 16 (s+o+32) C W NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m L d s (nt_done pages a j i) n (o+48) 16 (s+o+48) C0 W0 NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    rewrite (cpy_load m M d s (nt_staged pages a j i q) n (o+48) 16 (s+o+48) C W NOV)
      by (first [clear - OB; lia|f_equal; clear; lia]).
    reflexivity. }
  rewrite E. apply (nt_staged_advance m M d s n pages a j i q);
    assumption.
Qed.

Definition nt_image2 (M:memory) d s o :=
  M
    [Ⓧ d+o := M Ⓧ[s+o]]
    [Ⓧ 16+d+o := M Ⓧ[16+s+o]]
    [Ⓧ 32+d+o := M Ⓧ[32+s+o]]
    [Ⓧ 48+d+o := M Ⓧ[48+s+o]]
    [Ⓧ 4096+d+o := M Ⓧ[4096+s+o]]
    [Ⓧ 4112+d+o := M Ⓧ[4112+s+o]]
    [Ⓧ 4128+d+o := M Ⓧ[4128+s+o]]
    [Ⓧ 4144+d+o := M Ⓧ[4144+s+o]].

Lemma nt_image2_advance: forall m M d s n a j i,
  1<=a<=64 -> i<64 -> a+4096*2*(j+1)<=n ->
  nov d s n -> n<2^64 ->
  cpy m M d s (nt_done 2 a j i) ->
  cpy m (nt_image2 M d s (a+4096*2*j+64*i)) d s
    (nt_done 2 a j (i+1)).
Proof.
  intros m M d s n a j i A I B NOV NB C.
  assert (C0: cpy m M d s (nt_staged 2 a j i 0)).
  { eapply cpy_equiv; [|exact C]. intro x. symmetry. apply nt_staged_zero. }
  pose proof (nt_saved_page_staged m M _ d s n 2 a j i 0
    A I ltac:(lia) B NOV NB C C0) as C1.
  pose proof (nt_saved_page_staged m M _ d s n 2 a j i 1
    A I ltac:(lia) B NOV NB C C1) as C2.
  replace (nt_image2 M d s (a+4096*2*j+64*i)) with
    (nt_saved_page M (nt_saved_page M M d s (a+4096*2*j+4096*0+64*i)) d s (a+4096*2*j+4096*1+64*i)) by
    (unfold nt_image2, nt_saved_page; repeat first [reflexivity |
      lazymatch goal with
      | |- context [setmem] => f_equal
      | |- context [getmem] => f_equal
      | |- _ => clear; lia
      end]).
  eapply cpy_equiv; [|exact C2].
  intro x. apply nt_staged_finish.
Qed.

Definition nt_image4 (M:memory) d s o :=
  M
    [Ⓧ d+o := M Ⓧ[s+o]]
    [Ⓧ 16+d+o := M Ⓧ[16+s+o]]
    [Ⓧ 32+d+o := M Ⓧ[32+s+o]]
    [Ⓧ 48+d+o := M Ⓧ[48+s+o]]
    [Ⓧ 4096+d+o := M Ⓧ[4096+s+o]]
    [Ⓧ 4112+d+o := M Ⓧ[4112+s+o]]
    [Ⓧ 4128+d+o := M Ⓧ[4128+s+o]]
    [Ⓧ 4144+d+o := M Ⓧ[4144+s+o]]
    [Ⓧ 8192+d+o := M Ⓧ[8192+s+o]]
    [Ⓧ 8208+d+o := M Ⓧ[8208+s+o]]
    [Ⓧ 8224+d+o := M Ⓧ[8224+s+o]]
    [Ⓧ 8240+d+o := M Ⓧ[8240+s+o]]
    [Ⓧ 12288+d+o := M Ⓧ[12288+s+o]]
    [Ⓧ 12304+d+o := M Ⓧ[12304+s+o]]
    [Ⓧ 12320+d+o := M Ⓧ[12320+s+o]]
    [Ⓧ 12336+d+o := M Ⓧ[12336+s+o]].

Lemma nt_image4_advance: forall m M d s n a j i,
  1<=a<=64 -> i<64 -> a+4096*4*(j+1)<=n ->
  nov d s n -> n<2^64 ->
  cpy m M d s (nt_done 4 a j i) ->
  cpy m (nt_image4 M d s (a+4096*4*j+64*i)) d s
    (nt_done 4 a j (i+1)).
Proof.
  intros m M d s n a j i A I B NOV NB C.
  assert (C0: cpy m M d s (nt_staged 4 a j i 0)).
  { eapply cpy_equiv; [|exact C]. intro x. symmetry. apply nt_staged_zero. }
  pose proof (nt_saved_page_staged m M _ d s n 4 a j i 0
    A I ltac:(lia) B NOV NB C C0) as C1.
  pose proof (nt_saved_page_staged m M _ d s n 4 a j i 1
    A I ltac:(lia) B NOV NB C C1) as C2.
  pose proof (nt_saved_page_staged m M _ d s n 4 a j i 2
    A I ltac:(lia) B NOV NB C C2) as C3.
  pose proof (nt_saved_page_staged m M _ d s n 4 a j i 3
    A I ltac:(lia) B NOV NB C C3) as C4.
  replace (nt_image4 M d s (a+4096*4*j+64*i)) with
    (nt_saved_page M (nt_saved_page M (nt_saved_page M (nt_saved_page M M d s (a+4096*4*j+4096*0+64*i)) d s (a+4096*4*j+4096*1+64*i)) d s (a+4096*4*j+4096*2+64*i)) d s (a+4096*4*j+4096*3+64*i)) by
    (unfold nt_image4, nt_saved_page; repeat first [reflexivity |
      lazymatch goal with
      | |- context [setmem] => f_equal
      | |- context [getmem] => f_equal
      | |- _ => clear; lia
      end]).
  eapply cpy_equiv; [|exact C4].
  intro x. apply nt_staged_finish.
Qed.

Lemma nt_image2_at: forall M d s a c j i,
  nt_image2 M d s (a+c*j+64*i)=M
    [Ⓧ d+a+c*j+64*i := M Ⓧ[s+a+c*j+64*i]]
    [Ⓧ 16+d+a+c*j+64*i := M Ⓧ[16+s+a+c*j+64*i]]
    [Ⓧ 32+d+a+c*j+64*i := M Ⓧ[32+s+a+c*j+64*i]]
    [Ⓧ 48+d+a+c*j+64*i := M Ⓧ[48+s+a+c*j+64*i]]
    [Ⓧ 4096+d+a+c*j+64*i := M Ⓧ[4096+s+a+c*j+64*i]]
    [Ⓧ 4112+d+a+c*j+64*i := M Ⓧ[4112+s+a+c*j+64*i]]
    [Ⓧ 4128+d+a+c*j+64*i := M Ⓧ[4128+s+a+c*j+64*i]]
    [Ⓧ 4144+d+a+c*j+64*i := M Ⓧ[4144+s+a+c*j+64*i]].
Proof.
  intros. unfold nt_image2.
  repeat first [reflexivity | lazymatch goal with
    | |- context [setmem] => f_equal
    | |- context [getmem] => f_equal
    | |- _ => clear; lia end].
Qed.

Lemma nt_image4_at: forall M d s a c j i,
  nt_image4 M d s (a+c*j+64*i)=M
    [Ⓧ d+a+c*j+64*i := M Ⓧ[s+a+c*j+64*i]]
    [Ⓧ 16+d+a+c*j+64*i := M Ⓧ[16+s+a+c*j+64*i]]
    [Ⓧ 32+d+a+c*j+64*i := M Ⓧ[32+s+a+c*j+64*i]]
    [Ⓧ 48+d+a+c*j+64*i := M Ⓧ[48+s+a+c*j+64*i]]
    [Ⓧ 4096+d+a+c*j+64*i := M Ⓧ[4096+s+a+c*j+64*i]]
    [Ⓧ 4112+d+a+c*j+64*i := M Ⓧ[4112+s+a+c*j+64*i]]
    [Ⓧ 4128+d+a+c*j+64*i := M Ⓧ[4128+s+a+c*j+64*i]]
    [Ⓧ 4144+d+a+c*j+64*i := M Ⓧ[4144+s+a+c*j+64*i]]
    [Ⓧ 8192+d+a+c*j+64*i := M Ⓧ[8192+s+a+c*j+64*i]]
    [Ⓧ 8208+d+a+c*j+64*i := M Ⓧ[8208+s+a+c*j+64*i]]
    [Ⓧ 8224+d+a+c*j+64*i := M Ⓧ[8224+s+a+c*j+64*i]]
    [Ⓧ 8240+d+a+c*j+64*i := M Ⓧ[8240+s+a+c*j+64*i]]
    [Ⓧ 12288+d+a+c*j+64*i := M Ⓧ[12288+s+a+c*j+64*i]]
    [Ⓧ 12304+d+a+c*j+64*i := M Ⓧ[12304+s+a+c*j+64*i]]
    [Ⓧ 12320+d+a+c*j+64*i := M Ⓧ[12320+s+a+c*j+64*i]]
    [Ⓧ 12336+d+a+c*j+64*i := M Ⓧ[12336+s+a+c*j+64*i]].
Proof.
  intros. unfold nt_image4.
  repeat first [reflexivity | lazymatch goal with
    | |- context [setmem] => f_equal
    | |- context [getmem] => f_equal
    | |- _ => clear; lia end].
Qed.

Definition nt_bulk_state four m d s n rsp j i st :=
  j<nt_count four d n /\ i<64 /\
  cpy m (st V_MEM64) d s (nt_done (nt_pages four) (nt_align d) j i) /\
  st R_RDI=d+nt_offset four d j i /\ st R_RSI=s ⊕ nt_offset four d j i /\
  st R_RCX=64-i /\ st R_R10=nt_count four d n-j /\
  st R_RDX=nt_rest four d n /\ st R_RAX=d /\ st R_RSP=rsp.
Definition nt_bulk_post four m d s n rsp st :=
  nt_tail_state m d s n rsp (nt_align d+nt_chunk four*nt_count four d n) st.
Definition nt_bulk_exit (four:bool) (t:trace) :=
  match t with (Addr a,_)::_ => if four then a=?1855083 else a=?1854659
  | _ => false end.
Definition nt_bulk_invs (four:bool) m d s n rsp (t:trace) :=
  match t with (Addr a,st)::_ =>
    if a =? (if four then 1854789 else 1854501) then
      Some (exists j i, nt_bulk_state four m d s n rsp j i st)
    else if a =? (if four then 1855083 else 1854659) then
      Some (nt_bulk_post four m d s n rsp st)
    else None
  | _ => None end.

Lemma nt_count_bounds: forall four d n,
  64<=n -> nt_align d+nt_chunk four*nt_count four d n<=n /\
  n-(nt_align d+nt_chunk four*nt_count four d n)=nt_rest four d n /\
  nt_rest four d n<nt_chunk four.
Proof.
  intros four d n BIG. pose proof (nt_align_bounds d) as A.
  assert (P: nt_chunk four<>0) by (destruct four; discriminate).
  pose proof (N.div_mod (n-nt_align d) (nt_chunk four) P) as E.
  pose proof (N.mod_lt (n-nt_align d) (nt_chunk four) P) as R.
  unfold nt_count, nt_rest. nia.
Qed.

Ltac nt_scalar_projections :=
  lazy beta iota zeta delta [update iseq VarEqDec vareq
    X64Arch.Var.eq_dec MiniX64VarEq.eq_dec x64var_rec x64var_rect].

Lemma nt_bulk_iteration2: forall m d s n rsp st t,
  models archtyps st -> nov d s n -> d+n<2^64 -> n<2^64 -> 64<=n ->
  (exists j i, nt_bulk_state false m d s n rsp j i st) ->
  nextinv memcpy_amd64 (nt_bulk_invs false m d s n rsp) (nt_bulk_exit false) false
    ((Addr 1854501,st)::t).
Proof.
  intros m d s n rsp st t MDL NOV NW NB BIG PRE.
  destruct PRE as [j [i [J [I [C [D [S [CX [R10 [DX [AX SP]]]]]]]]]]].
  pose proof (nt_align_bounds d) as A.
  destruct (nt_count_bounds false d n BIG) as [CK [REST RB]].
  assert (B: nt_align d+4096*2*(j+1)<=n)
    by (change (nt_chunk false) with 8192 in CK; clear - CK J; nia).
  pose proof (nt_image2_advance m (st V_MEM64) d s n (nt_align d) j i A I B NOV NB C) as ADV.
  change (4096*2) with (2^13) in ADV.
  rewrite (nt_image2_at (st V_MEM64) d s (nt_align d) (2^13) j i) in ADV.
  unfold nt_offset, nt_chunk, nt_pages in D, S, CK, REST, RB.
  repeat x64_step.
  all: rewrite ?pack16; pack_xmm.
  all: change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  all: lazymatch type of ADV with cpy _ ?MP _ _ _ =>
    set (Mpost:=MP) in *; clearbody Mpost end.
  all: change (2^12) with 4096 in *; change (2^13) with 8192 in *; change (2^6) with 64 in *.
  all: change (nt_chunk false) with 8192 in *.
  - apply N.eqb_eq in BC. apply N.eqb_eq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count false d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    assert (JE: j+1=nt_count false d n) by (clear - BC0 J; lia).
    unfold nt_bulk_post, nt_tail_state.
    split; [clear - CK; lia|]. split; [clear - RB REST; lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. rewrite nt_done_chunk by reflexivity.
      rewrite JE. clear - A JE. intuition nia.
    + split.
      *         rewrite N.mod_small by (clear - NW B I; nia).
        clear - IE JE; nia.
      * split.
        --            f_equal. clear - IE JE; nia.
        -- split; [rewrite DX; clear - REST; lia|]. split; assumption.
  - apply N.eqb_eq in BC. apply N.eqb_neq in BC0.
    assert (IE: i=63) by (clear - I BC; lia).
    assert (CB: nt_count false d n<2^64) by (clear - CK NB; nia).
    rewrite N.mod_small in BC0 by (clear - J CB; lia).
    exists (j+1), 0. unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [clear - J BC0; lia|]. split; [lia|]. split.
    + eapply cpy_equiv; [|exact ADV]. intro x. rewrite IE.
      change (63+1) with 64. apply nt_done_next_chunk. reflexivity.
    + split.
      * rewrite N.mod_small by (clear - NW B I; nia). clear - IE; nia.
      * split; [f_equal; clear - IE; nia|]. split; [lia|].
        split; [rewrite msub_sub by (clear - J; lia);
          rewrite N.mod_small by (clear - CB J; lia); clear - J; lia|].
        split; [exact DX|]. split; assumption.
  - apply N.eqb_neq in BC.
    exists j, (i+1). unfold nt_bulk_state, nt_offset, nt_chunk, nt_pages.
    nt_scalar_projections.
    split; [exact J|]. split; [clear - BC I; lia|]. split; [exact ADV|].
    split; [rewrite N.mod_small by (clear - NW B I; nia); clear; nia|].
    split; [f_equal; clear; nia|].
    split; [rewrite msub_sub by (clear - I; lia);
      rewrite N.mod_small by (clear - I; lia); clear - I; lia|].
    split; [exact R10|]. split; [exact DX|]. split; assumption.
Qed.

