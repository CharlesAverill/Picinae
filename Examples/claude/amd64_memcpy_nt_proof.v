(* SSE2 memcpy non-temporal proof work (x01-sse2-nt).

   Inherited provenance: /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64
   glibc 2.35-0ubuntu3.12, SHA256
   9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9;
   memcpy@GLIBC_2.2.5 at 0x1c4870, image base 0x100000.
   Ghidra 11.4.2 + pcode2coq, as documented in amd64_memcpy_proof.v.
   The generated IL is unchanged; its binary provenance is not revalidated.
   Original author/model: OpenAI GPT-6 Astra, November 2026.
   Proof-script repairs and additional support/witnesses: OpenAI GPT-6.1
   Sol, November 2026. The assigned full-entry strategy remains partial.

   English spec: copy original source bytes to the destination, with all
   bytes outside the destination unchanged. System V AMD64 input is
   RDI=destination, RSI=source, RDX=size; output RAX=destination. RSP is
   unchanged at RET and RBX/RBP/R12-R15 are preserved by the inherited
   whole-program frame theorem.

   This file currently proves support for the NT paths, not correctness
   from the public entry. In particular, the tail theorem starts after the
   bulk prefix has been copied. It does not assume the final result.
   Its exact prefix and pointer hypotheses appear in nt_tail_state below.
   Both two-page and four-page tails use four 16-byte SSE2 stores per row.
   The IL treats MOVNTDQ as ordinary stores and SFENCE/prefetch as no-ops;
   no hardware concurrency, cache, or CPU feature claim is made here.
 *)
Require Import Picinae_amd64 memcpy_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memcpy_proof
               amd64_memcpy_loops_proof.
Import ListNotations.
Open Scope N.

Definition nt_align (d:N) := 64 - d mod 64.
Lemma nt_align_bounds: forall d, 1 <= nt_align d <= 64.
Proof. intro d. unfold nt_align. pose proof (N.mod_lt d 64 ltac:(discriminate)). lia. Qed.

(* One abstract-memory row. All loads precede the stores, as in the IL. *)
Definition nt_row (M:memory) d s o :=
  M [Ⓧ d + o := M Ⓧ[s + o]]
    [Ⓧ d + o + 16 := M Ⓧ[s + o + 16]]
    [Ⓧ d + o + 32 := M Ⓧ[s + o + 32]]
    [Ⓧ d + o + 48 := M Ⓧ[s + o + 48]].

Lemma nt_row_advance: forall m M d s n W o,
  cpy m M d s W -> (forall x, W x -> x < n) -> nov d s n ->
  n < 2^64 -> o + 64 <= n ->
  cpy m (nt_row M d s o) d s (fun x => W x \/ o <= x < o + 64).
Proof.
  intros m M d s n W o C WN NOV NB O. unfold nt_row.
  eapply cpy_equiv; [|eapply (cpy_store4 m M d s n W o (o+16) (o+32) (o+48));
    [exact C|exact WN|exact NOV|exact NB|..]].
  { intro x. clear. cbv beta. intuition lia. }
  all: clear - O; first [lia | f_equal; lia].
Qed.

(* A chunk counter must be positive before entering a bottom-tested bulk
   loop. This exact criterion imposes no artificial upper bound on n. It
   is arithmetic support only: entry dispatch is not yet proved here. *)
Lemma nt_chunk_positive: forall pages d n, 0 < pages ->
  (0 < (n - nt_align d) / (4096 * pages) <->
   nt_align d + 4096 * pages <= n).
Proof.
  intros pages d n P. pose proof (nt_align_bounds d) as A.
  rewrite N.div_str_pos_iff by (clear - P; nia). lia.
Qed.

Lemma nt_chunk_positive_from_threshold: forall pages d n threshold,
  (pages = 2 \/ pages = 4) -> 16448 <= threshold -> threshold < n ->
  0 < (n - nt_align d) / (4096 * pages).
Proof.
  intros pages d n threshold P T N.
  pose proof (nt_align_bounds d) as A.
  destruct P as [-> | ->]; apply nt_chunk_positive; lia.
Qed.

(* Offset-set invariant shared by the two/four-page bulk loops. At each
   inner iteration, copy a 64-byte row on every page. *)
Definition nt_done (pages a j i x:N) :=
  x < 64 \/ a <= x < a + 4096 * pages * j \/
  exists p, p < pages /\
    a + 4096 * pages * j + 4096 * p <= x <
    a + 4096 * pages * j + 4096 * p + 64 * i.

Lemma nt_done_initial: forall pages a x,
  nt_done pages a 0 0 x <-> x < 64.
Proof. intros. unfold nt_done. split.
  - intros [H|[H|[p [P H]]]]; lia.
  - intro H; left; exact H.
Qed.

Lemma nt_done_chunk: forall pages a j x, 0 < pages ->
  (nt_done pages a j 64 x <-> x < 64 \/ a <= x < a + 4096 * pages * (j+1)).
Proof.
  intros pages a j x P. unfold nt_done.
  split.
  - intros [H|[H|[p [PP H]]]]; [left; exact H|right; nia|right; nia].
  - intros [H|H]; [left; exact H|].
    destruct (N.lt_ge_cases x (a + 4096 * pages * j)) as [LT|GE].
    + right; left; nia.
    + right; right. exists ((x - (a + 4096 * pages * j)) / 4096).
      pose proof (N.div_mod (x - (a + 4096 * pages * j)) 4096 ltac:(discriminate)) as E.
      pose proof (N.mod_lt (x - (a + 4096 * pages * j)) 4096 ltac:(discriminate)) as R.
      split; nia.
Qed.

Lemma nt_done_next_chunk: forall pages a j x, 0 < pages ->
  (nt_done pages a j 64 x <-> nt_done pages a (j+1) 0 x).
Proof.
  intros pages a j x POS. rewrite nt_done_chunk by exact POS. unfold nt_done.
  split; [tauto|]. intros [H|[H|[p [P H]]]]; try tauto; lia.
Qed.

(* q pages of the current row have been stored. This extra cut allows
   each of the sixteen stores in a four-page iteration to be verified
   without keeping the whole concrete memory term alive across a branch. *)
Definition nt_staged pages a j i q x :=
  nt_done pages a j i x \/
  exists p, p < q /\
    a + 4096 * pages * j + 4096 * p + 64 * i <= x <
    a + 4096 * pages * j + 4096 * p + 64 * i + 64.

Lemma nt_staged_zero: forall pages a j i x,
  nt_staged pages a j i 0 x <-> nt_done pages a j i x.
Proof. intros. unfold nt_staged. split; [intros [H|[p [P H]]]; [exact H|lia]|tauto]. Qed.

Lemma nt_staged_finish: forall pages a j i x,
  nt_staged pages a j i pages x <-> nt_done pages a j (i+1) x.
Proof.
  intros. unfold nt_staged, nt_done. split.
  - intros [[H|[H|[p [P H]]]]|[p [P H]]].
    + left; exact H.
    + right; left; exact H.
    + right; right; exists p; split; [exact P|nia].
    + right; right; exists p; split; [exact P|nia].
  - intros [H|[H|[p [P H]]]]; try tauto.
    destruct (N.lt_ge_cases x (a + 4096 * pages * j + 4096 * p + 64 * i)).
    + left; right; right; exists p; split; [exact P|nia].
    + right; exists p; split; [exact P|nia].
Qed.

Lemma nt_staged_bound: forall pages a j i q n x,
  1 <= a <= 64 -> i < 64 -> 0 < pages -> q <= pages ->
  a + 4096 * pages * (j+1) <= n ->
  nt_staged pages a j i q x -> x < n.
Proof.
  intros pages a j i q n x A I PAGES Q B H.
  unfold nt_staged, nt_done in H.
  destruct H as [[H|[H|[p [P H]]]]|[p [P H]]]; nia.
Qed.

Lemma nt_staged_advance: forall m M d s n pages a j i q,
  1 <= a <= 64 -> i < 64 -> q < pages ->
  a + 4096 * pages * (j+1) <= n -> nov d s n -> n < 2^64 ->
  cpy m M d s (nt_staged pages a j i q) ->
  cpy m (nt_row M d s (a + 4096 * pages * j + 4096 * q + 64 * i)) d s
    (nt_staged pages a j i (q+1)).
Proof.
  intros m M d s n pages a j i q A I Q B NOV NB C.
  eapply cpy_equiv; [|apply (nt_row_advance m M d s n); [exact C| |exact NOV|exact NB|]].
  - intro x. unfold nt_staged. split.
    + intros [[H|[p [P H]]]|H]; [left; exact H|right; exists p; split; [lia|exact H]|].
      right; exists q; split; [lia|exact H].
    + intros [H|[p [P H]]]; [left; left; exact H|].
      destruct (N.eq_dec p q) as [->|NE]; [right; exact H|].
      left; right; exists p; split; [lia|exact H].
  - intros x H. eapply nt_staged_bound; [exact A|exact I| | |exact B|exact H]; lia.
  - clear - I Q B. nia.
Qed.

(* Actual lifted tail cutpoints, for either NT strategy. *)
Definition nt_tail_state m d s n rsp c (st:store) :=
  c <= n /\ n - c < 2^32 /\ cpy m (st V_MEM64) d s (fun x => x < c) /\
  st R_RDI = d + c /\ st R_RSI = s ⊕ c /\ st R_RDX = n - c /\
  st R_RAX = d /\ st R_RSP = rsp.
Definition nt_tail_exit (t:trace) :=
  match t with (Addr a,_)::_ =>
    match a with 1854761 | 1855185 => true | _ => false end
  | _ => false end.
Definition nt_tail_invs m d s n rsp (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1854667 | 1855091 => Some (exists c, c + 64 < n /\ nt_tail_state m d s n rsp c st)
  | 1854721 | 1855145 => Some (exists c, n - 64 <= c /\ nt_tail_state m d s n rsp c st)
  | 1854761 | 1855185 => Some (postcondition m d s n rsp st)
  | _ => None end | _ => None end.

Lemma nt_tail_addr: forall x c n k, k < 2^64 -> k <= n -> c <= n ->
  (x ⊖ k + c) ⊕ (n - c) = x ⊕ (n - k).
Proof.
  intros x c n k KB KN CN. unfold msub.
  rewrite (N.mod_small k) by exact KB.
  rewrite <- N.add_assoc, N.add_mod_idemp_l by discriminate.
  replace (x + (2^64 - k) + (c + (n-c))) with ((x + (n-k)) + 1 * 2^64)
    by (change (2^64) with 18446744073709551616 in *; lia).
  rewrite N.mod_add by discriminate. reflexivity.
Qed.

Lemma nt_tail_final: forall (four:bool) m d s n rsp st t,
  nov d s n -> n < 2^64 -> 64 <= n -> models archtyps st ->
  (exists c, n - 64 <= c /\ nt_tail_state m d s n rsp c st) ->
  nextinv memcpy_amd64 (nt_tail_invs m d s n rsp) nt_tail_exit false
    ((Addr (if four then 1855145 else 1854721), st)::t).
Proof.
  intros four m d s n rsp st t NOV NB BIG MDL PRE.
  destruct PRE as [c [CL [CU [REM [C [RDI [RSI [RDX [RAX RSP]]]]]]]]].
  destruct four; repeat x64_step.
  all: rewrite ?pack16.
  all: split; [exact RAX|]; split; [exact RSP|].
  all: eapply cpy_copied; cycle 1.
  all: try (eapply (cpy_store4 m (st V_MEM64) d s n (fun x => x < c)
                    (n-64) (n-48) (n-32) (n-16));
    [exact C | intros i I; clear - CU I; lia | exact NOV | exact NB | ..];
    try (clear - BIG; lia);
    rewrite nt_tail_addr by (clear - BIG CU; change (2^64) with 18446744073709551616; lia);
    reflexivity).
  all: intro i; clear - CL CU BIG; split; intro H; repeat destruct H as [H|H]; lia.
Qed.

Lemma nt_remainder_sub: forall a, 64 <= a -> a < 2^32 ->
  msub 32 a 64 = a - 64.
Proof.
  intros a A B. rewrite msub_sub by exact A. apply N.mod_small.
  clear - B. lia.
Qed.

Lemma nt_tail_loop: forall (four:bool) m d s n rsp st t,
  nov d s n -> n < 2^64 -> d + n < 2^64 -> models archtyps st ->
  (exists c, c + 64 < n /\ nt_tail_state m d s n rsp c st) ->
  nextinv memcpy_amd64 (nt_tail_invs m d s n rsp) nt_tail_exit false
    ((Addr (if four then 1855091 else 1854667), st)::t).
Proof.
  intros four m d s n rsp st t NOV NB NW MDL PRE.
  destruct PRE as [c [CL [CU [REM [C [RDI [RSI [RDX [RAX RSP]]]]]]]]].
  assert (RE: msub 32 (n-c) 64 = n-(c+64)).
  { rewrite nt_remainder_sub by (clear - CL REM; lia). clear - CL; lia. }
  destruct four; repeat x64_step.
  all: rewrite ?pack16.
  all: assert (ADV: cpy m
      ((st V_MEM64) [Ⓧ d+c := st V_MEM64 Ⓧ[s+c]]
        [Ⓧ 16+d+c := st V_MEM64 Ⓧ[16+s+c]]
        [Ⓧ 32+d+c := st V_MEM64 Ⓧ[32+s+c]]
        [Ⓧ 48+d+c := st V_MEM64 Ⓧ[48+s+c]]) d s (fun x => x < c+64)).
  all: try (eapply cpy_equiv; [|eapply (cpy_store4 m (st V_MEM64) d s n (fun x => x<c)
                      c (c+16) (c+32) (c+48));
     [exact C|intros x X; clear - X CU; lia|exact NOV|exact NB|..]];
     [intro x; clear; lia|..]; clear - CL; first [lia|f_equal; lia]).
  all: exists (c+64); split.
  all: try (apply ja_not_taken in BC; destruct BC as [BC|BC];
      [apply N.ltb_lt in BC; rewrite RE in BC|
       apply N.eqb_eq in BC; rewrite N.mod_small in BC by exact REM];
      clear - BC CL; lia).
  all: try (apply ja_taken in BC; destruct BC as [B1 B2];
      apply N.ltb_ge in B1; apply N.eqb_neq in B2;
      rewrite RE in B1; rewrite N.mod_small in B2 by exact REM;
      clear - B1 B2 CL; lia).
  all: unfold nt_tail_state; split; [clear - CL; lia|];
    split; [clear - REM; lia|]; split; [exact ADV|].
  all: split; [change (64 + d ⊕ c = d + (c+64));
    rewrite N.mod_small by (clear - NW CL; lia); clear; lia|].
  all: split; [change (64 + s ⊕ c = s ⊕ (c+64)); f_equal; clear; lia|].
  all: split; [exact RE|]; split; [exact RAX|exact RSP].
Qed.

(* Partial correctness from either bulk-complete tail loop entry. The caller
   supplies a copied prefix, not a copied whole buffer. No tunable is read
   on this suffix, so it needs no threshold/CPU-data hypotheses. *)
Theorem memcpy_nt_tail_correct:
  forall (four:bool) st t st' x' m d s n rsp c
    (ENTRY: startof t (x',st') = (Addr (if four then 1855091 else 1854667), st))
    (MDL: models x64typctx st)
    (NOV: nov d s n) (NB: n < 2^64) (NW: d+n < 2^64)
    (MORE: c+64 < n) (PRE: nt_tail_state m d s n rsp c st),
  satisfies_all memcpy_amd64 (nt_tail_invs m d s n rsp) nt_tail_exit ((x',st')::t).
Proof.
  intros. apply prove_invs.
  - simpl. rewrite ENTRY. destruct four; x64_step; exists c; split; assumption.
  - intros. erewrite startof_prefix in ENTRY; try eassumption.
    eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
    clear - PRE0 MDL1 NOV NB NW MORE. rename t1 into t.
    assert (BIG: 64 <= n) by (clear - MORE; lia).
    destruct_inv 64 PRE0.
    + apply (nt_tail_loop false); assumption.
    + apply (nt_tail_final false); assumption.
    + apply (nt_tail_loop true); assumption.
    + apply (nt_tail_final true); assumption.
Qed.

(* A concrete initial-state witness with no bytes assumed copied. *)
Definition nt_tail_witness : store := fun v => match v with
  | R_RDI | R_RAX => 4096 | R_RSI => 8192 | R_RDX => 128
  | _ => 0 end.
Theorem memcpy_nt_tail_nonvacuous:
  models x64typctx nt_tail_witness /\ nov 4096 8192 128 /\
  128 < 2^64 /\ 4096+128 < 2^64 /\ 0+64 < 128 /\
  nt_tail_state 0 4096 8192 128 0 0 nt_tail_witness.
Proof.
  split.
  { intros v w T. destruct v; inversion T; subst;
      cbv [nt_tail_witness]; first [apply N.neq_0_lt_0; apply N.pow_nonzero; discriminate
            | reflexivity]. }
  split.
  { intros i j I J. rewrite !N.mod_small by (clear - I J; lia).
    clear - I J. lia. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  unfold nt_tail_state. split; [lia|]. split; [reflexivity|]. split.
  { eapply cpy_equiv; [|apply cpy_empty]. intro x; cbv beta; lia. }
  repeat split; reflexivity.
Qed.

(* Four actual MOVNTDQ instructions, with vector values loaded before this
   cut. The proof has abstract incoming memory and stops before the next
   page's stores. This is a memory advance, not a public-entry theorem. *)
Definition nt_page_invs m d s o W (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 1854592 | 1854944 =>
      Some (cpy m (st V_MEM64) d s (fun x => W x \/ o <= x < o+64))
  | _ => None end | _ => None end.
Lemma memcpy_nt_first_page_stores: forall (four:bool) m d s n o W st t,
  models archtyps st -> cpy m (st V_MEM64) d s W ->
  (forall x, W x -> x < n) -> n < 2^64 -> o+64 <= n ->
  st R_RDI = d+o ->
  st R_YMM0 mod 2^128 = m Ⓧ[s+o] ->
  st R_YMM1 mod 2^128 = m Ⓧ[s+o+16] ->
  st R_YMM2 mod 2^128 = m Ⓧ[s+o+32] ->
  st R_YMM3 mod 2^128 = m Ⓧ[s+o+48] ->
  nextinv memcpy_amd64 (nt_page_invs m d s o W) (fun _ => false) false
    ((Addr (if four then 1854925 else 1854573), st)::t).
Proof.
  intros four m d s n o W st t MDL C WN NB O RDI X0 X1 X2 X3.
  destruct four; repeat x64_step.
  all: rewrite <- (setmem_mod_r 64 LittleE 16 _ _ (st R_YMM0)),
               <- (setmem_mod_r 64 LittleE 16 _ _ (st R_YMM1)),
               <- (setmem_mod_r 64 LittleE 16 _ _ (st R_YMM2)),
               <- (setmem_mod_r 64 LittleE 16 _ _ (st R_YMM3)).
  all: change (2^(16*8)) with (2^128); rewrite X0, X1, X2, X3.
  all: eapply cpy_equiv; [|eapply (cpy_store _ _ _ _ _ (o+48));
    [eapply (cpy_store _ _ _ _ _ (o+32));
      [eapply (cpy_store _ _ _ _ _ (o+16));
        [eapply (cpy_store _ _ _ _ _ o); [exact C|..]|..]|..]|..]].
  all: try (intro x; clear; cbv beta; intuition lia).
  all: try (intros x H; cbv beta in H; clear - H WN NB O;
      repeat destruct H as [H|H]; try apply WN in H;
      change (2^64) with 18446744073709551616 in *; lia).
  all: clear - O NB; change (2^64) with 18446744073709551616 in *;
    first [lia | f_equal; lia].
Qed.

(* A head constructed by the four actual source-sized stores supplies the
   initial staging relation, for arbitrary source contents. No whole-buffer
   copy is assumed. The genuine nonoverlap and size hypotheses are explicit. *)
Lemma nt_staged_initial_witness: forall m d s n pages a,
  64 <= n -> nov d s n -> n < 2^64 ->
  cpy m (nt_row m d s 0) d s (nt_staged pages a 0 0 0).
Proof.
  intros m d s n pages a BIG NOV NB.
  eapply cpy_equiv; [|apply (nt_row_advance m m d s n (fun _ => False) 0);
    [apply cpy_empty|intros x []|exact NOV|exact NB|exact BIG]].
  intro x. rewrite nt_staged_zero, nt_done_initial. cbv beta. lia.
Qed.

(* All premises of the staged-row advance are simultaneously inhabited for
   both page counts. Construct the copied head, then advance its first row.
   In particular, the invariant does not require an already copied buffer. *)
Theorem nt_staged_advance_nonvacuous: forall pages, (pages = 2 \/ pages = 4) ->
  exists m M d s n a,
    1 <= a <= 64 /\ 0 < 64 /\ 0 < pages /\
    a + 4096 * pages * (0+1) <= n /\ nov d s n /\ n < 2^64 /\
    cpy m M d s (nt_staged pages a 0 0 0).
Proof.
  intros pages P.
  assert (NOV: nov 65536 131072 16448).
  { intros i j I J. rewrite !N.mod_small by (clear - I J; lia).
    clear - I J; lia. }
  exists 0, (nt_row 0 65536 131072 0), 65536, 131072, 16448, 64.
  split; [lia|]. split; [reflexivity|].
  split; [destruct P as [-> | ->]; reflexivity|].
  split; [destruct P as [-> | ->]; lia|].
  split; [exact NOV|]. split; [reflexivity|].
  apply (nt_staged_initial_witness 0 65536 131072 16448 pages 64);
    first [exact NOV|reflexivity|lia].
Qed.

(* Concrete values satisfy every first-page-store premise, with an empty
   written set. The four low lanes contain actual loads from zero memory. *)
Theorem memcpy_nt_first_page_stores_nonvacuous:
  models archtyps nt_tail_witness /\
  cpy 0 (nt_tail_witness V_MEM64) 4096 8192 (fun _ => False) /\
  (forall x:N, False -> x < 128) /\ 128 < 2^64 /\ 0+64 <= 128 /\
  nt_tail_witness R_RDI = 4096+0 /\
  nt_tail_witness R_YMM0 mod 2^128 = 0 Ⓧ[8192+0] /\
  nt_tail_witness R_YMM1 mod 2^128 = 0 Ⓧ[8192+0+16] /\
  nt_tail_witness R_YMM2 mod 2^128 = 0 Ⓧ[8192+0+32] /\
  nt_tail_witness R_YMM3 mod 2^128 = 0 Ⓧ[8192+0+48].
Proof.
  split; [exact (proj1 memcpy_nt_tail_nonvacuous)|].
  split; [apply cpy_empty|]. split; [intros x []|].
  split; [reflexivity|]. split; [lia|]. repeat split; reflexivity.
Qed.
