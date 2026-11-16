(* memchr -- scan memory for a byte (musl x86_64, C)

   SEMANTICS
   ---------
   musl's memchr (src/string/memchr.c) is

       const unsigned char *s = src;
       c = (unsigned char)c;
       for (; ((uintptr_t)s & ALIGN) && n && *s != c; s++, n--);
       if (n && *s != c) {
           typedef size_t __attribute__((__may_alias__)) word;
           const word *w;
           size_t k = ONES * c;
           for (w = (const void * )s; n>=SS && !HASZERO( *w^k); w++, n-=SS);
           s = (const void * )w;
       }
       for (; n && *s != c; s++, n--);
       return n ? (void * )s : 0;

   GCC compiled the word loop with an end pointer s + (n & ~7) and saves RBX
   on the stack for it, so this one path writes the 8 bytes below RSP.  The
   word test HASZERO(w ^ c*ONES) = 0 means no byte of w equals c
   (haszero_bytes_msub + byte_of_lxor).

   SPECIFICATION (man 3 memchr, Linux man-pages 6.9.1)
   ---------------------------------------------------

     SYNOPSIS
            #include <string.h>
            void *memchr(const void s[.n], int c, size_t n);

     DESCRIPTION
            The memchr() function scans the initial n bytes of the memory
            area pointed to by s for the first instance of c.  Both c and the
            bytes of the memory area pointed to by s are interpreted as
            unsigned char.

     RETURN VALUE
            The memchr() and memrchr() functions return a pointer to the
            matching byte or NULL if the character does not occur in the
            given memory area.

   PROVENANCE
   ----------
   Binary:  alpine_musl/x86_64/lib/libc.musl-x86_64.so.1, Alpine musl-1.2.6-r6
            sha256 cc3e02006173e4d7c11c5d37deded8749cfe7786f71a70a5c87fa6f509714647
            memchr at 0x23940 (Ghidra image base 0x100000: 0x123940)
   Lifter:  Ghidra 12.0 (headless) + pcode2coq (tools/ghidra-lifter) with
            --globalAddressing; see lift.sh and programs/memchr_amd64.v.
   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked
            by Rocq 9.1.

   INPUT/OUTPUT SPECIFICATION (System V AMD64 ABI)
   -----------------------------------------------
   Input:   RDI = s, ESI = c (only c8 = c mod 256 matters), RDX = n;
            RSP = rsp; m = memory on entry.  Precondition: the n-byte area
            does not overlap the 8 bytes below rsp (where memchr saves RBX;
            no live C object can be there).
   Output:  At any of the four RETs, memchr_result holds: either some K < n
            has s[i] <> c8 for i < K, s[K] = c8 and RAX = s + K (mod 2^64),
            or no byte of s[0..n) equals c8 and RAX = 0 (NULL).  No byte
            outside the 8 bytes below rsp has changed (stack_frame); RSP = rsp;
            RBX, RBP, R12-R15 are unchanged.
 *)

Require Import Picinae_amd64.
Require Import CoqEtTu.programs.memchr_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Import ListNotations.
Require Import CoqEtTu.lib.x64_common CoqEtTu.lib.x64_abi CoqEtTu.lib.x64_haszero CoqEtTu.lib.x64_compose.
Open Scope N.

Theorem memchr_nwc: forall s2 s1, memchr_amd64 s1 = memchr_amd64 s2.
Proof. reflexivity. Qed.

Theorem memchr_welltyped: welltyped_prog x64typctx memchr_amd64.
Proof. exact welltyped. Qed.

(* bytes p+0 .. p+k-1 all differ from c *)
Definition cabsent (m:memory) (p c k:N) := forall i, i < k -> m Ⓑ[p ⊕ i] <> c.

Definition memchr_result (m:memory) (p c n r:N) :=
  (exists K, K < n /\ cabsent m p c K /\ m Ⓑ[p ⊕ K] = c /\ r = p ⊕ K) \/
  (cabsent m p c n /\ r = 0).

Lemma byte_load_off: forall (m:memory) p k, m Ⓑ[p ⊕ k] = m Ⓑ[p + k].
Proof. intros. apply getmem_mod_l. Qed.

Lemma land_align8: forall x, x < 2^64 -> x .& 18446744073709551608 = x - x mod 8.
Proof.
  intros x X.
  assert (E: x - x mod 8 = x >> 3 << 3).
  { rewrite N.shiftl_mul_pow2, N.shiftr_div_pow2. change (2^3) with 8.
    rewrite (N.div_mod x 8) at 1 by discriminate. lia. }
  rewrite E. change 18446744073709551608 with (N.ldiff (N.ones 64) (N.ones 3)).
  apply N.bits_inj. intro i. rewrite N.land_spec, N.ldiff_spec.
  destruct (N.ltb_spec i 3).
  - rewrite (N.ones_spec_low 3 i), N.shiftl_spec_low by lia. cbn [negb].
    rewrite !Bool.andb_false_r. reflexivity.
  - rewrite (N.ones_spec_high 3 i) by lia. rewrite N.shiftl_spec_high, N.shiftr_spec by lia.
    replace (i - 3 + 3) with i by lia. cbn [negb]. rewrite Bool.andb_true_r.
    destruct (N.ltb_spec i 64).
    + rewrite N.ones_spec_low by lia. apply Bool.andb_true_r.
    + rewrite N.ones_spec_high by lia. rewrite Bool.andb_false_r. symmetry.
      destruct x as [|q]. apply N.bits_0.
      apply N.bits_above_log2. apply N.lt_le_trans with 64; [|lia].
      apply N.log2_lt_pow2; [reflexivity|exact X].
Qed.

(* Reads inside the buffer do not see the saved RBX below the stack pointer. *)
Lemma frame_get:
  forall m p n a v i len, ~ overlap 64 p n a 8 -> i + len <= n ->
  getmem 64 LittleE len (m [Ⓠa := v]) (p + i) = getmem 64 LittleE len m (p + i).
Proof.
  intros m p n a v i len NOV I. apply getmem_noverlap. intros [x [y [X [Y E]]]].
  apply NOV. exists (i + x), y. split. lia. split. lia.
  change (2^64) with 18446744073709551616 in *. lia.
Qed.

Lemma cabsent_succ: forall m p c k, cabsent m p c k -> m Ⓑ[p ⊕ k] <> c -> cabsent m p c (k + 1).
Proof.
  intros m p c k CA B i I. destruct (N.lt_ge_cases i k). apply CA. assumption.
  replace i with k by lia. exact B.
Qed.

Lemma cabsent_add8:
  forall (m:memory) p c k, c < 256 -> cabsent m p c k ->
  N.lnot (m Ⓠ[p + k] .^ c * 0x0101010101010101) 64 .&
    (m Ⓠ[p + k] .^ c * 0x0101010101010101) ⊖ 0x0101010101010101 .& 0x8080808080808080 = 0 ->
  cabsent m p c (k + 8).
Proof.
  intros m p c k C CA H i I. destruct (N.lt_ge_cases i k) as [IK|IK]. apply CA, IK.
  assert (X: m Ⓠ[p + k] .^ c * 0x0101010101010101 < 2^64).
  { pose proof (getmem_bound 64 LittleE 8 m (p + k)) as GB. change (2^(8*8)) with (2^64) in GB.
    apply lxor_bound. exact GB. change (2^64) with 18446744073709551616. lia. }
  pose proof (haszero_bytes_msub _ X H (i - k) ltac:(lia)) as B.
  rewrite byte_of_lxor, byte_of_bcast, byte_of_load in B by lia.
  rewrite !getmem_mod_l in *. replace (p + k + (i - k)) with (p + i) in B by lia.
  apply lxor_neq0, B.
Qed.

Lemma c8_lt: forall c, c mod 2^8 < 256.
Proof. intros. apply N.mod_lt. discriminate. Qed.

Lemma bcast_r9: forall c,
  scast 32 64 ((c mod 2^8 >> 0) mod 2^32) ⊗ 72340172838076673 = c mod 2^8 * 72340172838076673.
Proof.
  intros. pose proof (c8_lt c).
  rewrite N.shiftr_0_r, (N.mod_small (c mod 2^8)), scast_32_64_small by
    (change (2^32) with 4294967296; change (2^31) with 2147483648; lia).
  apply N.mod_small. change (2^64) with 18446744073709551616. lia.
Qed.

Ltac reg_tac := repeat first [rewrite update_updated | rewrite update_frame by discriminate]; first [sreflexivity | sassumption].



Definition memchr_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 0x1239aa | 0x123a15 | 0x123a34 | 0x123a37 => true
  | _ => false end | _ => false end.

Definition memchr_post (s0:store) (m p c n:N) (s:store) :=
  memchr_result m p (c mod 2^8) n (s R_RAX) /\
  stack_frame m (s V_MEM64) (s0 R_RSP) 8 /\
  s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s.

(* common part of the loop invariants *)
Definition scan (s0:store) (m p c n k:N) (s:store) :=
  k <= n /\ cabsent m p (c mod 2^8) k /\ s R_RSI = c mod 2^8.

(* while RBX is saved on the stack *)
Definition cs_but_rbx (s0 s:store) :=
  s R_RBP = s0 R_RBP /\ s R_R12 = s0 R_R12 /\ s R_R13 = s0 R_R13 /\
  s R_R14 = s0 R_R14 /\ s R_R15 = s0 R_R15.

Ltac cs_tac :=
  lazymatch goal with
  | CS: callee_saved_eq ?s0 _ |- cs_but_rbx ?s0 _ =>
      destruct CS as (_ & ?&?&?&?&?); repeat split; rewrite ?update_frame by discriminate; assumption
  | CS: cs_but_rbx ?s0 _ |- cs_but_rbx ?s0 _ =>
      destruct CS as (?&?&?&?&?); repeat split; rewrite ?update_frame by discriminate; assumption
  | CS: cs_but_rbx ?s0 _ |- callee_saved_eq ?s0 _ =>
      destruct CS as (?&?&?&?&?); repeat split; rewrite ?update_frame by discriminate;
      first [assumption | rewrite update_updated; apply N.mod_small; assumption]
  end.

Ltac frame_tac :=
  lazymatch goal with |- stack_frame _ _ _ _ =>
    repeat (apply stack_frame_store; [lia | reflexivity |]);
    first [ apply stack_frame_refl
          | match goal with H: _ V_MEM64 = _ |- _ => rewrite H; apply stack_frame_refl end ]
  end.
Ltac fin := conj_tac; try cs_tac; try frame_tac; try (apply N.mod_small; assumption).


Definition memchr_invs (s0:store) (m p c n:N) (t:trace) :=
  match t with (Addr a,s)::_ => match a with
  | 0x123940 => Some (s V_MEM64 = m /\ s R_RDI = p /\ s R_RSI = c /\ s R_RDX = n /\
                      s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* alignment loop; 0x123966: a byte is left, test it *)
  | 0x123951 => Some (exists k, s R_RCX = p ⊕ k /\ s R_RDX = n - k /\ scan s0 m p c n k s /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x123966 => Some (exists k, s R_RCX = p ⊕ k /\ s R_RDX = n - k /\ k < n /\ scan s0 m p c n k s /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  (* word loop, after PUSH RBX *)
  | 0x1239c4 => Some (exists k e, s R_RCX = p ⊕ k /\ s R_RAX = p ⊕ e /\ s R_R10 = p ⊕ n /\
                      k <= e /\ e <= n /\ n - e < 8 /\ (e - k) mod 8 = 0 /\ scan s0 m p c n k s /\
                      s R_R9 = c mod 2^8 * 0x0101010101010101 /\ s R_RBX = 0xfefefefefefefeff /\
                      s R_R11 = 0x8080808080808080 /\
                      s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] /\ s R_RSP = s0 R_RSP ⊖ 8 /\
                      cs_but_rbx s0 s)
  (* tail loops, with and without RBX pushed *)
  | 0x123a08 => Some (exists k, s R_RAX = p ⊕ k /\ s R_RDX = n - k /\ scan s0 m p c n k s /\
                      s V_MEM64 = m [Ⓠs0 R_RSP ⊖ 8 := s0 R_RBX] /\ s R_RSP = s0 R_RSP ⊖ 8 /\
                      cs_but_rbx s0 s)
  | 0x123a28 => Some (exists k, s R_RAX = p ⊕ k /\ s R_RDX = n - k /\ scan s0 m p c n k s /\
                      s V_MEM64 = m /\ s R_RSP = s0 R_RSP /\ callee_saved_eq s0 s)
  | 0x1239aa | 0x123a15 | 0x123a34 | 0x123a37 => Some (memchr_post s0 m p c n s)
  | _ => None
  end | _ => None end.

Theorem memchr_correct:
  forall prog s t s' x' m p c n
         (MEMCHR: memchr_amd64 ⊆2 prog)
         (ENTRY: startof t (x',s') = (Addr 0x123940, s))
         (MDL: models x64typctx s)
         (MEM: s V_MEM64 = m) (P: s R_RDI = p) (C: s R_RSI = c) (Nn: s R_RDX = n)
         (NOV: ~ overlap 64 p n (s R_RSP ⊖ 8) 8),
  satisfies_all prog (memchr_invs s m p c n) memchr_exit ((x',s')::t).
Proof.
  intros prog s0 t s' x' m p c n MEMCHR ENTRY MDL MEM P C Nn NOV.
  assert (RB: s0 R_RSP < 2^64) by (apply (MDL R_RSP 64); reflexivity).
  assert (RBXB: s0 R_RBX < 2^64) by (apply (MDL R_RBX 64); reflexivity).
  assert (PB: p < 2^64) by (rewrite <- P; apply (MDL R_RDI 64); reflexivity).
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  eapply satisfies_all_pmono with (p1:=memchr_amd64); [exact MEMCHR| |].
    intros a s1 t1 EXIT NOCODE. unfold memchr_invs.
    repeat first
    [ reflexivity | discriminate EXIT | discriminate NOCODE
    | match goal with |- context [match ?n with _ => _ end] => destruct n end ].
  intros [x1 s1] t1 START. rewrite ENTRY in START.
  clear - s0 m p c n MDL MEM P C Nn PB NB NOV RB RBXB START.
  rename t1 into t. rename s1 into s'. rename x1 into x'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. conj_tac. apply callee_saved_eq_refl.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memchr_welltyped. intro MDL1.
  clear - PRE MDL1 PB NB NOV RB RBXB. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [P [C [Nn [RSP CS]]]]].
    repeat x64_step. all: bc_norm.
    + (* the alignment loop *)
      exists 0. rewrite N.add_0_r, N.mod_small by assumption. split. reflexivity.
      split. rewrite N.sub_0_r. assumption.
      split. split. mlia64. split. intros i I. mlia64. reg_tac. fin.
  - (* alignment loop *)
    destruct PRE as [k [RCX [RDX [[KN [CA RSI]] [MEM [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + split. right. split. replace n with k by mlia64. assumption. reflexivity. fin.
    + exists k. split. reflexivity. split. reflexivity. split. mlia64.
      split. split. assumption. split. assumption. reg_tac. fin.
    + split. right. split. replace n with k by mlia64. assumption. reflexivity. fin.
    + exists k. split. reflexivity. split. reflexivity. split. mlia64.
      split. split. assumption. split. assumption. reg_tac. fin.
    + exists (k + 1). split. f_equal. mlia64.
      split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. split. mlia64. split. apply cabsent_succ; assumption. reg_tac.
      fin.
  - (* 0x123966 *)
    destruct PRE as [k [RCX [RDX [KN [[KN' [CA RSI]] [MEM [RSP CS]]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + (* the byte equals c: hand over to the tail loop, which returns it *)
      exists k. split. reflexivity. split. assumption.
      split. split. assumption. split. assumption. reg_tac. fin.
    + (* enter the word loop *)
      pose proof (proj1 CS) as B.
      exists k, (k + (n - k .& 18446744073709551608)).
      assert (A: n - k .& 18446744073709551608 = (n - k) - (n - k) mod 8) by (apply land_align8; mlia64).
      pose proof (N.mod_lt (n - k) 8 ltac:(discriminate)) as ML.
      pose proof (N.div_mod (n - k) 8 ltac:(discriminate)) as DM.
      split. reflexivity. split. f_equal. mlia64. split. f_equal. mlia64.
      split. mlia64. split. mlia64. split. mlia64.
      split. rewrite A. replace (k + (n - k - (n - k) mod 8) - k) with (8 * ((n - k) / 8)) by mlia64.
        rewrite N.mul_comm. apply N.Div0.mod_mul.
      split. split. assumption. split. assumption. reg_tac.
      split. apply bcast_r9. split. reflexivity. split. reflexivity.
      split. rewrite B. reflexivity. split. reflexivity. cs_tac.
  - (* word loop *)
    destruct PRE as [k [e [RCX [RAX [R10 [KE [EN [NE [EK [[KN [CA RSI]] [R9 [RBX [R11 [MEM [RSP CS]]]]]]]]]]]]]]].
    repeat x64_step. all: bc_norm.
    + (* end of the word region: the tail loop *)
      assert (KE': k = e) by mlia64. clear BC. subst e.
      exists k. split. reflexivity. split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. split. assumption. split. assumption. reg_tac. fin.
    + (* no hit: next word *)
      assert (KE': k <> e) by mlia64. clear BC.
      rewrite (frame_get m p n) in BC0 by (assumption || mlia64).
      exists (k + 8), e. split. f_equal. mlia64. split. reflexivity. split. reflexivity.
      split. mlia64. split. assumption. split. assumption.
      split. rewrite N.sub_add_distr.
        rewrite <- (N.mod_add (e - k - 8) 1) by discriminate. replace (e - k - 8 + 1 * 8) with (e - k) by mlia64.
        assumption.
      split. split. mlia64. split. apply cabsent_add8. apply c8_lt. assumption. assumption.
        reg_tac.
      fin.
    + (* maybe a hit: the tail loop *)
      exists k. split. reflexivity. split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. split. assumption. split. assumption. reg_tac. fin.
  - (* tail loop, pushed *)
    destruct PRE as [k [RAX [RDX [[KN [CA RSI]] [MEM [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: try (rewrite (frame_get m p n) in BC0 by (assumption || mlia64)).
    all: try (rewrite (frame_get m p n) in BC1 by (assumption || mlia64)).
    all: rewrite <- ?byte_load_off in *.
    + split. right. split. replace n with k by mlia64. assumption. reflexivity. fin.
    + split. left. exists k. repeat split; try assumption; mlia64.
      fin.
    + exists (k + 1). split. f_equal. mlia64.
      split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. split. mlia64. split. apply cabsent_succ; assumption. reg_tac.
      fin.
  - (* tail loop *)
    destruct PRE as [k [RAX [RDX [[KN [CA RSI]] [MEM [RSP CS]]]]]].
    repeat x64_step. all: bc_norm.
    all: rewrite <- ?byte_load_off in *.
    + split. right. split. replace n with k by mlia64. assumption. reflexivity. fin.
    + split. left. exists k. repeat split; try assumption; mlia64. fin.
    + exists (k + 1). split. f_equal. mlia64.
      split. rewrite msub_nowrap; rewrite !N.mod_small; mlia64.
      split. split. mlia64. split. apply cabsent_succ; assumption. reg_tac.
      fin.
Qed.
