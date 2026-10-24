(* Shared definitions for the C string functions (strsep, strtok_r, ...).

   A C string at address s in memory m is the byte sequence m[s], m[s+1], ...
   up to and including the first NUL.  The definitions below talk only about
   the bytes up to the terminator, so they make sense for any memory.

   * inset m r c: byte c occurs in the string at r, or c is r's terminator.
     (Callers use it only for nonzero c, where it means "c is one of r's
     characters".)
   * slen m s n: n = strlen(s).
   * cspn m s r n: n = strcspn(s, r), the length of the initial segment of s
     with no byte of r.
   * spn m s r n:  n = strspn(s, r), the length of the initial segment of s
     made only of bytes of r.
   * agree lo len M1 M2: M1 and M2 hold the same bytes outside the window
     [lo, lo+len) (a stack frame).
   * strfree lo len m p: the string at p, including its terminator, lies
     outside the window.

   The lemmas transfer cspn/spn between memories that agree outside a frame
   when the strings involved lie outside it.  Written by Claude Opus 5.5
   (claude-opus-5-5) and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith Lia.
Require Import amd64_common.
Open Scope N.

Definition inwin (lo len a:N) := msub 64 a lo < len.
Definition agree lo len (M1 M2:memory) := forall a, ~ inwin lo len a -> M1 Ⓑ[a] = M2 Ⓑ[a].
Definition strfree lo len (m:memory) p :=
  forall k, (forall j, j < k -> m Ⓑ[p ⊕ j] <> 0) -> ~ inwin lo len (p ⊕ k).

Definition inset (m:memory) r c :=
  exists j, m Ⓑ[r ⊕ j] = c /\ forall k, k < j -> m Ⓑ[r ⊕ k] <> 0.
Definition slen (m:memory) s n :=
  (forall k, k < n -> m Ⓑ[s ⊕ k] <> 0) /\ m Ⓑ[s ⊕ n] = 0.
Definition cspn (m:memory) s r n :=
  (forall k, k < n -> m Ⓑ[s ⊕ k] <> 0 /\ ~ inset m r (m Ⓑ[s ⊕ k])) /\
  (m Ⓑ[s ⊕ n] = 0 \/ inset m r (m Ⓑ[s ⊕ n])).
Definition spn (m:memory) s r n :=
  (forall k, k < n -> m Ⓑ[s ⊕ k] <> 0 /\ inset m r (m Ⓑ[s ⊕ k])) /\
  ~ (m Ⓑ[s ⊕ n] <> 0 /\ inset m r (m Ⓑ[s ⊕ n])).

Section Agree.
  Variables lo len : N.

  Lemma agree_refl: forall M, agree lo len M M.
  Proof. intros M a _. reflexivity. Qed.

  Lemma agree_trans: forall M1 M2 M3, agree lo len M1 M2 -> agree lo len M2 M3 -> agree lo len M1 M3.
  Proof. intros M1 M2 M3 A B a H. rewrite (A a H). apply B, H. Qed.

  (* The same store applied to agreeing memories. *)
  Lemma agree_set:
    forall M1 M2 L a v, 0 < L -> L <= 2^64 -> agree lo len M1 M2 ->
    agree lo len (setmem 64 LittleE L M1 a v) (setmem 64 LittleE L M2 a v).
  Proof.
    intros M1 M2 L a v L0 LL A b B. rewrite !byte_setmem_cases by assumption.
    destruct (_ <? _). reflexivity. apply A, B.
  Qed.

  (* A store inside the window doesn't matter. *)
  Lemma agree_setwin:
    forall M1 M2 L a v, 0 < L -> L <= 2^64 -> len <= 2^64 -> msub 64 a lo + L <= len ->
    agree lo len M1 M2 -> agree lo len (setmem 64 LittleE L M1 a v) M2.
  Proof.
    intros M1 M2 L a v L0 LL LN W A b B. rewrite byte_setmem_cases by assumption.
    destruct (N.ltb_spec (msub 64 b a) L) as [I|I].
      exfalso. apply B. unfold inwin, msub in *. change (2^64) with 18446744073709551616 in *. lia.
      apply A, B.
  Qed.

  (* Reading a string through memory M that agrees with m outside the frame,
     where m's copy of the string lies outside the frame: M's bytes up to the
     first NUL (in M) are m's. *)
  Lemma prefix_eq:
    forall M m p, agree lo len M m -> strfree lo len m p ->
    forall k, (forall j, j < k -> M Ⓑ[p ⊕ j] <> 0) ->
    forall j, j <= k -> M Ⓑ[p ⊕ j] = m Ⓑ[p ⊕ j].
  Proof.
    intros M m p A SF k. induction k as [|k IH] using N.peano_ind; intros NZ j J.
    - assert (j = 0) by lia. subst j. apply A, SF. intros i I. lia.
    - destruct (N.eq_dec j (N.succ k)) as [E|E].
      + subst j. apply A, SF. intros i I. rewrite <- IH; [apply NZ; lia | |lia].
        intros i' I'. apply NZ. lia.
      + apply IH; [|lia]. intros i I. apply NZ. lia.
  Qed.

  Lemma inset_to_m:
    forall M m r c, agree lo len M m -> strfree lo len m r -> inset M r c -> inset m r c.
  Proof.
    intros M m r c A SF [j [J P]]. exists j.
    assert (EQ: forall i, i <= j -> M Ⓑ[r ⊕ i] = m Ⓑ[r ⊕ i]) by (apply (prefix_eq M m r A SF j P)).
    split. rewrite <- EQ by lia. exact J.
    intros k K. rewrite <- EQ by lia. apply P, K.
  Qed.

  Lemma inset_to_M:
    forall M m r c, agree lo len M m -> strfree lo len m r -> inset m r c -> inset M r c.
  Proof.
    intros M m r c A SF [j [J P]]. exists j.
    assert (EQ: forall i, i <= j -> M Ⓑ[r ⊕ i] = m Ⓑ[r ⊕ i]).
      intros i I. apply A, SF. intros k K. apply P. lia.
    split. rewrite EQ by lia. exact J.
    intros k K. rewrite EQ by lia. apply P, K.
  Qed.

  Lemma cspn_agree:
    forall M m s r n, agree lo len M m -> strfree lo len m s -> strfree lo len m r ->
    cspn M s r n -> cspn m s r n.
  Proof.
    intros M m s r n A SS SR [PRE END].
    assert (EQ: forall j, j <= n -> M Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j]).
      apply (prefix_eq M m s A SS n). intros j J. apply PRE, J.
    split.
    - intros k K. rewrite <- EQ by lia. destruct (PRE k K) as [NZ NI]. split. exact NZ.
      intro I. apply NI. eapply inset_to_M; eassumption.
    - rewrite <- EQ by lia. destruct END as [Z|I]. left; exact Z.
      right. eapply inset_to_m; eassumption.
  Qed.

  Lemma spn_agree:
    forall M m s r n, agree lo len M m -> strfree lo len m s -> strfree lo len m r ->
    spn M s r n -> spn m s r n.
  Proof.
    intros M m s r n A SS SR [PRE END].
    assert (EQ: forall j, j <= n -> M Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j]).
      apply (prefix_eq M m s A SS n). intros j J. apply PRE, J.
    split.
    - intros k K. rewrite <- EQ by lia. destruct (PRE k K) as [NZ I]. split. exact NZ.
      eapply inset_to_m; eassumption.
    - rewrite <- EQ by lia. intros [NZ I]. apply END. split. exact NZ.
      eapply inset_to_M; eassumption.
  Qed.

  Lemma slen_agree:
    forall M m s n, agree lo len M m -> strfree lo len m s -> slen M s n -> slen m s n.
  Proof.
    intros M m s n A SS [PRE END].
    assert (EQ: forall j, j <= n -> M Ⓑ[s ⊕ j] = m Ⓑ[s ⊕ j]) by exact (prefix_eq M m s A SS n PRE).
    split. intros k K. rewrite <- EQ by lia. apply PRE, K.
    rewrite <- EQ by lia. exact END.
  Qed.

  (* The byte that stopped the scan (the n-th) lies outside the frame. *)
  Lemma cspn_end_free:
    forall m s r n, strfree lo len m s -> cspn m s r n -> ~ inwin lo len (s ⊕ n).
  Proof. intros m s r n SF [PRE _]. apply SF. intros j J. apply PRE, J. Qed.

  Lemma spn_end_free:
    forall m s r n, strfree lo len m s -> spn m s r n -> ~ inwin lo len (s ⊕ n).
  Proof. intros m s r n SF [PRE _]. apply SF. intros j J. apply PRE, J. Qed.
End Agree.
