(* Unfinished: field-level corollary for amd64_seed48_proof.v (slow nov tactic). *)
(* Non-overlap side conditions: concrete offsets into D are decided by
   arithmetic; anything involving seed16v or the stack comes from hypotheses. *)
Ltac nov :=
  first
  [ assumption
  | apply noverlap_sym; assumption
  | intros [i [j [I [J E]]]]; unfold D in *; change (2^64) with 18446744073709551616 in E; lia
  | apply (noverlap_sub _ 6); [assumption|lia]
  | apply noverlap_sym, (noverlap_sub _ 6); [assumption|lia]
  | apply (noverlap_sub0 _ 6); [assumption|lia]
  | apply noverlap_sym, (noverlap_sub0 _ 6); [assumption|lia]
  | apply noverlap_sym, (noverlap_sub _ 6), noverlap_sym; [apply (noverlap_sub _ 24); [assumption|lia]|lia]
  | apply (noverlap_sub _ 6), noverlap_sym, (noverlap_sub _ 24), noverlap_sym; [assumption|lia|lia]
  | apply (noverlap_sub0 _ 6), noverlap_sym, (noverlap_sub _ 24), noverlap_sym; [assumption|lia|lia]
  | apply noverlap_sym, (noverlap_sub0 _ 6), noverlap_sym, (noverlap_sub _ 24); [assumption|lia|lia]
  | apply (noverlap_sub _ 24); [assumption|lia]
  | apply noverlap_sym, (noverlap_sub _ 24); [assumption|lia]
  | apply (noverlap_sub0 _ 24); [assumption|lia]
  | apply noverlap_sym, (noverlap_sub0 _ 24); [assumption|lia] ].

(* The man page's effect, when seed16v doesn't overlap D or the stack slot. *)
Theorem seed48_effect:
  forall (mem:memory) sp seed r,
  ~ overlap 64 D 24 (sp ⊖ 16) 8 -> ~ overlap 64 seed 6 D 24 -> ~ overlap 64 seed 6 (sp ⊖ 16) 8 ->
  let m' := seed48r_mem (mem [Ⓠ sp ⊖ 16 := r]) seed D in
  (* Xi = seed16v *)
  m' Ⓦ[D] = mem Ⓦ[seed] /\ m' Ⓦ[D ⊕ 2] = mem Ⓦ[seed ⊕ 2] /\ m' Ⓦ[D ⊕ 4] = mem Ⓦ[seed ⊕ 4] /\
  (* old_x = previous Xi *)
  m' Ⓓ[D ⊕ 6] = mem Ⓓ[D] /\ m' Ⓦ[D ⊕ 10] = mem Ⓦ[D ⊕ 4] /\
  (* c = 0xB (with __init = 1 in the next 2 bytes) and a = 0x5DEECE66D *)
  m' Ⓓ[D ⊕ 12] = 0x1000b /\ m' Ⓠ[D ⊕ 16] = 0x5deece66d.
Proof.
  intros mem sp seed r NO NS NSS m'. subst m'. unfold seed48r_mem. cbv zeta.
  repeat split;
  repeat match goal with
    | |- context [getmem ?w ?e ?l (setmem ?w ?e ?l ?m ?a ?v) ?a] =>
        rewrite (getmem_setmem w e l m a v) by discriminate
    | |- context [getmem ?w ?e1 ?l1 (setmem ?w ?e2 ?l2 ?m ?a2 ?v) ?a1] =>
        rewrite (getmem_noverlap w e1 e2 l1 l2 m a1 a2 v) by nov
    end;
  rewrite ?N.mod_small by apply getmem_bound; reflexivity.
Qed.
