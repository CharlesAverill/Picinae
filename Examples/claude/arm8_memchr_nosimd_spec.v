(* __memchr_nosimd: specification and frame support for the unchanged e30 map.
   Initial author: OpenAI gpt-6-astra, xhigh/default, 2026-11-03.
   This file does not assert functional correctness of the lifted program.
   Provenance and intended scope: arm8_memchr_nosimd_proof.v. *)
Require Import Picinae_armv8 e30___memchr_nosimd_arm8.
From Stdlib Require Import NArith Lia List.
Import ARM8Notations ListNotations.
Open Scope N.

Definition mc_lo (a:N) := 16 * (a / 16).
Definition mc_hi (a n:N) := 16 * ((a+n+15) / 16).
Definition mc_byte (m a i:N) := getmem 64 LittleE 1 m (a ⊕ i).
Definition mc_prefix (m a c k:N) :=
  forall i, i < k -> mc_byte m a i <> c mod 256.
Definition mc_first (m a c n k:N) :=
  k < n /\ mc_byte m a k = c mod 256 /\ mc_prefix m a c k.
Definition mc_result (m a c n r:N) :=
  (r = 0 /\ mc_prefix m a c n) \/
  exists k, mc_first m a c n k /\ r = a ⊕ k.

(* n=0 has no readable-memory or non-null requirement. For n>0, non-null
   is necessary for the NULL-iff-no-hit characterization. The +15 bound is
   required by ADD X8,X7,#15 before alignment. n<2^63 makes CMP a,a+n / MI
   and the final candidate-vs-end MI test agree with the ordered interval. *)
Definition mc_domain (s:store) (a n:N) :=
  n = 0 \/
  (0 < a /\ n < 2^63 /\ a+n+15 < 2^64 /\
   forall b, mc_lo a <= b < mc_hi a n -> mem_readable s b).
Definition mc_saved : list arm8var :=
  [R_SP; R_X19; R_X20; R_X21; R_X22; R_X23; R_X24; R_X25;
   R_X26; R_X27; R_X28; R_X29; R_X30; R_LR;
   R_Z8; R_Z9; R_Z10; R_Z11; R_Z12; R_Z13; R_Z14; R_Z15;
   A_READ; A_WRITE].
Definition mc_frame (s0 s:store) :=
  s V_MEM64 = s0 V_MEM64 /\ forall v, In v mc_saved -> s v = s0 v.
Definition mc_input (s0:store) (a c n:N) (s:store) :=
  s R_X0 = a /\ s R_X1 = c /\ s R_X2 = n /\ mc_frame s0 s.
Definition mc_post (s0:store) (a c n:N) (s:store) :=
  mc_result (s0 V_MEM64) a c n (s R_X0) /\
  (s R_X0 = 0 <-> mc_prefix (s0 V_MEM64) a c n) /\ mc_frame s0 s.

Definition mc_ret_site (a:N) := (a =? 0x19c894) || (a =? 0x19c89c).
(* Only AFTER a real RET instruction, even if X30 aliases a map address. *)
Definition mc_exit (t:trace) : bool :=
  match t with _::(Addr a,_)::_ => mc_ret_site a | _ => false end.

Theorem mc_nwc : forall s2 s1,
  e30___memchr_nosimd_arm8 s1 = e30___memchr_nosimd_arm8 s2.
Proof. reflexivity. Qed.
Print Assumptions mc_nwc.
Theorem mc_welltyped : welltyped_prog arm8typctx e30___memchr_nosimd_arm8.
Proof. exact e30___memchr_nosimd_arm8.welltyped. Qed.
Print Assumptions mc_welltyped.
Theorem mc_preserves_memory : forall_endstates e30___memchr_nosimd_arm8
  (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof. apply noassign_prog_same. prove_noassign. Qed.
Print Assumptions mc_preserves_memory.
Theorem mc_preserves_saved : forall v, In v mc_saved ->
  forall_endstates e30___memchr_nosimd_arm8 (fun _ s _ s' => s v = s' v).
Proof.
  intros v IN. apply noassign_prog_same. unfold mc_saved in IN.
  repeat destruct IN as [<-|IN]; [prove_noassign..|destruct IN].
Qed.
Print Assumptions mc_preserves_saved.
Theorem mc_preserves_frame : forall_endstates e30___memchr_nosimd_arm8
  (fun _ s _ s' => mc_frame s s').
Proof.
  intros t x s x' s' XP ENTRY. split.
  - symmetry. exact (mc_preserves_memory t x s x' s' XP ENTRY).
  - intros v IN. symmetry. exact (mc_preserves_saved v IN t x s x' s' XP ENTRY).
Qed.
Print Assumptions mc_preserves_frame.

Lemma mc_frame_refl : forall s, mc_frame s s.
Proof. intros s. split; [reflexivity|intros; reflexivity]. Qed.
Print Assumptions mc_frame_refl.
Lemma mc_zero_result : forall m a c, mc_result m a c 0 0.
Proof. intros. left. split; [reflexivity|intros i I; exfalso; clear - I; lia]. Qed.
Print Assumptions mc_zero_result.
Lemma mc_null_iff : forall m a c n r,
  0 < a -> a+n < 2^64 -> mc_result m a c n r ->
  (r = 0 <-> mc_prefix m a c n).
Proof.
  intros m a c n r A END [[R P]|[k [[K [H P]] R]]].
  - subst r. split; intros; [exact P|reflexivity].
  - split.
    + intro Z. exfalso. rewrite R in Z.
      rewrite N.mod_small in Z by (clear - END K; lia).
      clear - A Z. lia.
    + intro NONE. exfalso. exact (NONE k K H).
Qed.
Print Assumptions mc_null_iff.

(* Symbolic permission mask; never evaluate the enormous N.ones value.
   All bytes of m, including both padding regions, are unconstrained. *)
Definition mc_witness (m a c n:N) : store :=
  update (update (update (update (update (fun _ => 0)
    A_READ (N.ones (2^64))) V_MEM64 m) R_X0 a) R_X1 c) R_X2 n.
Theorem mc_witness_typed : forall m a c n,
  m < 2^(8*2^64) -> a < 2^64 -> c < 2^64 -> n < 2^64 ->
  models arm8typctx (mc_witness m a c n).
Proof.
  intros m a c n M A C NN. unfold mc_witness.
  apply models_update; [exact NN|].
  apply models_update; [exact C|].
  apply models_update; [exact A|].
  apply models_update; [exact M|].
  apply models_update; [apply ones_bound|].
  intros v w T. apply mp2_gt_0.
Qed.
Print Assumptions mc_witness_typed.
Theorem mc_entry_inhabited : forall m a c n,
  m < 2^(8*2^64) -> a < 2^64 -> c < 2^64 -> n < 2^64 ->
  (n = 0 \/ (0 < a /\ n < 2^63 /\ a+n+15 < 2^64)) ->
  exists s, models arm8typctx s /\ mc_domain s a n /\ mc_input s a c n s.
Proof.
  intros m a c n M A C NN D. exists (mc_witness m a c n).
  split; [apply mc_witness_typed; assumption|]. split.
  - destruct D as [Z|[POS [SZ END]]].
    + left. exact Z.
    + right. split; [exact POS|]. split; [exact SZ|]. split; [exact END|].
      intros b B. unfold mem_readable, mc_witness.
      rewrite !update_frame by discriminate. rewrite update_updated.
      apply N.ones_spec_low.
      assert (HI: mc_hi a n <= a+n+15).
      { unfold mc_hi. pose proof (N.div_mod (a+n+15) 16 ltac:(discriminate)) as E.
        clear - E. lia. }
      clear - B HI END. lia.
  - unfold mc_input. split.
    + unfold mc_witness. rewrite !update_frame by discriminate.
      rewrite update_updated. reflexivity.
    + split.
      * unfold mc_witness. rewrite update_frame by discriminate.
        rewrite update_updated. reflexivity.
      * split.
        -- unfold mc_witness. rewrite update_updated. reflexivity.
        -- apply mc_frame_refl.
Qed.
Print Assumptions mc_entry_inhabited.

Theorem mc_zero_entry_inhabited : exists s,
  models arm8typctx s /\ mc_domain s 0 0 /\ mc_input s 0 0 0 s.
Proof.
  apply (mc_entry_inhabited 0 0 0 0); try apply mp2_gt_0.
  left. reflexivity.
Qed.
Print Assumptions mc_zero_entry_inhabited.

(* Every residue class mod16 has a positive, one-byte inhabited instance.
   This remains universally quantified over the contents and search byte. *)
Theorem mc_all_alignments_inhabited : forall m c r,
  m < 2^(8*2^64) -> c < 2^64 -> r < 16 ->
  exists s, models arm8typctx s /\ mc_domain s (16+r) 1 /\
            mc_input s (16+r) c 1 s.
(* PARTIAL: exact initial proof is preserved in notes/a-memchr-nosimd/. *)
Abort.
