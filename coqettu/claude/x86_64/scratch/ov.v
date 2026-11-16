Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.
Lemma str_frame_off:
  forall p k L rsp, k <= L -> rsp < 2^64 -> ~ overlap 64 p (L + 1) (rsp ⊖ 48) 48 ->
  32 <= msub 64 (p ⊕ k) (msub 64 (msub 64 rsp 16) 32).
Proof.
  intros p k L rsp KL RB NOV.
  assert (E: msub 64 (msub 64 rsp 16) 32 = msub 64 rsp 48).
  { unfold msub. change (2^64) with 18446744073709551616 in *. lia. }
  rewrite E. assert (BB: msub 64 rsp 48 < 2^64) by apply (msub_lt 64). set (b := msub 64 rsp 48) in *. clearbody b.
  destruct (N.le_gt_cases 48 (msub 64 (p ⊕ k) b)) as [D|D]. lia. exfalso.
  apply NOV. exists k, (msub 64 (p ⊕ k) b). split. lia. split. exact D.
  unfold msub. change (2^64) with 18446744073709551616 in *. lia.
Qed.
