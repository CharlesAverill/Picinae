(* Four frozen-source byte stores equal one little-endian word store. *)
Require Import Picinae_i386.
From Picinae.coqettu.codex.x86 Require Import i386_byte_copy.
From Stdlib Require Import NArith Lia.
Open Scope N.
Lemma copy_bytes_four:forall source q p k m,
  setmem 32 LittleE 4 (copy_bytes source q p k m) (p+k) (getmem 32 LittleE 4 source (q+k))=
  copy_bytes source q p (k+4) m.
Proof.
  intros source q p k m.
  replace (k+4) with (((k+1)+1)+1+1) by lia. rewrite !copy_bytes_succ.
  change 4 with (1+3) at 1. rewrite setmem_split. cbn beta iota.
  change 3 with (1+2) at 1. rewrite setmem_split. cbn beta iota.
  change 2 with (1+1) at 1. rewrite setmem_split. cbn beta iota.
  rewrite !shiftr_getmem.
  rewrite !getmem_mod.
  cbn [N.min N.sub].
  replace (p+k+1) with (p+(k+1)) by lia.
  replace (p+(k+1)+1) with (p+(k+1+1)) by lia.
  replace (p+(k+1+1)+1) with (p+(k+1+1+1)) by lia.
  replace (q+k+1) with (q+(k+1)) by lia.
  replace (q+(k+1)+1) with (q+(k+1+1)) by lia.
  replace (q+(k+1+1)+1) with (q+(k+1+1+1)) by lia.
  reflexivity.
Qed.
