(* The musl x86_64 jmp_buf layout and lemmas about writing and reading it.

   musl's __jmp_buf on x86_64 is eight quadwords:
     [0] rbx  [8] rbp  [16] r12  [24] r13  [32] r14  [40] r15
     [48] the caller's stack pointer after setjmp returns (rsp + 8)
     [56] setjmp's return address

   Model:   Written by Claude Opus 5.5 (claude-opus-5-5), an AI model by
            Anthropic, and machine-checked by Rocq. *)

Require Import Picinae_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia.
Open Scope N.

Definition jmpbuf_write (m:N) (env rbx rbp r12 r13 r14 r15 sp pc:N) : N :=
  m [Ⓠenv := rbx] [Ⓠ8 + env := rbp] [Ⓠ16 + env := r12] [Ⓠ24 + env := r13]
    [Ⓠ32 + env := r14] [Ⓠ40 + env := r15] [Ⓠ48 + env := sp] [Ⓠ56 + env := pc].

Definition jmpbuf_holds (m:N) (env rbx rbp r12 r13 r14 r15 sp pc:N) :=
  m Ⓠ[env] = rbx /\ m Ⓠ[8 + env] = rbp /\ m Ⓠ[16 + env] = r12 /\
  m Ⓠ[24 + env] = r13 /\ m Ⓠ[32 + env] = r14 /\ m Ⓠ[40 + env] = r15 /\
  m Ⓠ[48 + env] = sp /\ m Ⓠ[56 + env] = pc.

(* Linear arithmetic modulo 2^64. *)
Ltac mod64_lia :=
  unfold msub in *; change (2^64) with 18446744073709551616 in *; lia.

(* Two 8-byte cells at offsets i, j of the same base are disjoint when the
   offsets are 8 apart and small. *)
Lemma noverlap_off8:
  forall e i j, i + 8 <= j \/ j + 8 <= i -> i < 2^63 -> j < 2^63 ->
  ~ overlap 64 (i + e) 8 (j + e) 8.
Proof.
  intros e i j D I J [x [y [X [Y E]]]]. mod64_lia.
Qed.

Lemma getmem8_setmem8_off:
  forall m e i j v, i + 8 <= j \/ j + 8 <= i -> i < 2^63 -> j < 2^63 ->
  (setmem 64 LittleE 8 m (j + e) v) Ⓠ[i + e] = m Ⓠ[i + e].
Proof. intros. apply getmem_noverlap, noverlap_off8; assumption. Qed.

Lemma getmem8_setmem8_off0:
  forall m e j v, 8 <= j -> j < 2^63 ->
  (setmem 64 LittleE 8 m (j + e) v) Ⓠ[e] = m Ⓠ[e].
Proof. intros. apply (getmem8_setmem8_off m e 0 j v); lia. Qed.

Lemma getmem8_setmem8_0off:
  forall m e i v, 8 <= i -> i < 2^63 ->
  (setmem 64 LittleE 8 m e v) Ⓠ[i + e] = m Ⓠ[i + e].
Proof. intros. apply (getmem8_setmem8_off m e i 0 v); lia. Qed.

Lemma getmem8_setmem8_same:
  forall m a v, v < 2^64 -> (setmem 64 LittleE 8 m a v) Ⓠ[a] = v.
Proof. intros. rewrite getmem_setmem by discriminate. apply N.mod_small. exact H. Qed.

Ltac jb_read :=
  repeat first
  [ rewrite getmem8_setmem8_same by assumption
  | rewrite getmem8_setmem8_off by lia
  | rewrite getmem8_setmem8_off0 by lia
  | rewrite getmem8_setmem8_0off by lia ].

(* Reading back a freshly written jmp_buf. *)
Theorem jmpbuf_write_holds:
  forall m env rbx rbp r12 r13 r14 r15 sp pc,
  rbx < 2^64 -> rbp < 2^64 -> r12 < 2^64 -> r13 < 2^64 -> r14 < 2^64 ->
  r15 < 2^64 -> sp < 2^64 -> pc < 2^64 ->
  jmpbuf_holds (jmpbuf_write m env rbx rbp r12 r13 r14 r15 sp pc)
               env rbx rbp r12 r13 r14 r15 sp pc.
Proof.
  intros. unfold jmpbuf_write, jmpbuf_holds.
  repeat split; jb_read; reflexivity.
Qed.

(* Writing a jmp_buf changes no byte outside [env, env+64). *)
Theorem jmpbuf_write_frame:
  forall m env rbx rbp r12 r13 r14 r15 sp pc a, 64 <= msub 64 a env ->
  (jmpbuf_write m env rbx rbp r12 r13 r14 r15 sp pc) Ⓑ[a] = m Ⓑ[a].
Proof.
  intros. unfold jmpbuf_write.
  repeat (rewrite getmem_noverlap; [|intros [x [y [X [Y E]]]]; mod64_lia]).
  reflexivity.
Qed.

(* A jmp_buf survives any memory change outside its 64 bytes. *)
Theorem jmpbuf_holds_frame:
  forall m m' env rbx rbp r12 r13 r14 r15 sp pc,
  (forall a, msub 64 a env < 64 -> m' Ⓑ[a] = m Ⓑ[a]) ->
  jmpbuf_holds m env rbx rbp r12 r13 r14 r15 sp pc ->
  jmpbuf_holds m' env rbx rbp r12 r13 r14 r15 sp pc.
Proof.
  intros m m' env rbx rbp r12 r13 r14 r15 sp pc FR H.
  assert (G: forall k, k <= 56 -> m' Ⓠ[k + env] = m Ⓠ[k + env]).
  { intros k K. apply getmem_frame_mem. intros a' A'.
    rewrite <- !getmem_1 with (e:=LittleE). apply FR. mod64_lia. }
  unfold jmpbuf_holds in *.
  rewrite <- (N.add_0_l env) at 1. rewrite G by lia. rewrite N.add_0_l.
  rewrite !G by lia. exact H.
Qed.

(* A read of [a, a+8) is unaffected by the jmp_buf writes when the two ranges
   are disjoint (used for setjmp's read of its own return address). *)
Theorem jmpbuf_write_read_frame:
  forall m env rbx rbp r12 r13 r14 r15 sp pc a len,
  ~ overlap 64 a len env 64 ->
  getmem 64 LittleE len (jmpbuf_write m env rbx rbp r12 r13 r14 r15 sp pc) a =
  getmem 64 LittleE len m a.
Proof.
  intros m env rbx rbp r12 r13 r14 r15 sp pc a len NO. unfold jmpbuf_write.
  repeat (rewrite getmem_noverlap;
    [|intros [x [y [X [Y E]]]]; apply NO;
      lazymatch type of E with
      | _ = (?k + env + y) mod _ => exists x, (k + y); repeat split; [assumption|lia|rewrite E; f_equal; lia]
      | _ = (env + y) mod _ => exists x, y; repeat split; [assumption|lia|assumption]
      end]).
  reflexivity.
Qed.

Lemma jmpbuf_write_sp_mod:
  forall m env rbx rbp r12 r13 r14 r15 sp pc,
  jmpbuf_write m env rbx rbp r12 r13 r14 r15 (sp mod 2^64) pc =
  jmpbuf_write m env rbx rbp r12 r13 r14 r15 sp pc.
Proof.
  intros. unfold jmpbuf_write. change (sp mod 2^64) with (sp mod 2^(8*8)).
  rewrite setmem_mod_r. reflexivity.
Qed.
