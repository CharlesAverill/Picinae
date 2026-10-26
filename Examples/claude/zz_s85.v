Require Import Picinae_amd64.
Require Import memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Require Import amd64_memcpy_sets.
Require Import amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_loops_proof.
Require Import amd64_memmove_avx_rep_proof.
Require Import amd64_memmove_avx_nt_proof.
Open Scope N.

Lemma cpy_store16:
  forall m M d s n (W:N->Prop) o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16
         a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16,
  cpy m M d s W -> (forall i, W i -> i < n) -> nov d s n -> n < 2^64 ->
  o1 + 32 <= n -> o2 + 32 <= n -> o3 + 32 <= n -> o4 + 32 <= n -> o5 + 32 <= n -> o6 + 32 <= n -> o7 + 32 <= n -> o8 + 32 <= n -> o9 + 32 <= n -> o10 + 32 <= n -> o11 + 32 <= n -> o12 + 32 <= n -> o13 + 32 <= n -> o14 + 32 <= n -> o15 + 32 <= n -> o16 + 32 <= n ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 -> a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 -> a5 mod 2^64 = (d + o5) mod 2^64 -> a6 mod 2^64 = (d + o6) mod 2^64 -> a7 mod 2^64 = (d + o7) mod 2^64 -> a8 mod 2^64 = (d + o8) mod 2^64 -> a9 mod 2^64 = (d + o9) mod 2^64 -> a10 mod 2^64 = (d + o10) mod 2^64 -> a11 mod 2^64 = (d + o11) mod 2^64 -> a12 mod 2^64 = (d + o12) mod 2^64 -> a13 mod 2^64 = (d + o13) mod 2^64 -> a14 mod 2^64 = (d + o14) mod 2^64 -> a15 mod 2^64 = (d + o15) mod 2^64 -> a16 mod 2^64 = (d + o16) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 -> b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 -> b5 mod 2^64 = (s + o5) mod 2^64 -> b6 mod 2^64 = (s + o6) mod 2^64 -> b7 mod 2^64 = (s + o7) mod 2^64 -> b8 mod 2^64 = (s + o8) mod 2^64 -> b9 mod 2^64 = (s + o9) mod 2^64 -> b10 mod 2^64 = (s + o10) mod 2^64 -> b11 mod 2^64 = (s + o11) mod 2^64 -> b12 mod 2^64 = (s + o12) mod 2^64 -> b13 mod 2^64 = (s + o13) mod 2^64 -> b14 mod 2^64 = (s + o14) mod 2^64 -> b15 mod 2^64 = (s + o15) mod 2^64 -> b16 mod 2^64 = (s + o16) mod 2^64 ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (M) a1 (M Ⓨ[b1])) a2 (M Ⓨ[b2])) a3 (M Ⓨ[b3])) a4 (M Ⓨ[b4])) a5 (M Ⓨ[b5])) a6 (M Ⓨ[b6])) a7 (M Ⓨ[b7])) a8 (M Ⓨ[b8])) a9 (M Ⓨ[b9])) a10 (M Ⓨ[b10])) a11 (M Ⓨ[b11])) a12 (M Ⓨ[b12])) a13 (M Ⓨ[b13])) a14 (M Ⓨ[b14])) a15 (M Ⓨ[b15])) a16 (M Ⓨ[b16])) d s
      (fun i => W i \/ o1 <= i < o1 + 32 \/ o2 <= i < o2 + 32 \/ o3 <= i < o3 + 32 \/ o4 <= i < o4 + 32 \/ o5 <= i < o5 + 32 \/ o6 <= i < o6 + 32 \/ o7 <= i < o7 + 32 \/ o8 <= i < o8 + 32 \/ o9 <= i < o9 + 32 \/ o10 <= i < o10 + 32 \/ o11 <= i < o11 + 32 \/ o12 <= i < o12 + 32 \/ o13 <= i < o13 + 32 \/ o14 <= i < o14 + 32 \/ o15 <= i < o15 + 32 \/ o16 <= i < o16 + 32).
Proof.
  intros m M d s n W o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 o15 o16 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
         C WN NOV NB O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16.
  rewrite (cpy_load m M d s W n o1 32 b1 C WN NOV O1 B1).
  rewrite (cpy_load m M d s W n o2 32 b2 C WN NOV O2 B2).
  rewrite (cpy_load m M d s W n o3 32 b3 C WN NOV O3 B3).
  rewrite (cpy_load m M d s W n o4 32 b4 C WN NOV O4 B4).
  rewrite (cpy_load m M d s W n o5 32 b5 C WN NOV O5 B5).
  rewrite (cpy_load m M d s W n o6 32 b6 C WN NOV O6 B6).
  rewrite (cpy_load m M d s W n o7 32 b7 C WN NOV O7 B7).
  rewrite (cpy_load m M d s W n o8 32 b8 C WN NOV O8 B8).
  rewrite (cpy_load m M d s W n o9 32 b9 C WN NOV O9 B9).
  rewrite (cpy_load m M d s W n o10 32 b10 C WN NOV O10 B10).
  rewrite (cpy_load m M d s W n o11 32 b11 C WN NOV O11 B11).
  rewrite (cpy_load m M d s W n o12 32 b12 C WN NOV O12 B12).
  rewrite (cpy_load m M d s W n o13 32 b13 C WN NOV O13 B13).
  rewrite (cpy_load m M d s W n o14 32 b14 C WN NOV O14 B14).
  rewrite (cpy_load m M d s W n o15 32 b15 C WN NOV O15 B15).
  rewrite (cpy_load m M d s W n o16 32 b16 C WN NOV O16 B16).
  assert (C16: cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (M) a1 (getmem 64 LittleE 32 m b1)) a2 (getmem 64 LittleE 32 m b2)) a3 (getmem 64 LittleE 32 m b3)) a4 (getmem 64 LittleE 32 m b4)) a5 (getmem 64 LittleE 32 m b5)) a6 (getmem 64 LittleE 32 m b6)) a7 (getmem 64 LittleE 32 m b7)) a8 (getmem 64 LittleE 32 m b8)) a9 (getmem 64 LittleE 32 m b9)) a10 (getmem 64 LittleE 32 m b10)) a11 (getmem 64 LittleE 32 m b11)) a12 (getmem 64 LittleE 32 m b12)) a13 (getmem 64 LittleE 32 m b13)) a14 (getmem 64 LittleE 32 m b14)) a15 (getmem 64 LittleE 32 m b15)) a16 (getmem 64 LittleE 32 m b16)) d s (fun i => ((((((((((((((((W i \/ o1 <= i < o1 + 32) \/ o2 <= i < o2 + 32) \/ o3 <= i < o3 + 32) \/ o4 <= i < o4 + 32) \/ o5 <= i < o5 + 32) \/ o6 <= i < o6 + 32) \/ o7 <= i < o7 + 32) \/ o8 <= i < o8 + 32) \/ o9 <= i < o9 + 32) \/ o10 <= i < o10 + 32) \/ o11 <= i < o11 + 32) \/ o12 <= i < o12 + 32) \/ o13 <= i < o13 + 32) \/ o14 <= i < o14 + 32) \/ o15 <= i < o15 + 32) \/ o16 <= i < o16 + 32))).
  { repeat (apply cpy_store; [|try assumption..]); [exact C| ..].
    all: try (intros i Hi; clear - Hi WN NB O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16;
              change (2^64) with 18446744073709551616 in *;
              repeat destruct Hi as [Hi|Hi]; try apply WN in Hi; lia).
    all: try (clear; lia).
    all: clear - NB O1 O2 O3 O4 O5 O6 O7 O8 O9 O10 O11 O12 O13 O14 O15 O16; change (2^64) with 18446744073709551616 in *; lia. }
  eapply cpy_equiv; [|exact C16]. intro i. tauto.
Qed.


Lemma seg1285 : forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists j i, j < nk 14 d n /\ i < 32 /\
   cpy m (s1 V_MEM64) d s (done4 d j i) /\
   s1 R_RDI = d + aA d + 16384 * j + 128 * i /\
   s1 R_RSI = (s + (aA d + 16384 * j + 128 * i)) mod 2^64 /\
   s1 R_RCX = 32 - i /\ s1 R_R10 = nk 14 d n - j /\ s1 R_RDX = nr 14 d n /\
   s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1285, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [j [i [J [I [C [RDI [RSI [RCX [R10 [RDX [RAX RSP]]]]]]]]]]].
  assert (CKB: 16384 * nk 14 d n <= n - aA d).
  { unfold nk. change 16384 with (2^14). apply N.mul_div_le. discriminate. }
  pose proof (aA_bounds d) as AAB.
  assert (LE: aA d + 16384 * j + 128 * i + 12416 <= n)
    by (clear - J I CKB AAB NB; nia).
  repeat x64_step.
  all: change (2^14) with 16384 in *; change (2^13) with 8192 in *; change (2^12) with 4096 in *; change (2^7) with 128 in *.
  all: assert (ADV: cpy m
    (s1 V_MEM64
     [Ⓨ d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ s + aA d + 16384*j + 128*i ]]
     [Ⓨ 32 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 32 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 64 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 64 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 96 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 96 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 4096 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 4096 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 4128 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 4128 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 4160 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 4160 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 4192 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 4192 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 8192 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 8192 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 8224 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 8224 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 8256 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 8256 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 8288 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 8288 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 12288 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 12288 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 12320 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 12320 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 12352 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 12352 + s + aA d + 16384*j + 128*i ]]
     [Ⓨ 12384 + d + aA d + 16384*j + 128*i := s1 V_MEM64 Ⓨ[ 12384 + s + aA d + 16384*j + 128*i ]])
    d s (done4 d j (N.succ i))).
  { eapply cpy_equiv; cycle 1.
    { eapply (cpy_store16 m (s1 V_MEM64) d s n (done4 d j i)
        (aA d + 16384*j + 128*i) (32 + (aA d + 16384*j + 128*i))
        (64 + (aA d + 16384*j + 128*i)) (96 + (aA d + 16384*j + 128*i))
        (4096 + (aA d + 16384*j + 128*i)) (4128 + (aA d + 16384*j + 128*i))
        (4160 + (aA d + 16384*j + 128*i)) (4192 + (aA d + 16384*j + 128*i))
        (8192 + (aA d + 16384*j + 128*i)) (8224 + (aA d + 16384*j + 128*i))
        (8256 + (aA d + 16384*j + 128*i)) (8288 + (aA d + 16384*j + 128*i))
        (12288 + (aA d + 16384*j + 128*i)) (12320 + (aA d + 16384*j + 128*i))
        (12352 + (aA d + 16384*j + 128*i)) (12384 + (aA d + 16384*j + 128*i)));
      first [ exact C | exact NOV | exact NB
            | (intros ii Hii; unfold done4 in Hii; clear - Hii LE CKB AAB J I NB;
               change (2^64) with 18446744073709551616 in *; repeat destruct Hii as [Hii|Hii]; nia)
            | (clear - LE; change (2^64) with 18446744073709551616 in *; lia)
            | (clear; change (2^64) with 18446744073709551616; f_equal; lia) ]. }
    intro x. unfold done4. clear - AAB.
    split; intro H; repeat destruct H as [H|H]; lia. }
  all: (lazymatch goal with
       | |- cpy _ _ _ _ (done4 _ _ (N.succ _)) => idtac "SIG=bareADV"
       | |- cpy _ _ _ _ _ => idtac "SIG=bareCPYother"
       | |- exists _ _, _ => idtac "SIG=exists"
       | |- _ /\ _ => idtac "SIG=conj"
       | |- ?g => idtac "SIG=other" end).
  all: admit.
Admitted.
