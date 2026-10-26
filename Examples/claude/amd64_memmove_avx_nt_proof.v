(* memcpy via __memmove_avx_unaligned_erms, the non-temporal path
   (n >= __x86_rep_movsb_stop_threshold)

   This file continues amd64_memmove_avx_proof.v, amd64_memmove_avx_loops_proof.v
   and amd64_memmove_avx_rep_proof.v.  At or above the stop threshold (the
   quadword at 0x3215a0, by default the non-temporal threshold), the
   function copies very large buffers without polluting the caches:
   * it stores the first 64 source bytes (saved in YMM0/YMM1) at dest, then
     aligns the destination up to 64 bytes: with a = 64 - d mod 64 it continues
     at offset a with n - a bytes left;
   * it copies the bulk in chunks of two 4 KiB pages (8 KiB), or of four pages
     (16 KiB) when n/16 reaches the non-temporal threshold or when dest and
     src alias modulo 4 KiB.  Each inner iteration loads 128 bytes from each
     page of the chunk and stores them with VMOVNTDQ; 32 iterations finish a
     chunk;
   * it copies the rest (less than one chunk) with an aligned 128-byte loop,
     and finally stores the last 128 bytes from the end.
   The prefetches lift as no-ops, and VMOVNTDQ as an ordinary store (its
   non-temporal hint has no meaning in a sequential memory model).

   PRECONDITIONS (memcpy's contract and the sizes)
   * nov d s n: [d, d+n) and [s, s+n) do not overlap.
   * d + n < 2^64 and s + n <= 2^64 (dest does not reach the top of the
     address space; no real buffer does).
   * m[0x31a3f8] < n and m[0x3215a0] <= n: above the REP MOVSB threshold, at
     or above its stop threshold.
   * 16448 <= n: glibc never sets the non-temporal threshold below 0x4040, so
     this follows in a running process; it guarantees at least one whole
     chunk, so the chunk counter (decremented and tested at the bottom of the
     loop) does not wrap.

   OUTPUT: at the RET, RAX = d, RSP is unchanged, and copied m m' d s n.

   Model:   This specification and proof were written by Claude Opus 5.5
            (claude-opus-5-5), an AI model by Anthropic, and machine-checked by Rocq.
 *)

Require Import Picinae_amd64.
Require Import memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common.
Require Import amd64_memcpy_lemmas.
Require Import amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_loops_proof.
Require Import amd64_memmove_avx_rep_proof.
Open Scope N.

(* The bulk starts at offset aA d (the destination rounded up to 64 bytes),
   with n - aA d bytes left: k chunks of 2^c bytes and a rest. *)
Definition nk (c d n:N) := (n - aA d) / 2^c.
Definition nr (c d n:N) := (n - aA d) mod 2^c.

(* Offsets copied after j whole chunks of 2^c bytes and i inner iterations
   (i 128-byte rows of each of the pages of chunk j). *)
Definition done2 (d j i:N) (x:N) :=
  x < 64 \/ aA d <= x < aA d + 8192 * j \/
  aA d + 8192 * j <= x < aA d + 8192 * j + 128 * i \/
  aA d + 8192 * j + 4096 <= x < aA d + 8192 * j + 4096 + 128 * i.

Definition done4 (d j i:N) (x:N) :=
  x < 64 \/ aA d <= x < aA d + 16384 * j \/
  aA d + 16384 * j <= x < aA d + 16384 * j + 128 * i \/
  aA d + 16384 * j + 4096 <= x < aA d + 16384 * j + 4096 + 128 * i \/
  aA d + 16384 * j + 8192 <= x < aA d + 16384 * j + 8192 + 128 * i \/
  aA d + 16384 * j + 12288 <= x < aA d + 16384 * j + 12288 + 128 * i.

Lemma neg_add: forall d s, msub 64 0 d ⊕ s = msub 64 s d.
Proof.
  intros d s. unfold msub. rewrite N.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.

(* The overlap test of the non-temporal entry (JA: n > s - d) fails without
   overlap. *)
Lemma nt_no_overlap: forall n d s p, n <= msub 64 s d -> s < 2^64 ->
  ((if n <? msub 64 0 d ⊕ s then 1 else 0) .| (if n ⊕ d =? s then 1 else 0)) .^ 1 = N.pos p -> False.
Proof.
  intros n d s p SD SB H. apply ja_taken in H. destruct H as [H1 H2].
  apply N.ltb_ge in H1. apply N.eqb_neq in H2. rewrite neg_add in H1.
  assert (E: n = msub 64 s d) by lia. subst n. apply H2.
  rewrite N.add_comm, addmsub. apply N.mod_small, SB.
Qed.

(* Eight 32-byte stores of source pieces read from the current memory M. *)
Lemma cpy_store8:
  forall m M d s n (W:N->Prop) o1 o2 o3 o4 o5 o6 o7 o8
         a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8,
  cpy m M d s W -> (forall i, W i -> i < n) -> nov d s n -> n < 2^64 ->
  o1 + 32 <= n -> o2 + 32 <= n -> o3 + 32 <= n -> o4 + 32 <= n ->
  o5 + 32 <= n -> o6 + 32 <= n -> o7 + 32 <= n -> o8 + 32 <= n ->
  a1 mod 2^64 = (d + o1) mod 2^64 -> a2 mod 2^64 = (d + o2) mod 2^64 ->
  a3 mod 2^64 = (d + o3) mod 2^64 -> a4 mod 2^64 = (d + o4) mod 2^64 ->
  a5 mod 2^64 = (d + o5) mod 2^64 -> a6 mod 2^64 = (d + o6) mod 2^64 ->
  a7 mod 2^64 = (d + o7) mod 2^64 -> a8 mod 2^64 = (d + o8) mod 2^64 ->
  b1 mod 2^64 = (s + o1) mod 2^64 -> b2 mod 2^64 = (s + o2) mod 2^64 ->
  b3 mod 2^64 = (s + o3) mod 2^64 -> b4 mod 2^64 = (s + o4) mod 2^64 ->
  b5 mod 2^64 = (s + o5) mod 2^64 -> b6 mod 2^64 = (s + o6) mod 2^64 ->
  b7 mod 2^64 = (s + o7) mod 2^64 -> b8 mod 2^64 = (s + o8) mod 2^64 ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32
        (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (M Ⓨ[b1])) a2 (M Ⓨ[b2])) a3 (M Ⓨ[b3])) a4 (M Ⓨ[b4]))
          a5 (M Ⓨ[b5])) a6 (M Ⓨ[b6])) a7 (M Ⓨ[b7])) a8 (M Ⓨ[b8])) d s
      (fun i => W i \/ o1 <= i < o1 + 32 \/ o2 <= i < o2 + 32 \/ o3 <= i < o3 + 32 \/ o4 <= i < o4 + 32
                     \/ o5 <= i < o5 + 32 \/ o6 <= i < o6 + 32 \/ o7 <= i < o7 + 32 \/ o8 <= i < o8 + 32).
Proof.
  intros m M d s n W o1 o2 o3 o4 o5 o6 o7 o8 a1 a2 a3 a4 a5 a6 a7 a8 b1 b2 b3 b4 b5 b6 b7 b8
         C WN NOV NB O1 O2 O3 O4 O5 O6 O7 O8 A1 A2 A3 A4 A5 A6 A7 A8 B1 B2 B3 B4 B5 B6 B7 B8.
  rewrite (cpy_load m M d s W n o1 32 b1 C WN NOV O1 B1).
  rewrite (cpy_load m M d s W n o2 32 b2 C WN NOV O2 B2).
  rewrite (cpy_load m M d s W n o3 32 b3 C WN NOV O3 B3).
  rewrite (cpy_load m M d s W n o4 32 b4 C WN NOV O4 B4).
  rewrite (cpy_load m M d s W n o5 32 b5 C WN NOV O5 B5).
  rewrite (cpy_load m M d s W n o6 32 b6 C WN NOV O6 B6).
  rewrite (cpy_load m M d s W n o7 32 b7 C WN NOV O7 B7).
  rewrite (cpy_load m M d s W n o8 32 b8 C WN NOV O8 B8).
  assert (C8: cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32
        (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M
          a1 (getmem 64 LittleE 32 m b1)) a2 (getmem 64 LittleE 32 m b2)) a3 (getmem 64 LittleE 32 m b3))
          a4 (getmem 64 LittleE 32 m b4)) a5 (getmem 64 LittleE 32 m b5)) a6 (getmem 64 LittleE 32 m b6))
          a7 (getmem 64 LittleE 32 m b7)) a8 (getmem 64 LittleE 32 m b8)) d s
      (fun i => (((((((W i \/ o1 <= i < o1 + 32) \/ o2 <= i < o2 + 32) \/ o3 <= i < o3 + 32) \/ o4 <= i < o4 + 32)
                 \/ o5 <= i < o5 + 32) \/ o6 <= i < o6 + 32) \/ o7 <= i < o7 + 32) \/ o8 <= i < o8 + 32)).
  { repeat (apply cpy_store; [|try assumption..]); [exact C| ..].
    all: try (intros i Hi; clear - Hi WN NB O1 O2 O3 O4 O5 O6 O7 O8;
              change (2^64) with 18446744073709551616 in *;
              repeat destruct Hi as [Hi|Hi]; try apply WN in Hi; lia).
    all: try (clear; lia).
    all: clear - NB O1 O2 O3 O4 O5 O6 O7 O8; change (2^64) with 18446744073709551616 in *; lia. }
  eapply cpy_equiv; [|exact C8]. intro i. tauto.
Qed.

Definition nt_exit (t:trace) :=
  match t with (Addr a,_)::_ => match a with
  | 1261 | 1757 => true
  | _ => false
  end | _ => false end.

Definition nt_invs (m d s n rsp:N) (t:trace) :=
  match t with (Addr a,st)::_ => match a with
  | 0 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\ st R_RSP = rsp)
  | 704 => Some (st V_MEM64 = m /\ st R_RDI = d /\ st R_RSI = s /\ st R_RDX = n /\
                 st R_RSP = rsp /\ st R_RAX = d /\ st R_YMM0 = m Ⓨ[s])
  (* two-page chunks: inner loop head *)
  | 917 => Some (exists j i, j < nk 13 d n /\ i < 32 /\
                 cpy m (st V_MEM64) d s (done2 d j i) /\
                 st R_RDI = d + aA d + 8192 * j + 128 * i /\
                 st R_RSI = (s + (aA d + 8192 * j + 128 * i)) mod 2^64 /\
                 st R_RCX = 32 - i /\ st R_R10 = nk 13 d n - j /\ st R_RDX = nr 13 d n /\
                 st R_RAX = d /\ st R_RSP = rsp)
  (* all two-page chunks done *)
  | 1117 => Some (cpy m (st V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n) /\
                  st R_RDI = d + aA d + 8192 * nk 13 d n /\
                  st R_RSI = (s + (aA d + 8192 * nk 13 d n)) mod 2^64 /\
                  st R_RDX = nr 13 d n /\ st R_RAX = d /\ st R_RSP = rsp)
  (* two-page chunks done: the 128-byte tail loop *)
  | 1125 => Some (exists t, 128 * t + 128 < nr 13 d n /\
                 cpy m (st V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n + 128 * t) /\
                 st R_RDI = d + aA d + 8192 * nk 13 d n + 128 * t /\
                 st R_RSI = (s + (aA d + 8192 * nk 13 d n + 128 * t)) mod 2^64 /\
                 st R_RDX = nr 13 d n - 128 * t /\ st R_RAX = d /\ st R_RSP = rsp)
  (* two-page: final overlapping 128-byte copy entry *)
  | 1210 => Some (exists c, n - 128 <= c <= n /\
                 cpy m (st V_MEM64) d s (fun x => x < c) /\
                 st R_RDI = d + c /\ st R_RDX = n - c /\
                 st R_RSI = (s + c) mod 2^64 /\ st R_RAX = d /\ st R_RSP = rsp)
  (* four-page chunks: inner loop head *)
  | 1285 => Some (exists j i, j < nk 14 d n /\ i < 32 /\
                 cpy m (st V_MEM64) d s (done4 d j i) /\
                 st R_RDI = d + aA d + 16384 * j + 128 * i /\
                 st R_RSI = (s + (aA d + 16384 * j + 128 * i)) mod 2^64 /\
                 st R_RCX = 32 - i /\ st R_R10 = nk 14 d n - j /\ st R_RDX = nr 14 d n /\
                 st R_RAX = d /\ st R_RSP = rsp)
  | 1613 => Some (cpy m (st V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n) /\
                  st R_RDI = d + aA d + 16384 * nk 14 d n /\
                  st R_RSI = (s + (aA d + 16384 * nk 14 d n)) mod 2^64 /\
                  st R_RDX = nr 14 d n /\ st R_RAX = d /\ st R_RSP = rsp)
  | 1621 => Some (exists t, 128 * t + 128 < nr 14 d n /\
                 cpy m (st V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n + 128 * t) /\
                 st R_RDI = d + aA d + 16384 * nk 14 d n + 128 * t /\
                 st R_RSI = (s + (aA d + 16384 * nk 14 d n + 128 * t)) mod 2^64 /\
                 st R_RDX = nr 14 d n - 128 * t /\ st R_RAX = d /\ st R_RSP = rsp)
  (* four-page: final overlapping 128-byte copy entry *)
  | 1706 => Some (exists c, n - 128 <= c <= n /\
                 cpy m (st V_MEM64) d s (fun x => x < c) /\
                 st R_RDI = d + c /\ st R_RDX = n - c /\
                 st R_RSI = (s + c) mod 2^64 /\ st R_RAX = d /\ st R_RSP = rsp)
  | 1261 | 1757 => Some (postcondition m d s n rsp st)
  (* paths excluded by the preconditions or by non-overlap *)
  | 309 | 337 | 363 | 496 | 731 => Some False
  | _ => None
  end | _ => None end.



Lemma cpy_equiv': forall m m' d s (W W':N->Prop),
  cpy m m' d s W -> (forall i, W i <-> W' i) -> cpy m m' d s W'.
Proof. intros. eapply cpy_equiv; eassumption. Qed.

(* One two-page inner iteration advances the copied set from done2 d j i to
   done2 d j (i+1).  Stated over an abstract memory M so the eight-store term
   is built once; the call site applies it, unifying M with the real memory. *)
Lemma nt_adv2: forall m M d s n j i,
  cpy m M d s (done2 d j i) -> nov d s n -> n < 2^64 ->
  aA d + 2 ^ 13 * j + 2 ^ 7 * i + 4224 <= n ->
  cpy m (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 (setmem 64 LittleE 32 M (d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (32 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (32 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (64 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (64 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (96 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (96 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (2 ^ 12 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (2 ^ 12 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (4128 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (4128 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (4160 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (4160 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) (4192 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (getmem 64 LittleE 32 M (4192 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i))) d s (done2 d j (N.succ i)).
Proof.
  intros m M d s n j i C NOV NB LE.
  eapply cpy_equiv';
  [ eapply (cpy_store8 m M d s n (done2 d j i) (aA d + 2 ^ 13 * j + 2 ^ 7 * i) (32 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (64 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (96 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (4096 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (4128 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (4160 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (4192 + (aA d + 2 ^ 13 * j + 2 ^ 7 * i)) (d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (32 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (64 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (96 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (2 ^ 12 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4128 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4160 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4192 + d + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (32 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (64 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (96 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (2 ^ 12 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4128 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4160 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i) (4192 + s + aA d + 2 ^ 13 * j + 2 ^ 7 * i));
    first [ exact C | exact NOV | exact NB
          | (intros ii Hii; unfold done2 in Hii; change (2^13) with 8192 in *; change (2^7) with 128 in *;
             clear - Hii LE; lia)
          | (change (2^12) with 4096 in *; clear - LE; lia)
          | (clear; f_equal; lia) ]
  | intro x; unfold done2; change (2^12) with 4096; change (2^13) with 8192 in *; change (2^7) with 128 in *;
    rewrite N.mul_succ_r; clear; split; intro H; repeat destruct H as [H|H]; lia ].
Qed.

(* The final overlapping-copy store address d-k+c+(n-c) is offset n-k from d. *)
Lemma fcaddr: forall x c n k, k < 2^64 -> k <= n -> c <= n ->
  (x ⊖ k + c) ⊕ (n - c) = x ⊕ (n - k).
Proof.
  intros x c n k K2 KN CN. unfold msub.
  rewrite (N.mod_small k) by exact K2.
  rewrite <- N.add_assoc.
  rewrite N.add_mod_idemp_l by discriminate.
  replace (x + (2 ^ 64 - k) + (c + (n - c))) with ((x + (n - k)) + 1 * 2^64)
    by (change (2^64) with 18446744073709551616 in *; lia).
  rewrite N.mod_add by discriminate. reflexivity.
Qed.

(* The 32-bit SUB of 0x80 decrements the remaining byte count (when it fits). *)
Lemma reme: forall a, 128 <= a -> a < 2^32 -> msub 32 a 128 = a - 128.
Proof.
  intros a Ha Hb. unfold msub. change (128 mod 2^32) with 128.
  replace (a + (2 ^ 32 - 128)) with ((a - 128) + 1 * 2^32)
    by (change (2^32) with 4294967296 in *; lia).
  rewrite N.mod_add by discriminate. apply N.mod_small.
  change (2^32) with 4294967296 in *; lia.
Qed.

(* JBE / JA branch conditions, as lifted (CF .| ZF). *)
Lemma jbe_not: forall a b:bool,
  ((if a then 1 else 0) .| (if b then 1 else 0)) = 0 -> a = false /\ b = false.
Proof. intros [|] [|]; cbn; intro H; first [discriminate|tauto]. Qed.

Lemma jbe_taken: forall a b:bool, forall p,
  ((if a then 1 else 0) .| (if b then 1 else 0)) = N.pos p -> a = true \/ b = true.
Proof. intros [|] [|] p; cbn; intro H; first [discriminate|tauto]. Qed.

Lemma nt_seg_1117: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (cpy m (s1 V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n) /\
   s1 R_RDI = d + aA d + 8192 * nk 13 d n /\
   s1 R_RSI = (s + (aA d + 8192 * nk 13 d n)) mod 2^64 /\
   s1 R_RDX = nr 13 d n /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1117, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [C [RDI [RSI [RDX [RAX RSP]]]]].
  repeat x64_step.
  all: change (2^13) with 8192 in *; change (2^7) with 128 in *.
  all: pose proof (aA_bounds d) as AAB.
  all: assert (DVM: n - aA d = 8192 * nk 13 d n + nr 13 d n) by
    (unfold nk, nr; change 8192 with (2^13); apply N.div_mod; discriminate).
  all: assert (NRB: nr 13 d n < 8192) by (unfold nr; change 8192 with (2^13); apply N.mod_lt; discriminate).
  all: assert (ALE: aA d <= n) by (clear - AAB BIG; lia).
  all: assert (CE: aA d + 8192 * nk 13 d n = n - nr 13 d n) by (clear - DVM ALE NRB; lia).
  - (* fall-through: nr > 128, enter the 128-byte tail loop at 1125 (t=0) *)
    apply jbe_not in BC. destruct BC as [B1 B2].
    apply N.ltb_ge in B1. apply N.eqb_neq in B2.
    exists 0. rewrite !N.mul_0_r, !N.add_0_r, !N.sub_0_r.
    split. { clear - B1 B2; lia. }
    split. { exact C. }
    split. { exact RDI. }
    split. { exact RSI. }
    split. { reflexivity. }
    split. { exact RAX. } exact RSP.
  - (* taken: nr <= 128, go straight to the final overlapping copy at 1210 *)
    apply jbe_taken in BC.
    assert (NR32: nr 13 d n < 2^32) by (change (2^32) with 4294967296; clear - NRB; lia).
    assert (NRLE: nr 13 d n <= 128).
    { destruct BC as [B|B].
      - apply N.ltb_lt in B. rewrite N.mod_small in B by exact NR32. clear - B; lia.
      - apply N.eqb_eq in B. rewrite N.mod_small in B by exact NR32. clear - B; lia. }
    assert (NKB: 64 <= aA d + 8192 * nk 13 d n) by (clear - DVM BIG AAB NRB; lia).
    exists (aA d + 8192 * nk 13 d n).
    split. { rewrite CE. clear - NRLE NRB; lia. }
    split. { eapply cpy_equiv'; [exact C|]. intro x. clear - AAB NKB.
             split; intro H; [repeat destruct H as [H|H]; lia | lia]. }
    split. { rewrite RDI. clear; lia. }
    split. { rewrite CE. clear - NRB BIG; lia. }
    split. { exact RSI. }
    split. { exact RAX. } exact RSP.
Qed.

Lemma nt_seg_1125: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists t0, 128 * t0 + 128 < nr 13 d n /\
   cpy m (s1 V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n + 128 * t0) /\
   s1 R_RDI = d + aA d + 8192 * nk 13 d n + 128 * t0 /\
   s1 R_RSI = (s + (aA d + 8192 * nk 13 d n + 128 * t0)) mod 2^64 /\
   s1 R_RDX = nr 13 d n - 128 * t0 /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1125, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [t0 [TLT [C [RDI [RSI [RDX [RAX RSP]]]]]]].
  repeat x64_step.
  all: change (2^13) with 8192 in *; change (2^12) with 4096 in *; change (2^7) with 128 in *.
  all: pose proof (aA_bounds d) as AAB.
  all: assert (DVM: n - aA d = 8192 * nk 13 d n + nr 13 d n) by
    (unfold nk, nr; change 8192 with (2^13); apply N.div_mod; discriminate).
  all: assert (NRB: nr 13 d n < 8192) by (unfold nr; change 8192 with (2^13); apply N.mod_lt; discriminate).
  all: assert (CT: aA d + 8192 * nk 13 d n + 128 * t0 + 128 <= n) by (clear - DVM AAB TLT; lia).
  all: assert (REME: msub 32 (nr 13 d n - 128 * t0) 128 = nr 13 d n - 128 * (t0+1)) by
    (rewrite reme by (change (2^32) with 4294967296; clear - TLT NRB; lia);
     clear - TLT; lia).
  all: assert (ADV: cpy m
         (s1 V_MEM64
          [Ⓨ d + aA d + 8192 * nk 13 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ s + aA d + 8192 * nk 13 d n + 128 * t0 ]]
          [Ⓨ 32 + d + aA d + 8192 * nk 13 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 32 + s + aA d + 8192 * nk 13 d n + 128 * t0 ]]
          [Ⓨ 64 + d + aA d + 8192 * nk 13 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 64 + s + aA d + 8192 * nk 13 d n + 128 * t0 ]]
          [Ⓨ 96 + d + aA d + 8192 * nk 13 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 96 + s + aA d + 8192 * nk 13 d n + 128 * t0 ]])
         d s (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n + 128 * (t0+1)))
  by (eapply cpy_equiv; cycle 1;
      [ eapply (cpy_store4w m (s1 V_MEM64) d s n
          (fun x => x < 64 \/ aA d <= x < aA d + 8192 * nk 13 d n + 128 * t0)
          (aA d + 8192 * nk 13 d n + 128 * t0) (aA d + 8192 * nk 13 d n + 128 * t0 + 32)
          (aA d + 8192 * nk 13 d n + 128 * t0 + 64) (aA d + 8192 * nk 13 d n + 128 * t0 + 96));
        first [ exact C | exact NOV | exact NB
              | (intros i Hi; clear - Hi CT AAB; change (2^64) with 18446744073709551616 in *;
                 repeat destruct Hi as [Hi|Hi]; lia)
              | (clear - CT; change (2^64) with 18446744073709551616 in *; lia)
              | (clear; change (2^64) with 18446744073709551616; f_equal; lia) ]
      | (intro x; clear - AAB; split; intro H; repeat destruct H as [H|H]; lia) ]).
  2:{ (* continue: JA taken, remaining still > 128 *)
    apply ja_taken in BC. destruct BC as [B1 B2].
    apply N.ltb_ge in B1. apply N.eqb_neq in B2.
    rewrite REME in B1. rewrite (N.mod_small (nr 13 d n - 128 * t0)) in B2
      by (change (2^32) with 4294967296; clear - NRB; lia).
    exists (t0 + 1).
    split. { clear - B1 B2 TLT; lia. }
    split. { exact ADV. }
    split. { rewrite N.mod_small by (clear - CT NW; lia). clear; lia. }
    split. { change (?a ⊕ ?b) with ((a + b) mod 2^64). f_equal. clear; lia. }
    split. { exact REME. }
    split. { exact RAX. } exact RSP. }
  { (* exit: JA not taken, remaining <= 128 *)
    apply ja_not_taken in BC.
    assert (RLE: nr 13 d n - 128 * (t0+1) <= 128).
    { destruct BC as [B|B].
      - apply N.ltb_lt in B. rewrite REME in B. clear - B; lia.
      - apply N.eqb_eq in B. rewrite (N.mod_small (nr 13 d n - 128*t0)) in B
          by (change (2^32) with 4294967296; clear - NRB; lia).
        clear - B TLT; lia. }
    exists (aA d + 8192 * nk 13 d n + 128 * (t0+1)).
    split. { clear - DVM AAB RLE TLT NRB; lia. }
    split. { eapply cpy_equiv'; [exact ADV|]. intro x. clear - AAB CT.
             split; intro H; [repeat destruct H as [H|H]; lia | lia]. }
    split. { rewrite N.mod_small by (clear - CT NW; lia). clear; lia. }
    split. { rewrite REME. clear - DVM AAB; lia. }
    split. { change (?a ⊕ ?b) with ((a + b) mod 2^64). f_equal. clear; lia. }
    split. { exact RAX. } exact RSP. }
Qed.

Lemma nt_seg_1210: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists c, n - 128 <= c <= n /\
   cpy m (s1 V_MEM64) d s (fun x => x < c) /\
   s1 R_RDI = d + c /\ s1 R_RDX = n - c /\
   s1 R_RSI = (s + c) mod 2^64 /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1210, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [c [[CL CU] [C [RDI [RDX [RSI [RAX RSP]]]]]]].
  repeat x64_step.
  split; [assumption|]. split; [assumption|].
  eapply cpy_copied; cycle 1.
  { eapply (cpy_store4w m (s1 V_MEM64) d s n (fun x => x < c) (n-128) (n-96) (n-64) (n-32));
      [ exact C | | assumption | assumption | .. ].
    { intros i Hi. clear - Hi CU. lia. }
    all: try (clear - CL CU BIG; lia).
    all: change (2^7) with 128.
    all: rewrite fcaddr by (clear - CL CU BIG; try (change (2^64) with 18446744073709551616); lia).
    all: reflexivity. }
  intro i. clear - CL CU BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
Qed.

Lemma nt_seg_1285: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists j i, j < nk 14 d n /\ i < 32 /\
   cpy m (s1 V_MEM64) d s (done4 d j i) /\
   s1 R_RDI = d + aA d + 16384 * j + 128 * i /\
   s1 R_RSI = (s + (aA d + 16384 * j + 128 * i)) mod 2^64 /\
   s1 R_RCX = 32 - i /\ s1 R_R10 = nk 14 d n - j /\ s1 R_RDX = nr 14 d n /\
   s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1285, s1) :: t).
Proof. Admitted.

Lemma nt_seg_1613: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (cpy m (s1 V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n) /\
   s1 R_RDI = d + aA d + 16384 * nk 14 d n /\
   s1 R_RSI = (s + (aA d + 16384 * nk 14 d n)) mod 2^64 /\
   s1 R_RDX = nr 14 d n /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1613, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [C [RDI [RSI [RDX [RAX RSP]]]]].
  repeat x64_step.
  all: change (2^14) with 16384 in *; change (2^7) with 128 in *.
  all: pose proof (aA_bounds d) as AAB.
  all: assert (DVM: n - aA d = 16384 * nk 14 d n + nr 14 d n) by
    (unfold nk, nr; change 16384 with (2^14); apply N.div_mod; discriminate).
  all: assert (NRB: nr 14 d n < 16384) by (unfold nr; change 16384 with (2^14); apply N.mod_lt; discriminate).
  all: assert (ALE: aA d <= n) by (clear - AAB BIG; lia).
  all: assert (CE: aA d + 16384 * nk 14 d n = n - nr 14 d n) by (clear - DVM ALE NRB; lia).
  - (* fall-through: nr > 128, enter the 128-byte tail loop at 1621 (t=0) *)
    apply jbe_not in BC. destruct BC as [B1 B2].
    apply N.ltb_ge in B1. apply N.eqb_neq in B2.
    exists 0. rewrite !N.mul_0_r, !N.add_0_r, !N.sub_0_r.
    split. { clear - B1 B2; lia. }
    split. { exact C. }
    split. { exact RDI. }
    split. { exact RSI. }
    split. { reflexivity. }
    split. { exact RAX. } exact RSP.
  - (* taken: nr <= 128, go straight to the final overlapping copy at 1706 *)
    apply jbe_taken in BC.
    assert (NR32: nr 14 d n < 2^32) by (change (2^32) with 4294967296; clear - NRB; lia).
    assert (NRLE: nr 14 d n <= 128).
    { destruct BC as [B|B].
      - apply N.ltb_lt in B. rewrite N.mod_small in B by exact NR32. clear - B; lia.
      - apply N.eqb_eq in B. rewrite N.mod_small in B by exact NR32. clear - B; lia. }
    assert (NKB: 64 <= aA d + 16384 * nk 14 d n) by (clear - DVM BIG AAB NRB; lia).
    exists (aA d + 16384 * nk 14 d n).
    split. { rewrite CE. clear - NRLE NRB; lia. }
    split. { eapply cpy_equiv'; [exact C|]. intro x. clear - AAB NKB.
             split; intro H; [repeat destruct H as [H|H]; lia | lia]. }
    split. { rewrite RDI. clear; lia. }
    split. { rewrite CE. clear - NRB BIG; lia. }
    split. { exact RSI. }
    split. { exact RAX. } exact RSP.
Qed.

Lemma nt_seg_1621: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists t0, 128 * t0 + 128 < nr 14 d n /\
   cpy m (s1 V_MEM64) d s (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n + 128 * t0) /\
   s1 R_RDI = d + aA d + 16384 * nk 14 d n + 128 * t0 /\
   s1 R_RSI = (s + (aA d + 16384 * nk 14 d n + 128 * t0)) mod 2^64 /\
   s1 R_RDX = nr 14 d n - 128 * t0 /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1621, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [t0 [TLT [C [RDI [RSI [RDX [RAX RSP]]]]]]].
  repeat x64_step.
  all: change (2^14) with 16384 in *; change (2^13) with 8192 in *; change (2^12) with 4096 in *; change (2^7) with 128 in *.
  all: pose proof (aA_bounds d) as AAB.
  all: assert (DVM: n - aA d = 16384 * nk 14 d n + nr 14 d n) by
    (unfold nk, nr; change 16384 with (2^14); apply N.div_mod; discriminate).
  all: assert (NRB: nr 14 d n < 16384) by (unfold nr; change 16384 with (2^14); apply N.mod_lt; discriminate).
  all: assert (CT: aA d + 16384 * nk 14 d n + 128 * t0 + 128 <= n) by (clear - DVM AAB TLT; lia).
  all: assert (REME: msub 32 (nr 14 d n - 128 * t0) 128 = nr 14 d n - 128 * (t0+1)) by
    (rewrite reme by (change (2^32) with 4294967296; clear - TLT NRB; lia);
     clear - TLT; lia).
  all: assert (ADV: cpy m
         (s1 V_MEM64
          [Ⓨ d + aA d + 16384 * nk 14 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ s + aA d + 16384 * nk 14 d n + 128 * t0 ]]
          [Ⓨ 32 + d + aA d + 16384 * nk 14 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 32 + s + aA d + 16384 * nk 14 d n + 128 * t0 ]]
          [Ⓨ 64 + d + aA d + 16384 * nk 14 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 64 + s + aA d + 16384 * nk 14 d n + 128 * t0 ]]
          [Ⓨ 96 + d + aA d + 16384 * nk 14 d n + 128 * t0 := s1 V_MEM64 Ⓨ[ 96 + s + aA d + 16384 * nk 14 d n + 128 * t0 ]])
         d s (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n + 128 * (t0+1)))
  by (eapply cpy_equiv; cycle 1;
      [ eapply (cpy_store4w m (s1 V_MEM64) d s n
          (fun x => x < 64 \/ aA d <= x < aA d + 16384 * nk 14 d n + 128 * t0)
          (aA d + 16384 * nk 14 d n + 128 * t0) (aA d + 16384 * nk 14 d n + 128 * t0 + 32)
          (aA d + 16384 * nk 14 d n + 128 * t0 + 64) (aA d + 16384 * nk 14 d n + 128 * t0 + 96));
        first [ exact C | exact NOV | exact NB
              | (intros i Hi; clear - Hi CT AAB; change (2^64) with 18446744073709551616 in *;
                 repeat destruct Hi as [Hi|Hi]; lia)
              | (clear - CT; change (2^64) with 18446744073709551616 in *; lia)
              | (clear; change (2^64) with 18446744073709551616; f_equal; lia) ]
      | (intro x; clear - AAB; split; intro H; repeat destruct H as [H|H]; lia) ]).
  2:{ (* continue: JA taken, remaining still > 128 *)
    apply ja_taken in BC. destruct BC as [B1 B2].
    apply N.ltb_ge in B1. apply N.eqb_neq in B2.
    rewrite REME in B1. rewrite (N.mod_small (nr 14 d n - 128 * t0)) in B2
      by (change (2^32) with 4294967296; clear - NRB; lia).
    exists (t0 + 1).
    split. { clear - B1 B2 TLT; lia. }
    split. { exact ADV. }
    split. { rewrite N.mod_small by (clear - CT NW; lia). clear; lia. }
    split. { change (?a ⊕ ?b) with ((a + b) mod 2^64). f_equal. clear; lia. }
    split. { exact REME. }
    split. { exact RAX. } exact RSP. }
  { (* exit: JA not taken, remaining <= 128 *)
    apply ja_not_taken in BC.
    assert (RLE: nr 14 d n - 128 * (t0+1) <= 128).
    { destruct BC as [B|B].
      - apply N.ltb_lt in B. rewrite REME in B. clear - B; lia.
      - apply N.eqb_eq in B. rewrite (N.mod_small (nr 14 d n - 128*t0)) in B
          by (change (2^32) with 4294967296; clear - NRB; lia).
        clear - B TLT; lia. }
    exists (aA d + 16384 * nk 14 d n + 128 * (t0+1)).
    split. { clear - DVM AAB RLE TLT NRB; lia. }
    split. { eapply cpy_equiv'; [exact ADV|]. intro x. clear - AAB CT.
             split; intro H; [repeat destruct H as [H|H]; lia | lia]. }
    split. { rewrite N.mod_small by (clear - CT NW; lia). clear; lia. }
    split. { rewrite REME. clear - DVM AAB; lia. }
    split. { change (?a ⊕ ?b) with ((a + b) mod 2^64). f_equal. clear; lia. }
    split. { exact RAX. } exact RSP. }
Qed.

Lemma nt_seg_1706: forall m d s n rsp s1 t,
  nov d s n -> d + n < 2^64 -> s + n <= 2^64 -> 16448 <= n ->
  m Ⓠ[0x31a3f8] < n -> m Ⓠ[0x3215a0] <= n -> n < 2^64 -> models archtyps s1 ->
  (exists c, n - 128 <= c <= n /\
   cpy m (s1 V_MEM64) d s (fun x => x < c) /\
   s1 R_RDI = d + c /\ s1 R_RDX = n - c /\
   s1 R_RSI = (s + c) mod 2^64 /\ s1 R_RAX = d /\ s1 R_RSP = rsp) ->
  nextinv memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit false ((Addr 1706, s1) :: t).
Proof.
  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.
  destruct PRE as [c [[CL CU] [C [RDI [RDX [RSI [RAX RSP]]]]]]].
  repeat x64_step.
  split; [assumption|]. split; [assumption|].
  eapply cpy_copied; cycle 1.
  { eapply (cpy_store4w m (s1 V_MEM64) d s n (fun x => x < c) (n-128) (n-96) (n-64) (n-32));
      [ exact C | | assumption | assumption | .. ].
    { intros i Hi. clear - Hi CU. lia. }
    all: try (clear - CL CU BIG; lia).
    all: change (2^7) with 128.
    all: rewrite fcaddr by (clear - CL CU BIG; try (change (2^64) with 18446744073709551616); lia).
    all: reflexivity. }
  intro i. clear - CL CU BIG. split; intro H; [repeat destruct H as [H|H]; lia | lia].
Qed.

Theorem memmove_avx_correct_nt:
  forall st t s' x' m d s n rsp
         (ENTRY: startof t (x',s') = (Addr 0, st))
         (MDL: models x64typctx st)
         (MEM: st V_MEM64 = m) (D: st R_RDI = d) (S: st R_RSI = s) (Nn: st R_RDX = n)
         (RSP: st R_RSP = rsp)
         (NOV: nov d s n) (NW: d + n < 2^64) (SW: s + n <= 2^64)
         (BIG: 16448 <= n) (THR1: m Ⓠ[0x31a3f8] < n) (THR3: m Ⓠ[0x3215a0] <= n),
  satisfies_all memmove_avx_amd64 (nt_invs m d s n rsp) nt_exit ((x',s')::t).
Proof.
  intros.
  assert (NB: n < 2^64) by (rewrite <- Nn; apply (MDL R_RDX 64); reflexivity).
  apply prove_invs.
  simpl. rewrite ENTRY. x64_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply memmove_avx_welltyped. intro MDL1.
  clear - PRE MDL1 NOV NW SW BIG THR1 THR3 NB. rename t1 into t.
  destruct_inv 64 PRE.
  - (* entry *)
    destruct PRE as [MEM [D [S [Nn RSP]]]].
    clear NOV NW SW.
    repeat x64_step.
    all: try (set (T := m Ⓠ[0x31a3f8]) in *; clearbody T).
    all: assert (BG: 256 < n) by (clear - BIG; lia).
    all: try (match goal with |- False => idtac | |- nextinv _ _ _ _ _ => idtac end; bc_norm; refute BG).
    all: try (match goal with |- False => idtac end;
              bc_norm; first [refute THR1 | exfalso; nlia]).
    all: repeat split; reflexivity || assumption.
  - (* dispatch *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX Y0]]]]]].
    assert (N0: 0 < n) by (clear - BIG; lia).
    assert (DSN: n <= msub 64 d s) by (apply nov_ds; assumption).
    assert (SDN: n <= msub 64 s d) by (apply nov_sd; assumption).
    clear NOV.
    repeat x64_step.
    all: set (T1 := m Ⓠ[0x31a3f8]) in *; clearbody T1.
    all: set (T3 := m Ⓠ[0x3215a0]) in *; clearbody T3.
    all: try (match goal with |- False => idtac end;
              bc_norm; first [refute DSN | refute THR3 | refute THR1 | refute SDN | exfalso; nlia]).
    all: change (2^13) with 8192; change (2^14) with 16384; change (2^7) with 128.
    all: pose proof (N.mod_lt d 64 ltac:(discriminate)) as DM; pose proof (N.mod_le d 64 ltac:(discriminate)) as DL.
    all: pose proof (aA_bounds d) as AA.
    all: try (match goal with |- False => idtac end;
              match goal with H: (_ .| _) .^ 1 = N.pos _ |- _ =>
                eapply nt_no_overlap; [exact SDN | clear - SW N0; lia | exact H] end).
    all: exists 0, 0.
    all: split; [unfold nk; apply N.div_str_pos; change (2^13) with 8192; change (2^14) with 16384; clear - BIG AA; lia|].
    all: split; [clear; lia|].
    all: split;
      [ eapply cpy_equiv; [| eapply (cpy_store _ _ _ _ _ 32); [eapply (cpy_store _ _ _ _ _ 0); [apply cpy_empty|..]|..]];
        [ intro x; unfold done2, done4; clear; split; intro H; repeat destruct H as [H|H]; lia
        | .. ];
        lazymatch goal with
        | |- forall i, _ -> _ => let i := fresh in let H := fresh in intros i H; repeat destruct H as [H|H]; clear - H NB; lia
        | |- _ => clear - NB NW BIG; aside
        end
      |].
    all: unfold aA in *.
    all: split; [unfold msub; clear - NW BIG DM DL; fin_mod|].
    all: split; [unfold msub; clear - NW SW BIG DM DL NB; fin_mod|].
    all: split; [clear; lia|].
    all: split; [rewrite N.shiftr_div_pow2; unfold nk, aA; rewrite msub_sub by (clear - BIG DM; lia);
                 rewrite (N.mod_small (n + d mod 64 - 64)) by (clear - NB DM DL; lia);
                 rewrite N.sub_0_r; f_equal; clear - BIG DM DL; lia|].
    all: split; [rewrite msub_sub by (clear - BIG DM; lia); unfold nr, aA; f_equal; clear - BIG DM DL; lia|].
    all: split; [assumption || reflexivity | assumption].
  (* STATUS: build this file with `ulimit -v 13000000'.  Each per-segment
     obligation is a standalone lemma whose conclusion is a `nextinv'
     (nt_seg_1117 .. nt_seg_1706 below), so each has its own bounded Qed and the
     theorem just `apply's them.  Peak RAM was the whole difficulty here: a
     single destruct_inv branch that stepped a tail loop *through* its final
     overlapping copy carried the eight-store memory into the branch tests and
     peaked near the machine's RAM ceiling (~9 GB).  The fix was two extra
     loop-head cut points -- 1210 (two-page) and 1706 (four-page), the entries
     of the final 128-byte overlapping copy -- so the heavy final-copy stepping
     becomes its own bounded obligation (nt_seg_1210 / nt_seg_1706) and the tail
     dispatch stops there instead of stepping on.  With those cuts the two-page
     tail (nt_seg_1117 / nt_seg_1125 / nt_seg_1210) and the four-page tail
     (nt_seg_1613 / nt_seg_1621 / nt_seg_1706) are all PROVEN under ~1 GB each.
     The 128-byte tail-loop body is advanced one row at a time by cpy_store4w
     (four 32-byte stores); the final overlapping copy is discharged by
     cpy_store4w + cpy_copied via the fcaddr address lemma.  The four-page inner
     loop (nt_seg_1285) advances done4 one 128-byte-x-4-page iteration via
     cpy_store16 (sixteen 32-byte stores, loads taken from the pre-store memory),
     mirroring how the two-page inner loop (the 917 segment, inline below) uses
     nt_adv2 / cpy_store8. *)
  - (* two-page inner iteration (single loop-head cut) *)
    destruct PRE as [j [i [J [I [C [RDI [RSI [RCX [R10 [RDX [RAX RSP]]]]]]]]]]].
    assert (CKB: 8192 * nk 13 d n <= n - aA d).
    { unfold nk. change 8192 with (2^13). apply N.mul_div_le. discriminate. }
    pose proof (aA_bounds d) as AAB.
    assert (LE: aA d + 2 ^ 13 * j + 2 ^ 7 * i + 4224 <= n)
      by (change (2^13) with 8192 in *; change (2^7) with 128 in *; clear - J I CKB AAB NB; nia).
    pose proof (nt_adv2 m (s1 V_MEM64) d s n j i C NOV NB LE) as ADV.
    repeat x64_step.
    all: change (2^13) with 8192 in *; change (2^12) with 4096 in *; change (2^7) with 128 in *.
    + (* done: i=31, j=nk-1 -> full set, tail loop entry 1117 *)
      apply N.eqb_eq in BC. apply N.eqb_eq in BC0.
      rewrite N.mod_small in BC0 by (clear - J NB CKB; change (2^64) with 18446744073709551616 in *; nia).
      assert (IE: i = 31) by (clear - BC; lia). assert (JE: j = nk 13 d n - 1) by (clear - BC0 J; lia).
      assert (K1: 1 <= nk 13 d n) by (clear - J; lia).
      assert (Ej: 8192 * j = 8192 * nk 13 d n - 8192) by (clear - JE K1; nia).
      assert (Ei: 128 * i = 3968) by (clear - IE; nia).
      assert (Es: 128 * N.succ i = 4096) by (clear - IE; nia).
      split.
      { eapply cpy_equiv'; [exact ADV|]. intro x. unfold done2. rewrite Ej, Es.
        clear - K1. split; intro Hx; repeat destruct Hx as [Hx|Hx]; lia. }
      split. { rewrite Ej, Ei. rewrite N.mod_small by (clear - NW CKB AAB K1; change (2^64) with 18446744073709551616 in *; nia).
               clear - K1; lia. }
      split. { rewrite Ej, Ei. f_equal. clear - K1; lia. }
      split. exact RDX. split. exact RAX. exact RSP.
    + (* j+1 chunk *)
      apply N.eqb_eq in BC. apply N.eqb_neq in BC0.
      rewrite N.mod_small in BC0 by (clear - J NB CKB; change (2^64) with 18446744073709551616 in *; nia).
      assert (IE: i = 31) by (clear - BC; lia).
      assert (K1: 1 <= nk 13 d n) by (clear - J; lia).
      assert (Ei: 128 * i = 3968) by (clear - IE; nia).
      assert (Es: 128 * N.succ i = 4096) by (clear - IE; nia).
      assert (Ej1: 8192 * (j + 1) = 8192 * j + 8192) by (clear; nia).
      exists (j + 1), 0. split. clear - BC0 J; lia. split. clear; lia.
      split.
      { eapply cpy_equiv'; [exact ADV|]. intro x. unfold done2. rewrite Es, Ej1.
        clear. split; intro Hx; repeat destruct Hx as [Hx|Hx]; lia. }
      split. { rewrite Ei, Ej1. rewrite N.mod_small by (clear - NW CKB AAB J K1; change (2^64) with 18446744073709551616 in *; nia).
               clear; lia. }
      split. { rewrite Ei, Ej1. rewrite N.mul_0_r, N.add_0_r. f_equal. clear; lia. }
      split. clear; lia.
      split. { rewrite msub_sub by (clear - BC0 J; lia).
               rewrite N.mod_small by (clear - J NB CKB; change (2^64) with 18446744073709551616 in *; nia).
               clear - BC0 J; lia. }
      split. exact RDX. split. exact RAX. exact RSP.
    + (* i+1 inner *)
      apply N.eqb_neq in BC.
      assert (Es: 128 * N.succ i = 128 * i + 128) by (clear; nia).
      exists j, (N.succ i). split. exact J. split. clear - I BC; lia. split. exact ADV.
      split. { rewrite Es. rewrite N.mod_small by (clear - NW LE AAB J I CKB NB BC; change (2^64) with 18446744073709551616 in *; nia).
               clear; lia. }
      split. { rewrite Es. f_equal. clear; lia. }
      split. { rewrite msub_sub by (clear - I; lia). rewrite N.mod_small by (clear - I; lia). clear - I; lia. }
      split. exact R10. split. exact RDX. split. exact RAX. exact RSP.
  - (* 1117 *) apply nt_seg_1117; assumption.
  - (* 1125 *) apply nt_seg_1125; assumption.
  - (* 1210 *) apply nt_seg_1210; assumption.
  - (* 1285 *) apply nt_seg_1285; assumption.
  - (* 1613 *) apply nt_seg_1613; assumption.
  - (* 1621 *) apply nt_seg_1621; assumption.
  - (* 1706 *) apply nt_seg_1706; assumption.
Admitted.
