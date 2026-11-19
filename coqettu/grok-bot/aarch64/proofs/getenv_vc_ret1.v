(* getenv: VCs after __strchrnul returns (0x11ffa4 to the loop head or RET).
   Full header (SEMANTICS, man-page SPECIFICATION, PROVENANCE, I/O specification)
   is in getenv_proof.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require getenv_armv8 strncmp_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require strchrnul_proof strncmp_proof.
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib.
Import ARM8Notations.
Open Scope N.



Lemma gv_after_chrnul:
  ∀ sp mem raddr x19 x20 x21 x29 name L s t
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (ST: gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0 \/ gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0x3d)
    (NL: name + L < 2^64) (SPL: 48 <= sp) (W_SP: sp < 2^64) (W0: name < 2^64) (KLT: L < 2^64)
    (G48: gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 48] = x29)
    (G40: gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 40] = raddr)
    (G32: gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 32] = x19)
    (G24: gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 24] = x20)
    (G16: gv_M sp mem raddr x19 x20 x21 x29 Ⓠ[sp ⊖ 16] = x21)
    (RSP: s R_SP = sp ⊖ 48) (MEM': s V_MEM64 = gv_M sp mem raddr x19 x20 x21 x29)
    (R0: s R_X0 = name + L) (K21: s R_X21 = name),
  nextinv gv_prog (make_invs 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0))
    (make_exits 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0)) true ((Addr 0x11ffa4, s) :: t).
Proof.
  intros.
    all: repeat arm8_step.
    all: set (M := gv_M sp mem raddr x19 x20 x21 x29) in *; clearbody M.
    all: gv_bools.
    all: try rewrite (N.mod_small L (2^64) KLT) in *.
    all: try (refine (conj eq_refl (conj G40 (conj G32 (conj G24 (conj G16 (conj G48 (conj eq_refl (or_introl (conj eq_refl _)))))))));
              first [ left; sassumption | right; left; sassumption | right; right; left; unfold gv_env; sassumption ]).
    all: exists 0; unfold gv_env; rewrite N.mul_0_r, N.add_0_r, N.mod_small by apply qword_lt64.
    all: splits; try sreflexivity.
    all: first [ sassumption | apply skip_0 | (apply N.neq_0_lt_0; sassumption) ].
Qed.
