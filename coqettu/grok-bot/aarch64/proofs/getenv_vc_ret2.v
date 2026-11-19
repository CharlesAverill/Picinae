(* getenv: VCs after strncmp returns (0x11fff0 to the loop head or RET).
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


Ltac ringmod := unfold env_entry; match goal with |- (?a) mod ?m = (?b) mod ?m => replace b with a by ring; reflexivity end.
Ltac scontra BB := lazymatch type of BB with ?X = ?Y =>
  match goal with H: ¬ (?X' = ?Y') |- _ => constr_eq X X'; constr_eq Y Y'; exact (H BB) end end.

Lemma gv_after_ncmp:
  ∀ sp mem raddr x19 x20 x21 x29 name L j k s t
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (NL: name + L < 2^64) (SPL: 48 <= sp) (W_SP: sp < 2^64)
    (G48: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 48] = x29) (G40: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 40] = raddr) (G32: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 32] = x19)
    (G24: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 24] = x20) (G16: (gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[sp ⊖ 16] = x21)
    (LP: 0 < L) (NZ: (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + L] = 0) (EN: gv_env (gv_M sp mem raddr x19 x20 x21 x29) ≠ 0)
    (SK: gv_skip (gv_M sp mem raddr x19 x20 x21 x29) name (gv_env (gv_M sp mem raddr x19 x20 x21 x29)) L j) (BC: ((gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) ≠ 0)
    (KL: k < L) (EQk: mem_eq (gv_M sp mem raddr x19 x20 x21 x29) name ((gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) k)
    (STk: (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k] ≠ (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[((gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) + k] \/ (gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k] = 0 \/ k = L - 1)
    (R0: s R_X0 = msub 32 ((gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[name + k]) ((gv_M sp mem raddr x19 x20 x21 x29) Ⓑ[((gv_M sp mem raddr x19 x20 x21 x29) Ⓠ[gv_env (gv_M sp mem raddr x19 x20 x21 x29) + 8 * j]) + k]))
    (MEM': s V_MEM64 = (gv_M sp mem raddr x19 x20 x21 x29)) (RSP: s R_SP = sp ⊖ 48)
    (K19: s R_X19 = gv_env (gv_M sp mem raddr x19 x20 x21 x29) ⊕ 8 * j) (K20: s R_X20 = L) (K21: s R_X21 = name),
  nextinv gv_prog (make_invs 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0))
    (make_exits 3 gv_prog (invs sp mem raddr x19 x20 x21 x29 name L 0 0)) true ((Addr 0x11fff0, s) :: t).
Proof.
  intros.
      repeat arm8_step.
      all: set (M := (gv_M sp mem raddr x19 x20 x21 x29)) in *; clearbody M.
      all: gv_bools.
      all: lazymatch goal with
        | |- ∃ _, _ =>
            exists (j+1); splits;
            first [ sassumption | sreflexivity | ringmod
                  | (apply skip_succ; [ sassumption | unfold env_entry; sassumption
                                      | first [ (lazymatch type of BC0 with _ ≠ 0 => idtac end; intros (MEQ & _); rewrite msub32_mod in BC0; exact (sn_nonzero _ _ _ _ _ KL BC0 MEQ))
                                              | (intros (_ & BB); unfold env_entry in BB; scontra BB) ] ]) ]
        | |- _ =>
            split; [sreflexivity|]; split; [sassumption|]; split; [sassumption|]; split; [sassumption|];
            split; [sassumption|]; split; [sassumption|]; split; [sreflexivity|];
            right; exists j; splits;
            first [ sassumption | (unfold env_entry; sassumption) | ringmod
                  | (unfold gv_match, env_entry; split;
                     [ rewrite msub32_mod in BC0; exact (sn_zero _ _ _ _ _ LP (scan_nf _ _ _ _ SC) KL EQk STk BC0)
                     | sassumption ]) ]
        end.
Qed.
