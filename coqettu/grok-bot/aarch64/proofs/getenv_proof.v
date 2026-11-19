(* getenv -- musl 1.2.6 (Alpine 1.2.6-r6), aarch64, compiled C (calls __strchrnul and strncmp)

   SEMANTICS
   ---------
   musl's src/env/getenv.c:
       size_t l = __strchrnul(name, '=') - name;
       if (l && !name[l] && __environ) {
           for (char **e = __environ; *e; e++)
               if (!strncmp(name, *e, l) && l[*e] == '=')
                   return *e + l+1;
       }
       return 0;
   The binary pushes a 48-byte frame (X29, X30 at sp-48/sp-40, X19, X20 at
   sp-32/sp-24, X21 at sp-16), keeps name in X21, calls __strchrnul
   (0x15ebf4, which itself may call strlen 0x15efa8) with c = '=', sets
   X20 = l, loads __environ through the GOT slot 0x1bffa8, walks the
   environment with X19 = &environ[j], calls strncmp (0x15f110) for each
   entry and compares entry[l] with '='.  The proofs of __strchrnul
   (strchrnul_proof.v) and strncmp (strncmp_proof.v) are reused whole via
   lib/GrokCall.v (satisfies_all_transfer) at levels 1 and 2, with X19/X20/X21
   carried across the calls by lib/GrokKeep.v.

   SPECIFICATION (man 3 getenv, Linux man-pages 6.9.1)
   ---------------------------------------------------
     SYNOPSIS
            #include <stdlib.h>
            char *getenv(const char *name);

     DESCRIPTION
            The getenv() function searches the environment list to find the
            environment variable name, and returns a pointer to the
            corresponding value string.

     RETURN VALUE
            The getenv() function returns a pointer to the value in the
            environment, or NULL if there is no match.

   THEOREM AND PRECONDITIONS
   -------------------------
   getenv_partial_correctness, with M = gv_M sp mem raddr x19 x20 x21 x29 the
   memory after the frame is pushed (equal to the entry memory wherever the
   name and the environment do not overlap [sp-48, sp)):
   - L is the __strchrnul length of name in M: the first L bytes of name are
     neither 0 nor '=' (strchrnul_proof.scan) and M[name+L] is 0 or '=';
     name + L < 2^64; 48 <= sp.
   - E = gv_env M = M[M[0x1bffa8]] is __environ; entry j is M[E + 8j]
     (env_entry); gv_match M name e L says e's first L bytes equal name's and
     e[L] = '='; gv_skip ... j says entries 0..j-1 are non-null and do not
     match.

   PROVENANCE
   ----------
   Binary:  alpine_musl/aarch64/lib/libc.musl-aarch64.so.1 (symlink to
            ld-musl-aarch64.so.1), from musl-1.2.6-r6.apk (Alpine aarch64,
            apk sha256 180b2e52dbd452919c3271ed9dddf06826cee9a387650c81c00c7ac393031c5b)
            sha256 4723e4caefd84b40d4164d62762360d3e7ab0b968eae16ea4aa6781e6d59141e
            getenv at 0x1ff88 (ELF vaddr); 0x11ff88 in Ghidra (image base 0x100000);
            callees __strchrnul 0x15ebf4, strlen 0x15efa8, strncmp 0x15f110.
   Lifter:  Ghidra 12.0 PUBLIC (headless, pyghidraRun) + pcode2coq_headless.py,
            our copy in ../lifter (picinae-llm tools/ghidra-lifter at a4bae9c +
            local fixes, see ../lifter/README_GROK.md), options
            --globalAddressing --typeCheck; see ../lifted/getenv_armv8.v,
            strncmp_armv8.v, strchrnul_armv8.v, strlen_armv8.v.
   Model:   This specification and proof were written by Grok Bot (agent coqettu)
            and machine-checked by Rocq.

   INPUT/OUTPUT SPECIFICATION (AAPCS64)
   ------------------------------------
   Input:   X0 = name; X30 = raddr, SP = sp, X19 = x19, X20 = x20, X21 = x21,
            X29 = x29; mem = memory on entry.
   Output:  At getenv's RET (0x11ffd4; gv_post at level 3): memory = M,
            SP = sp, X30 = raddr, X19 = x19, X20 = x20, X21 = x21, X29 = x29,
            and either
            X0 = 0 and (L = 0, or M[name+L] <> 0 (name contains '='), or
            E = 0, or some J has gv_skip ... J and entry J = 0), or
            X0 = entry j + (L + 1) mod 2^64 for some j with gv_skip ... j,
            entry j <> 0 and gv_match M name (entry j) L (the first matching
            entry; X0 points just past its '=').
            X22..X28 and Z8..Z15 are never written by getenv, __strchrnul,
            strlen or strncmp (getenv_preserves_other_callee_saved).
 *)
From Stdlib Require Import Utf8 NArith Lia List.
Require Import Picinae_armv8.
From Grok.lifted Require getenv_armv8 strncmp_armv8 strchrnul_armv8 strlen_armv8.
From Grok.lib Require Import GrokCommon GrokStep GrokCall GrokKeep.
From Grok.proofs Require strchrnul_proof strncmp_proof.
From Grok.proofs Require Import getenv_defs getenv_callees getenv_lib getenv_vc_entry getenv_vc_loop.
Import ARM8Notations.
Open Scope N.

Ltac srefl := match goal with |- ?a = ?a => reflexivity end.

Theorem getenv_partial_correctness:
  ∀ prog s sp mem raddr x19 x20 x21 x29 name L t xs'
    (P3: getenv_armv8.getenv_armv8 ⊆2 prog) (P2: strncmp_armv8.strncmp_armv8 ⊆2 prog)
    (P1: strchrnul_armv8.strchrnul_armv8 ⊆2 prog) (P0: strlen_armv8.strlen_armv8 ⊆2 prog)
    (ENTRY: startof t xs' = (Addr 0x11ff88, s)) (MDL: models arm8typctx s)
    (SP: s R_SP = sp) (MEM: s V_MEM64 = mem) (X30: s R_X30 = raddr) (X0: s R_X0 = name)
    (X19: s R_X19 = x19) (X20: s R_X20 = x20) (X21: s R_X21 = x21) (X29: s R_X29 = x29)
    (SC: strchrnul_proof.scan (gv_M sp mem raddr x19 x20 x21 x29) name 0x3d L)
    (ST: gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0 \/ gv_M sp mem raddr x19 x20 x21 x29 Ⓑ[name + L] = 0x3d)
    (NL: name + L < 2^64) (SPL: 48 <= sp),
  satisfies_all prog (gv_invs3 sp mem raddr x19 x20 x21 x29 name L 0 0) (gv_exits3 sp mem raddr x19 x20 x21 x29 name L 0 0) (xs'::t).
Proof.
  intros.
  pose proof (MDL R_SP 64 eq_refl) as W_SP. rewrite SP in W_SP. simpl in W_SP.
  pose proof (MDL R_X19 64 eq_refl) as W19. rewrite X19 in W19. simpl in W19.
  pose proof (MDL R_X20 64 eq_refl) as W20. rewrite X20 in W20. simpl in W20.
  pose proof (MDL R_X21 64 eq_refl) as W21. rewrite X21 in W21. simpl in W21.
  pose proof (MDL R_X29 64 eq_refl) as W29. rewrite X29 in W29. simpl in W29.
  pose proof (MDL R_X30 64 eq_refl) as W30. rewrite X30 in W30. simpl in W30.
  pose proof (MDL R_X0 64 eq_refl) as W0. rewrite X0 in W0. simpl in W0.
  eapply satisfies_all_pmono with (p1:=gv_prog).
    apply gv_prog_mono; assumption.
    intros a s1 t1 EXIT NOCODE. unfold gv_invs3, make_invs. rewrite NOCODE. reflexivity.
    intros xs1 t1 START. rewrite ENTRY in START.
    clear - MDL SP MEM X30 X0 X19 X20 X21 X29 SC ST NL SPL W_SP W19 W20 W21 W29 W30 W0 START.
    rename t1 into t. rename xs1 into xs'. rename START into ENTRY.
  apply prove_invs.
  simpl. rewrite ENTRY. arm8_step. repeat split; assumption.
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply gv_prog_welltyped. intro MDL1.
  clear - PRE MDL1 SC ST NL SPL W_SP W19 W20 W21 W29 W30 W0. rename t1 into t.
  destruct_inv 64 PRE.
  - eapply (gv_case_entry sp mem raddr x19 x20 x21 x29 name L); first [ exact PRE | sassumption | assumption ].
  - eapply (gv_case_loop sp mem raddr x19 x20 x21 x29 name L); first [ exact PRE | sassumption | assumption ].
Qed.
