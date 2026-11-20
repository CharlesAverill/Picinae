from pathlib import Path
src=Path('Examples/claude/amd64_memmove_avx_overlap_forward_proof.v').read_text()
header='''(* Forward overlap above the starting NT-policy threshold.
   Initial author: OpenAI gpt-6-astra, xhigh/default.
   Final proof producer: pending kernel validation.
   Binary: /lib/x86_64-linux-gnu/libc.so.6, Ubuntu amd64 glibc 2.35-0ubuntu3.12,
   SHA256 9b846df01200e522f8c57c1c0e4435777180d6fa031fa2baa6fa34f68562c4d9.
   __memmove_avx_unaligned_erms: Ghidra 0x2a0840, image base 0x100000.
   Inherited Ghidra 11.4.2/pcode2coq provenance, not revalidated here.
   Generated memmove_avx_amd64.v remains unchanged.

   English specification: memmove(d,s,n) copies the ORIGINAL source bytes
   to destination and returns d, preserving all bytes outside destination.
   System V AMD64 entry: RDI=d, RSI=s, RDX=n, RSP=rsp, V_MEM64=m.
   At the cut before RET 493: RAX=d, RSP=rsp, original-memory copy and
   outside frame; RBX/RBP/R12-R15 retain their initial values.

   Exact domain: 256<n<2^63, d<s<d+n, s+n<=2^64 (so d+n<2^64),
   n<=m[0x31a3f8] and m[0x3215a8]<n, both little-endian quadwords.
   Equality with the starting REP threshold is included. All positive gaps
   below n are allowed. No d lower bound, gap heuristic, additional tunable,
   CPU-bit or DF assumption. No threshold separation from either data region
   is required: both actual reads precede any destination writes.

   Dispatch 309/324/331 selects 813. NEG makes RCX=s-d; CMP/JA 816/819
   therefore goes to 363, before any NT store. The other branch at 825 is
   impossible for genuine forward overlap. This proves the actual fallback,
   not the nonoverlap NT theorem from x02. Entry REP selection is excluded
   only by the assigned domain; n>REP belongs to x07.

   The saved original head/tail and unread-source row reasoning reuse x03
   helpers. The ordinary-loop proof below is adapted from the accepted x03
   Astra/Sol proof (and its attributed Claude Opus 5.5 arithmetic scaffolding).
   No assumed helper/callee contracts are introduced.

   Sequential IL partial correctness only: no termination, execution of RET,
   caller continuation, hardware availability/fault/cache/timing/concurrency
   claim or binary/lifter refinement. Inherited functional extensionality is
   subject to the transitive Print Assumptions audit.
 *)
Require Import Picinae_amd64 memmove_avx_amd64.
Import X64Notations.
From Stdlib Require Import NArith ZArith Lia List.
Require Import amd64_common amd64_memcpy_lemmas amd64_memmove_avx_proof.
Require Import amd64_memmove_avx_overlap_forward_proof.
Import ListNotations.
Open Scope N.

'''
defs=src[src.index('Definition ofw_path'):src.index('(* Copy-set frames')]
defs=defs.replace('ofw_', 'ofnt_').replace('n <= m Ⓠ[0x3215a8]', 'm Ⓠ[0x3215a8] < n')
defs=defs.replace('Definition a0 (d:N) := 32 - d mod 32.\n', '')
defs=defs.replace('| 309 =>', '| 309 | 363 =>')
defs=defs.replace('  | 493 =>', '''  | 813 => Some (st V_MEM64=m /\\ st R_RDI=d /\\ st R_RSI=s /\\ st R_RDX=n /\\
      st R_RSP=rsp /\\ st R_RAX=d /\\ st R_YMM0=m Ⓨ[s] /\\ st R_RCX=d ⊖ s)
  | 493 =>''').replace('| 496 | 501 | 704 | 813 =>', '| 337 | 496 | 501 | 704 | 825 =>')
# The wrappers use x03's checked all-execution frame, with identical definition.
helpers='''Ltac ignore_vars v ::= constr:(match v with
  R_AF | R_OF | R_PF | R_SF => true | _ => false end).

Lemma ofnt_reverse_gap:
  forall d s, d < s -> s < 2^64 -> s ⊖ d = s-d.
Proof.
  intros d s DS SB. rewrite msub_sub by lia. apply N.mod_small. lia.
Qed.

Lemma ofnt_negative_gap:
  forall d s, d < s -> s < 2^64 -> msub 64 0 (d ⊖ s) = s-d.
Proof.
  intros d s DS SB.
  rewrite msub_msub_distr, N.add_comm, add_msub, N.add_0_r.
  exact (ofnt_reverse_gap d s DS SB).
Qed.

'''
main=src[src.index('Theorem memmove_avx_correct_overlap_forward:'):src.index('(* Nonvacuity:')]
main=main.replace('memmove_avx_correct_overlap_forward', 'memmove_avx_correct_forward_nt_policy').replace('memmove_avx_overlap_forward_at_ret', 'memmove_avx_forward_nt_policy_at_ret')
main=main.replace('ofw_invs','ofnt_invs').replace('ofw_exit','ofnt_exit').replace('ofw_path','ofnt_path').replace('ofw_postcondition','ofnt_postcondition').replace('ofw_frame','ofnt_frame').replace('ofw_preserves_callee_saved','ofnt_preserves_callee_saved')
main=main.replace('(THR2: n <= m Ⓠ[0x3215a8])','(THR2: m Ⓠ[0x3215a8] < n)')
a=main.index('  - (* dispatch *)'); b=main.index('    all: change (2^7) with 128.',a)
main=main[:a]+'''  - (* Actual NT-policy dispatch: branch 331 reaches 813 before stores. *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX Y0]]]]]].
    repeat x64_step.
    all: set (T := m Ⓠ[0x3215a8]) in *; clearbody T.
    all: try (match goal with |- False => idtac end;
              bc_norm; first [discriminate | exfalso; nlia]).
    all: repeat split; reflexivity || assumption.
  - (* Common forward preparation at 363; RCX on entry is irrelevant. *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX Y0]]]]]].
    repeat x64_step.
'''+main[b:]
a=main.index('Time Qed.')
main=main[:a]+'''  - (* NEG/CMP/JA falls back on every genuine forward overlap distance. *)
    destruct PRE as [MEM [D [S [Nn [RSP [RAX [Y0 RCX]]]]]]].
    assert (SB: s < 2^64) by (clear - SN BIG; lia).
    assert (GAP: s-d < n) by (clear - DS OV; lia).
    repeat x64_step.
    all: rewrite ?(ofnt_negative_gap d s DS SB),
                 ?(ofnt_reverse_gap d s DS SB) in *.
    all: try (match goal with |- False => idtac end;
              bc_norm; first [discriminate | exfalso; nlia]).
    all: repeat split; reflexivity || assumption.
'''+main[a:]
witness=src[src.index('(* Nonvacuity:'):].replace('ofw_','ofnt_')
witness=witness.replace('0x3215a8 512', '0x3215a8 511').replace('Ⓠ[0x3215a8] = 512','Ⓠ[0x3215a8] = 511')
out=header+defs+helpers+main+witness
p=Path('Examples/claude/amd64_memmove_avx_forward_nt_policy_proof.v');p.write_text(out)
Path('notes/x10-avx-forward-nt-policy/initial-attempt.v.txt').write_text(out)
p=Path('dune');d=p.read_text().replace('  Examples.claude.amd64_memmove_avx_overlap_forward_proof\n','  Examples.claude.amd64_memmove_avx_overlap_forward_proof\n  Examples.claude.amd64_memmove_avx_forward_nt_policy_proof\n');p.write_text(d)
