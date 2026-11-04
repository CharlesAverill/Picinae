from pathlib import Path
src = Path('Examples/claude/arm8_memcpy_small_proof.v').read_text()
header = '''(* __memcpy_generic, AArch64: ONLY actual medium size paths 33 <= n <= 128.

   PROVENANCE (inherited; not a binary/lifter-refinement certificate):
   Ubuntu ARM64 /lib/aarch64-linux-gnu/libc.so.6, glibc 2.35-0ubuntu3.15,
   SHA256 79fd4ecae5fb5fab4e17ec4f145d2b79026559dce52f01a478b0a04fef3dff06.
   Ghidra 11.4.2 strict scalar replacement, accepted e08 union map, unchanged:
   99 generic instructions plus nine mempcpy wrapper instructions. Model
   addresses = ELF addresses + 0x100000; generic entry is 0x19ab40.
   Initial author: OpenAI gpt-6-astra, xhigh/default, 2026-11-03.
   Initial proof adapted from accepted Astra/Sol arm8_memcpy_small_proof.v;
   shared pure helpers from arm8_memcpy_common.v are imported unchanged.
   Final proof producer/status: see notes/a-memcpy-medium/README.md.

   ENGLISH SPECIFICATION / AAPCS64:
   X0=d, X1=s, X2=n are 64-bit. Initially typed ARM8 state; 33<=n<=128;
   d+n<=2^64 and s+n<=2^64; modular source/destination byte sets disjoint;
   every source byte readable and destination byte writable. There are no
   extra alignment, non-null, CPU-feature, or tunable hypotheses.
   At either reached medium RET cut, X0=d; each destination byte equals its
   ORIGINAL source byte; EVERY byte outside the destination is unchanged.
   SP, X19..X29, X30, distinct modeled R_LR, and whole modeled Z8..Z15
   are unchanged. The theorem stops AT RET, before executing the transfer
   through X30. It proves IL partial correctness, not termination, accessible
   execution/fault freedom, hardware behavior, or binary-to-IL soundness.

   Actual size branches:
   33..64: loads head32/tail32, stores them, RET 0x19abf8.
   65..96: also loads/stores head[32,64), RET 0x19ac38.
   97..128: also loads/stores tail[n-64,n-32), RET 0x19ac38.
   All source loads precede the first store on all three paths. The proof
   executes the original map, including entry size dispatch, with separate
   opaque lemmas for each size to bound symbolic-state growth. Small/large
   copy, mempcpy and checked wrappers are NOT covered by this theorem.
*)

'''
prefix = src[src.index('Require Import'):src.index('Theorem memcpy_small_zero_entry:')]
prefix = prefix.replace('memcpy_small', 'memcpy_medium').replace('n <= 32', '33 <= n <= 128')
prefix = prefix.replace('| 0x19ab74 | 0x19ab8c | 0x19aba4 | 0x19abc8', '| 0x19abf8 | 0x19ac38')
prefix = prefix.replace('| 0x19abd0 | 0x19ac40 => Some False', '| 0x19ab5c | 0x19ac40 => Some False')
prefix = prefix.replace('unfold memcpy_medium_domain. repeat split; try assumption.', 'unfold memcpy_medium_domain. repeat split; try assumption;\n        try (exact (proj1 NN)); try (exact (proj2 NN)).')
# All alignments modulo 16, every size in the assigned class, arbitrary memory.
witness = '''Theorem memcpy_medium_alignment_witness:
  forall m da sa n,
    m < 2^(8*2^64) -> da < 16 -> sa < 16 -> 33 <= n <= 128 ->
    exists st, models arm8typctx st /\\
      memcpy_medium_domain st da (256+sa) n /\\
      memcpy_medium_input st m da (256+sa) n st.
Proof.
  intros m da sa n M DA SA NN. apply memcpy_medium_entry_inhabited.
  - exact M.
  - clear - DA. change (2^64) with 18446744073709551616. lia.
  - clear - SA. change (2^64) with 18446744073709551616. lia.
  - exact NN.
  - clear - DA NN. change (2^64) with 18446744073709551616. lia.
  - clear - SA NN. change (2^64) with 18446744073709551616. lia.
  - unfold nov. intros i j I J. clear - DA SA NN I J.
    change (2^64) with 18446744073709551616.
    rewrite !N.mod_small by lia. lia.
Qed.
Print Assumptions memcpy_medium_alignment_witness.

'''
tactics = src[src.index('(* Bound the search'):src.index('(* Concrete small size 0;')]
tactics = tactics.replace('small', 'medium').replace('(k <? 31)', '(k <? 127)')
tactics = tactics.replace('NG and OV are never consulted on the medium path.', 'NG and OV are never consulted on the medium paths.')
case = src[src.index('(* Concrete small size 0;'):src.index('(* Concrete small size 1;')].replace('small','medium')
cases = ''.join(case.replace('size 0;', f'size {n};').replace('case_0', f'case_{n}').replace('d s 0', f'd s {n}') for n in range(33,129))
main = src[src.index('Theorem memcpy_small_correct:'):]
main = main.replace('small', 'medium').replace('SMALL', 'MEDIUM')
start = main.index('    assert (CASES:')
end = main.index('\nQed.', start)
main = main[:start] + '    assert (CASES: ' + ' \\/ '.join(f'n = {n}' for n in range(33,129)) + ')\n      by (clear - MEDIUM; lia).\n    repeat destruct CASES as [->|CASES]; try (rewrite CASES in *; clear CASES).\n' + ''.join(f'    + apply memcpy_medium_case_{n}; [exact MDL1|].\n      exact (conj MEM (conj DEST (conj SRC (conj COUNT FRAME)))).\n' for n in range(33,129)) + main[end:]
main = main.replace('[0x19ab74; 0x19ab8c; 0x19aba4; 0x19abc8]', '[0x19abf8; 0x19ac38]')
# Export the full terminal contract as well as the trace-scoped frame.
terminal = '''
Theorem memcpy_medium_at_ret:
  forall st t st' a m d s n,
    startof t (Addr a,st') = (Addr 0x19ab40,st) ->
    models arm8typctx st -> st V_MEM64 = m -> st R_X0 = d ->
    st R_X1 = s -> st R_X2 = n -> memcpy_medium_domain st d s n ->
    exec_prog e08___memcpy_generic_arm8 ((Addr a,st')::t) ->
    unterminated memcpy_medium_exit t ->
    In a [0x19abf8; 0x19ac38] ->
    memcpy_medium_post st m d s n st'.
Proof.
  intros st t st' a m d s n ENTRY MDL MEM D S NN DOMAIN XP UT RET.
  pose proof (memcpy_medium_correct st t st' (Addr a) m d s n
    ENTRY MDL MEM D S NN DOMAIN) as SA.
  pose proof (satall_trueif_inv _ _ _ _ SA XP UT) as POST.
  repeat destruct RET as [<-|RET]; try contradiction;
    cbn [memcpy_medium_invs trueif_inv] in POST; exact POST.
Qed.
Print Assumptions memcpy_medium_at_ret.
'''
result = header + prefix + witness + tactics + cases + main + terminal
Path('Examples/claude/arm8_memcpy_medium_proof.v').write_text(result)
Path('notes/a-memcpy-medium/initial-proof.v.txt').write_text(result)
p = Path('dune')
dune = p.read_text()
module = '  Examples.claude.arm8_memcpy_medium_proof\n'
if module not in dune:
    dune = dune.replace('  Examples.claude.arm8_memcpy_common Examples.claude.arm8_memcpy_small_proof\n', '  Examples.claude.arm8_memcpy_common Examples.claude.arm8_memcpy_small_proof\n' + module)
if '(name a-memcpy-medium)' not in dune:
    dune += '\n(alias\n (name a-memcpy-medium)\n (deps Examples/claude/arm8_memcpy_medium_proof.vo))\n'
p.write_text(dune)
