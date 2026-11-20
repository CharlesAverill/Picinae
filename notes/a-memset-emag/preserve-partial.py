from pathlib import Path
import re
src=Path('notes/a-memset-emag/initial-attempt.v.txt').read_text()
cut=src.index('Theorem memset_emag_inputs_inhabited:')
head=src[:cut]
tail=src[cut:]
tail=re.sub(r'Proof\..*?Qed\.', 'Proof.\n  (* Unverified initial attempt preserved verbatim in notes/a-memset-emag/initial-attempt.v.txt. *)\nAbort.', tail, flags=re.S)
a=tail.index('(* Keep arithmetic automation')
b=tail.index('Theorem memset_emag_correct:')
tail=tail[:a]+'(* Initial Ltac script preserved in initial-attempt.v.txt. *)\n\n'+tail[b:]
tail=re.sub(r'^Print Assumptions .*?\.\n', '', tail, flags=re.M)
status='''(* PARTIAL HANDOFF: the single full build exited 1 at original line 147,
   unavailable N.pow_pos_nonneg in the inhabited-input witness. No Astra
   repair cycle was run. All declarations from that witness onward are
   aborted, not proved; exact statements and original scripts are retained
   in notes/a-memset-emag/initial-attempt.v.txt. Earlier four Qed commands
   were reached, but no full .vo or new-theorem assumptions certificate was
   produced. This sanitized handoff source has not been rebuilt. *)

'''
Path('Examples/claude/arm8_memset_emag_proof.v').write_text(status+head+tail)
# Ensure statements have not changed during mechanical quarantine.
def statements(s):
    return re.findall(r'(?:Theorem|Lemma)\s+.*?(?=\nProof\.| Proof\.)',s,re.S)
assert statements(src)==statements(head+tail)
print('Preserved all',len(statements(src)),'theorem/lemma statements exactly.')
print('Retained four pre-failure Qed bodies; aborted every later attempt.')
log=Path('notes/a-memset-emag/06-first-full-build.log').read_text()
a=log.index('Axioms:\n')
b=log.index('File ',a)
Path('notes/a-memset-emag/inherited-lift-assumptions.txt').write_text(log[a:b])
