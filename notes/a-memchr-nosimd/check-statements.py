from pathlib import Path
import re
for stem in ['arm8_memchr_nosimd_spec','arm8_memchr_nosimd_proof']:
    initial=Path('notes/a-memchr-nosimd/initial-'+stem+'.v.txt').read_text()
    final=Path('Examples/claude/'+stem+'.v').read_text()
    decls=re.findall(r'((?:Theorem|Lemma) (\w+)\b.*?\n)Proof\.',initial,re.S)
    for declaration,name in decls:
        assert declaration in final,name
        print('UNCHANGED STATEMENT',name)
    # All packaging changes are confined to the three named proof bodies.
    for name in (['mc_all_alignments_inhabited'] if stem.endswith('_spec') else
                 ['mc_detector_correct','memchr_nosimd_correct']):
        pattern=r'((?:Theorem|Lemma) '+name+r'\b.*?\n)Proof\..*?Qed\.\nPrint Assumptions '+name+r'\.'
        initial,count=re.subn(pattern,lambda m:m[1]+'(* PARTIAL: exact initial proof is preserved in notes/a-memchr-nosimd/. *)\nAbort.',initial,flags=re.S)
        assert count==1
    assert initial==final,stem
print('Only failed/unattempted proof bodies were replaced by Abort; no statement or definition change.')
