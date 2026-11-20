from pathlib import Path
base=Path('Examples/claude/amd64_memmove_avx_nt_proof.v').read_text()
off=[p*4096+q*32 for p in range(4) for q in range(4)]
def addr(x,o):
 prefix={0:'',4096:'2 ^ 12 + ',8192:'2 ^ 13 + '}.get(o,str(o)+' + ')
 return '('+prefix+x+' + aA d + 2 ^ 14 * j + 2 ^ 7 * i)'
def mem(k):
 t='M'
 for o in off[:k]: t=f'(setmem 64 LittleE 32 {t}\n    {addr("d",o)} (getmem 64 LittleE 32 M {addr("s",o)}))'
 return t
s='''(* One four-page inner iteration, over an abstract initial memory. *)
Lemma nt_adv4: forall m M d s n j i,
  cpy m M d s (done4 d j i) -> nov d s n -> n < 2^64 ->
  aA d + 2 ^ 14 * j + 2 ^ 7 * i + 12416 <= n ->
  cpy m '''+mem(16)+''' d s (done4 d j (N.succ i)).
Proof.
  intros m M d s n j i C NOV NB LE.
  eapply cpy_equiv';
  [ eapply (cpy_store16 m M d s n (done4 d j i)
'''
s+='    '+' '.join('('+str(o)+' + (aA d + 2 ^ 14 * j + 2 ^ 7 * i))' if o else '(aA d + 2 ^ 14 * j + 2 ^ 7 * i)' for o in off)+'\n'
s+='    '+' '.join(addr('d',o) for o in off)+'\n'
s+='    '+' '.join(addr('s',o) for o in off)+''');
    first [ exact C | exact NOV | exact NB
          | (intros ii Hii; unfold done4 in Hii;
             change (2^14) with 16384 in *; change (2^7) with 128 in *;
             clear - Hii LE; lia)
          | (change (2^12) with 4096 in *; change (2^13) with 8192 in *;
             clear - LE; lia)
          | (clear; f_equal; lia) ]
  | intro x; unfold done4;
    change (2^14) with 16384 in *; change (2^7) with 128 in *;
    rewrite N.mul_succ_r; clear; split; intro H;
    repeat destruct H as [H|H]; lia ].
Qed.

'''
start=base.index('    destruct PRE as [j [i [J [I [C')
end=base.index('  - (* 1117 *)',start)
seg=base[start:end].replace('nk 13','nk 14').replace('8192','16384').replace('2^13','2^14').replace('2 ^ 13','2 ^ 14').replace('4224','12416').replace('nt_adv2','nt_adv4').replace('done2','done4')
seg=seg.replace('    repeat x64_step.', '''    do 33 x64_step.
    set (Mhalf := '''+mem(8).replace('M','(s1 V_MEM64)')+''') in *.
    clearbody Mhalf.
    do 8 x64_step.
    lazymatch type of ADV with cpy _ ?MP _ _ _ =>
      set (Mpost := MP) in *; clearbody Mpost
    end.
    repeat x64_step.''')
# Add missing power normalization for second page and fourth-page address.
seg=seg.replace('all: change (2^14)', 'all: change (2^13) with 8192 in *; change (2^14)')
Path('/tmp/x02-adv4.txt').write_text(s)
Path('/tmp/x02-seg.txt').write_text('Proof.\n  intros m d s n rsp s1 t NOV NW SW BIG THR1 THR3 NB MDL1 PRE.\n'+seg+'Qed.\n')
