from pathlib import Path
p=Path('Examples/claude/amd64_memmove_avx_nt_stores.v')
ids=range(1,17)
names=lambda x:' '.join(f'{x}{i}' for i in ids)
def stores(m):
 t='M'
 for i in ids: t=f'(setmem 64 LittleE 32 {t}\n    a{i} (getmem 64 LittleE 32 {m} b{i}))'
 return t
def predicate(flat):
 t='W i'
 for i in ids: t=f'{t} \\/ o{i} <= i < o{i} + 32' if flat else f'({t} \\/ o{i} <= i < o{i} + 32)'
 return '(fun i => '+t+')'
s='''(* Abstract sixteen-store memory lemma for the AVX NT four-page loop.
   Author: OpenAI GPT-6 Astra, x02-avx-nt campaign repair, 2026-11-03.
   The stores use a single pre-store snapshot M, matching the sixteen loads
   before the sixteen VMOVNTDQ instructions in the unchanged lift.
   This is a memory lemma, not an instruction or binary correctness claim. *)
Require Import Picinae_amd64.
Require Import amd64_memcpy_sets.
From Stdlib Require Import NArith Lia.
Open Scope N.

Lemma cpy_store16:
  forall m M d s n (W:N->Prop)
'''
s+='    '+names('o')+'\n    '+names('a')+'\n    '+names('b')+',\n'
s+='  cpy m M d s W -> (forall i, W i -> i < n) -> nov d s n -> n < 2^64 ->\n'
for i in ids: s+=f'  o{i} + 32 <= n ->\n'
for x,y in [('a','d'),('b','s')]:
 for i in ids: s+=f'  {x}{i} mod 2^64 = ({y} + o{i}) mod 2^64 ->\n'
s+='  cpy m '+stores('M')+' d s\n    '+predicate(True)+'.\nProof.\n'
s+='  intros m M d s n W '+names('o')+'\n    '+names('a')+'\n    '+names('b')+'\n    C WN NOV NB '+names('O')+'\n    '+names('A')+'\n    '+names('B')+'.\n'
for i in ids: s+=f'  rewrite (cpy_load m M d s W n o{i} 32 b{i} C WN NOV O{i} B{i}).\n'
s+='  assert (CS: cpy m '+stores('m')+' d s\n    '+predicate(False)+').\n'
s+='''  { repeat (apply cpy_store; [|try assumption..]); [exact C| ..].
    all: try (intros i Hi; clear - Hi WN NB '''+names('O')+''';
      change (2^64) with 18446744073709551616 in *;
      repeat destruct Hi as [Hi|Hi]; try apply WN in Hi; lia).
    all: try (clear; lia).
    all: clear - NB '''+names('O')+''';
      change (2^64) with 18446744073709551616 in *; lia. }
  eapply cpy_equiv; [|exact CS]. intro i. tauto.
Qed.
'''
p.write_text(s)
p=Path('dune');s=p.read_text().replace('  Examples.claude.amd64_memmove_avx_nt_proof))','  Examples.claude.amd64_memmove_avx_nt_stores\n  Examples.claude.amd64_memmove_avx_nt_proof))');p.write_text(s)
