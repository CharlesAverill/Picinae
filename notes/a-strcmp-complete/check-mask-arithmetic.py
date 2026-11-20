#!/usr/bin/env python3
"""Finite arithmetic sanity checks; NOT a Rocq proof or execution certificate."""
import random
W=(1<<64)-1
C=0x0101010101010101
L=0x7f7f7f7f7f7f7f7f

def byte(x,j): return (x>>(8*j))&255

def mask(x): return ((x-C)&W)&((x|L)^W)

for a in range(256):
    for borrow in (0,1):
        value=((a-1-borrow)&255)&((a|127)^255)
        assert value == (128 if a==0 or a==1 and borrow else 0)
print('512 byte/borrow cases pass')

rng=random.Random(192)
words=[0,W,C,L,0x8080808080808080]
words += [rng.getrandbits(64) for _ in range(4096)]
for x in words:
    assert (mask(x)==0)==all(byte(x,j)!=0 for j in range(8))
    for j in range(8):
        b=byte(x,j)
        borrow=int((x% (1<<(8*j))) < (C% (1<<(8*j))))
        assert byte((x-C)&W,j)==(b-1-borrow)%256
        assert byte(mask(x),j)==(128 if b==0 or b==1 and borrow else 0)
        if all(byte(x,i)!=0 for i in range(j+1)):
            assert byte(mask(x),j)==0
    for r in range(9):
        for j in range(8):
            assert byte(x|((1<<(8*r))-1),j)==(255 if j<r else byte(x,j))
            assert byte((x<<(8*r))&W,j)==(0 if j<r else byte(x,j-r))
    y=int.from_bytes(x.to_bytes(8,'little'),'big')
    if x:
        j=next(i for i in range(8) if byte(x,i))
        clz=64-y.bit_length()
        assert 8*j<=clz<=8*j+7
        if byte(x,j)&128: assert clz==8*j
print(f'{len(words)} deterministic word cases pass: borrow, first-zero, masks, REV/CLZ')
print('These checks do not certify the unproved main contract.')
