#!/usr/bin/env python3
"""Finite arithmetic sanity check only; not an IL or Rocq certificate."""
Q = 2**64
checked = 0
for n in list(range(129, 4097)) + [2**63-1, 2**63]:
    for r in range(16):
        q0 = 16-r
        k = max(0, (n-q0-128+63)//64)
        q = q0+64*k
        assert 1 <= q0 <= 16 and q0+64 <= n
        assert q+64 <= n <= q+128
        if k:
            assert q-64+128 < n
        assert max(16,q)+64 >= n-64
        # End pointer 0 must still load/store n-64..n-1 correctly.
        s = Q-n
        for offset in range(64):
            assert ((s+n)%Q-64+offset)%Q == s+(n-64+offset)
        # Source alignment may underflow; its actual first buffer access doesn't.
        assert ((0-r)%Q+16)%Q == q0
        checked += 1
print(f'{checked} count/residue cases checked; arithmetic sanity only, no proof claim')
