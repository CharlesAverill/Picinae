# Improvement factors (1/m) sum_{n=0}^{m} WCP/f(n) for the aiT table in the paper.
# WCP: aiT reports; f: closed forms checked by check_closed_forms.py; m: from the .ais loop bounds.
import math
from collatz_max import cyc
def psi(x):  # digamma, asymptotic (x large)
    return math.log(x)-1/(2*x)-1/(12*x*x)+1/(120*x**4)
def lin_sum(a,b,lo,hi):  # sum_{n=lo}^{hi} 1/(a+b n), exact head + digamma tail
    K=min(hi,lo+10**6); s=sum(1/(a+b*n) for n in range(lo,K+1))
    if hi>K: s+=(psi(a/b+hi+1)-psi(a/b+K+1))/b
    return s
def fac(wcp, terms, m):  # terms: list of (value f at single n) or (a,b,lo,hi)
    tot=0
    for t in terms:
        tot += wcp/t[0] if len(t)==1 else wcp*lin_sum(*t)
    return tot/m
M31=2**31-1
print('sum   ', round(fac(15032385539, [(11,),(7,7,1,M31)], M31)))
print('wtb   ', round(fac(8981, [(10,),(10,),(10,),(-10,8,3,999)], 999)))
print('arr   ', round(fac(983077, [(29,14,0,65535)], 65535)))  # len is uint16_t; +4/elt partial matches (worst case)
print('ins   ', round(fac(21474836499, [(29,),(30,10,1,M31)], M31)))
print('sorted', round(fac(18448, [(26,9,0,2047)], 2047)))
print('collatz', round(sum(990042/cyc(n) for n in range(1,65536))/65535))
