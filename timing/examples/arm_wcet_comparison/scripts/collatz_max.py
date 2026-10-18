# Cortex-M0 copy of collatz_from / collatz_cycles from collatz/collatz_proofs.v
# (CortexM0NoWait constants), used to find the worst-case input reported in the paper.
t_even=1+3; t_odd=8; t_half_ret=1+1+1+(4+2); t_half_loop=1+1+3
t_ret0=1+3+(4+2); t_head_exit=1+1+3+t_ret0; t_head_cont=1+1+1
def nxt(n): return ((1+n+(n<<1))%65536)//2
def cf(k,n):
    tot=0
    while True:
        if k==0: return tot
        kp=k-1
        if n%2==0:
            tot+=t_even
            if n//2==1: return tot+t_half_ret
            tot+=t_half_loop
            if kp==0: return tot+t_head_exit
            tot+=t_head_cont; k=kp; n=n//2
        else:
            tot+=t_odd
            if kp==0: return tot+3+t_ret0
            tot+=1; kpp=kp-1
            if nxt(n)==1: return tot+t_half_ret
            tot+=t_half_loop
            if kpp==0: return tot+t_head_exit
            tot+=t_head_cont; k=kpp; n=nxt(n)
setup=1+(1+1+1)+1+1+2+3
cyc=lambda n: setup+cf(55000,n)
if __name__ == '__main__':
    best = max(range(1, 65536), key=cyc)
    print(f'max collatz_cycles = {cyc(best)} at n = {best}')
