# Python copy of collatz_from / collatz_cycles from collatz_proofs.v (i5-7300U
# constants), used to find the worst-case input reported in the paper.
test_r8_i,jz,add,lea,cmp64,shr,cmp16,jnz,ret,xor,jmp=1,10,1,10,1,5,1,10,26,1,10
t_even=test_r8_i+jz; t_odd=test_r8_i+jz+add+lea+cmp64+jz
t_half_ret=shr+cmp16+jnz+ret; t_half_loop=shr+cmp16+jnz
t_head_exit=add+cmp64+jz+ret; t_head_cont=add+cmp64+jz
def odd_next(n): return ((1+n+n*2)%65536)//2
def collatz_from(k,n):
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
            if kp==0: return tot+ret
            kpp=kp-1
            if odd_next(n)==1: return tot+t_half_ret
            tot+=t_half_loop
            if kpp==0: return tot+t_head_exit
            tot+=t_head_cont; k=kpp; n=odd_next(n)
def cycles(n): return xor+jmp+collatz_from(55000,n)
if __name__ == '__main__':
    assert cycles(27) == 3657 and cycles(21845) == 2145020  # the Goals in collatz_proofs.v
    best = max(range(1, 65536), key=cycles)
    print(f'max collatz_cycles = {cycles(best)} at n = {best}')
