# Checks the Cortex-M0 closed forms in the paper's aiT table against the
# time_of_* definitions in the *_proofs.v files.
# Cortex-M0 (CortexM0NoWait) constants
tmovs_imm=tmovs_reg=tadds_3reg=tadds_imm8=tsubs_imm8=tmuls=tcmp_reg=tcmp_imm=tlsls_imm=tlsrs_imm=ttst=tuxth=1
tldr_imm=tldr_pc=tstr_imm=2; tldm_base=tpush_base=1; tpop_pc_base=4
tb_taken=3; tb_not_taken=1; tb=3; tbx=3
# the time_of_* right-hand sides
def sum_(size):
    return tcmp_imm + ((tb_taken+tmovs_imm+tb+tbx) if size==0 else (tb_not_taken+tlsls_imm+tmovs_reg+tadds_3reg+tmovs_imm+(size-1)*((tldm_base+1)+tadds_3reg+tcmp_reg+tb_taken)+(tldm_base+1)+tadds_3reg+tcmp_reg+tb_not_taken+tbx))
def wtb(n):
    return tmovs_reg+tmuls+tlsls_imm+tcmp_reg+((tb_taken+tbx) if n*n<=n+n else (tb_not_taken+(n-3)*(tsubs_imm8+tmovs_reg+tmuls+tlsls_imm+tcmp_reg+tb_taken)+tsubs_imm8+tmovs_reg+tmuls+tlsls_imm+tcmp_reg+tb_not_taken+tbx))
def find(length,idx,p):
    base=(tpush_base+2+1)+tcmp_imm
    if length==0: return base+tb_taken+tldr_pc+(tpop_pc_base+3)
    body=tldr_imm+tcmp_reg+tb_taken+tadds_imm8+tadds_imm8+tcmp_reg+tb_not_taken
    r=base+tb_not_taken+tmovs_imm+tb+p*(tb_not_taken+tldr_imm+tcmp_reg)
    if idx is not None: return r+idx*body+tldr_imm+tcmp_reg+tb_not_taken+tldr_imm+tcmp_reg+tb_not_taken+tuxth+tb+(tpop_pc_base+3)
    return r+(length-1)*body+tldr_imm+tcmp_reg+tb_taken+tadds_imm8+tadds_imm8+tcmp_reg+tb_taken+tldr_pc+(tpop_pc_base+3)
def ins(pos,length):
    r=(tpush_base+1+1)+tcmp_imm+tb_not_taken+tcmp_imm+tb_not_taken+tmovs_imm+tcmp_imm
    if pos==0: return r+tb_not_taken+tb+tmovs_reg+tldr_imm+tb+tstr_imm+tstr_imm+(tpop_pc_base+2)
    m=min(pos,length)
    return r+tb_taken+(m-1)*(tmovs_reg+tldr_imm+tcmp_imm+tb_taken+tadds_imm8+tcmp_reg+tb_not_taken)+tmovs_reg+tldr_imm+tcmp_imm+((tb_taken+tadds_imm8+tcmp_reg+tb_taken+tmovs_reg+tldr_imm+tb) if pos<length else tb_not_taken)+tstr_imm+tstr_imm+(tpop_pc_base+2)
def sorted_(d):
    return tldr_imm+tldr_pc+(tpush_base+1+1)+tcmp_reg+tb_not_taken+d*(tmovs_reg+tldr_imm+tldr_imm+tcmp_reg+tb_taken)+tmovs_reg+tldr_imm+tldr_imm+tcmp_reg+tb_not_taken+tstr_imm+tstr_imm+(tpop_pc_base+2)
# closed forms in the paper
for n in range(0,300):
    assert sum_(n)==(11 if n==0 else 7+7*n)
    assert wtb(n)==(10 if n<=2 else 8*n-10)
    assert sorted_(n)==26+9*n
    for L in range(1,40):
        for p in range(0,3):
            if n<L: assert find(L,n,p)==29+10*n+4*p
        assert find(L,None,0)==21+10*L
        if n>=1: assert ins(n,L)==(30+10*n if n<L else 17+10*L)
    assert ins(0,5)==29
print("all closed forms check")
