import sys
sys.argv=['run.py','4','2','100','6','3','1']
import run
from flint import arb
run.build()
T=run.T; n=run.n; KD=run.KD
from rig import lift,e_jets,exp_lin_jet
def detail(l):
    h=T.h; bs=h*KD/2; y0=T.y(l); y1=T.y(l+1)
    zpt=[T.zjet_point(m,l,2) for m in range(n-1)]
    ept=[exp_lin_jet(m,y0,2) for m in range(n-1)]
    e2=e_jets(n,2,[lift(z,2,"ab_p") for z in zpt],[lift(z,2,"ab_q") for z in zpt],[lift(z,2,"x") for z in zpt],[lift(z,2,"x") for z in ept])
    Ab=(y0+y1)/2+arb(0,float(((y1-y0)/2).abs_upper())*1.0000001)
    zA=[T.zjet(m,Ab,3,l) for m in range(n-1)]; eA=[exp_lin_jet(m,Ab,3) for m in range(n-1)]
    e3=e_jets(n,3,[lift(z,3,"ab_p") for z in zA],[lift(z,3,"ab_q") for z in zA],[lift(z,3,"x") for z in zA],[lift(z,3,"x") for z in eA])
    plo=T.y(l-KD) if l>=KD else arb(0)
    hull=lambda a,b:(a+b)/2+arb(0,float(((b-a)/2).abs_upper())*1.0000001)
    Pb,Qb=hull(plo,y1),hull(y0,y1+bs)
    zP=[T.zjet(m,Pb,4,l) for m in range(n-1)]; zQ=[T.zjet(m,Qb,4,l) for m in range(n-1)]
    zA4=[T.zjet(m,Ab,4,l) for m in range(n-1)]; eA4=[exp_lin_jet(m,Ab,4) for m in range(n-1)]
    e4=e_jets(n,4,[lift(z,4,"ab_p") for z in zP],[lift(z,4,"ab_q") for z in zQ],[lift(z,4,"x") for z in zA4],[lift(z,4,"x") for z in eA4])
    for j in range(n-1):
        print(l,j,"G0",e2[j].get(0,2).str(8),"dG",e3[j].get(1,2).str(6),"c04",e4[j].get(0,4).str(6))
for l in (0,1,20,100,127,128,300): detail(l)
