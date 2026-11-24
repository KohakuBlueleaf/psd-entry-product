import sys
sys.argv=['run.py','4','2','100','6','3','1']
import run, rig
from flint import arb
from rig import exp_lin_jet
run.build()
T=run.T; n=run.n; KD=run.KD; DS=run.DS; hull=run.hull
def detail(l):
    h=T.h; bs=h*KD/2; y0=T.y(l); y1=T.y(l+1); D=DS-1
    zc=[T.zjet_point(m,l,D+2) for m in range(n-1)]; ec=[exp_lin_jet(m,y0,D) for m in range(n-1)]
    pj=rig.strip_jets(n,D,zc,zc,zc,ec,True)
    plo=T.y(l-KD) if l>=KD else arb(0)
    Ab=hull(y0,y1);Pb=hull(plo,y1);Qb=hull(y0,y1+bs);Bb=hull(plo,y1+bs)
    zB=[T.zjet(m,Bb,DS+2,l) for m in range(n-1)]
    zP=[T.zjet(m,Pb,DS,l) for m in range(n-1)]; zQ=[T.zjet(m,Qb,DS,l) for m in range(n-1)]
    eA=[exp_lin_jet(m,Ab,DS) for m in range(n-1)]
    bj=rig.strip_jets(n,DS,zB,zP,zQ,eA,False)
    print("l",l,"zB[1]",[z.str(5) for z in zB[1]])
    print("   zc[1]",[z.str(5) for z in zc[1]])
    for j in range(n-1):
        print("  j",j,"c0",pj[j].get(0,0).str(6),{k:v.str(4) for k,v in pj[j].c.items() if sum(k)>=1},"TOP",{k:v.str(4) for k,v in bj[j].c.items() if sum(k)==DS})
for l in (2,10,30,45): detail(l)
