import sys; sys.path.insert(0, '..')
import mpmath as mp
from flint import arb, ctx
import rig
from rig import Table, lift, e_jets, exp_lin_jet
import e31_criterion_v2 as e31
n=6; hden=50; Q=2
T=Table(n,1,hden,Q,3)
mp.mp.dps=50
# A_m at grid points vs mp
for m in (0,1,3):
    l=37; x=mp.mpf(l)/(2*hden)
    if m==0: ref=-2*e31.gam0(n,x,400)
    else: ref=(1-e31.sigma(n,m,x,400))*mp.e**(-m*x)/m
    print("A",m, T.A[m][l].str(25), mp.nstr(ref,25))
# e_j at point p=y_20=0.2, q=y_90=0.9, alpha=y_55
lp,lq,la=20,90,55
D=2
Zp=[lift(T.zjet_point(m,lp,D),D,"x") for m in range(n-1)]
Zq=[lift(T.zjet_point(m,lq,D),D,"y") for m in range(n-1)]
Za=[lift(T.zjet_point(m,la,D),D,"mid") for m in range(n-1)]
Ea=[lift(exp_lin_jet(m,T.y(la),D),D,"mid") for m in range(n-1)]
ej=e_jets(n,D,Zp,Zq,Za,Ea)
al=mp.mpf('0.55'); b=mp.mpf('0.35')
d=e31.delta_seq(n,al,b)+[mp.mpf(0)]*3
ev=[d[j]-2*d[j+1]+d[j+2] for j in range(n-1)]
for j in range(n-1): print("e",j, ej[j].get(0,0).str(20), mp.nstr(ev[j],20))
# derivative check by finite differences of e_0 in p
eps=mp.mpf('1e-12')
def e0(p,q):
    dd=e31.delta_seq(n,(p+q)/2,(q-p)/2)+[mp.mpf(0)]*3
    return dd[1]-2*dd[2]+dd[3]
p0,q0=mp.mpf('0.2'),mp.mpf('0.9')
print("d/dp e_1:", ej[1].get(1,0).str(12), mp.nstr((e0(p0+eps,q0)-e0(p0-eps,q0))/(2*eps),12))
print("d2/dpdq e_1:", ej[1].get(1,1).str(10), mp.nstr((e0(p0+1e-8,q0+1e-8)-e0(p0+1e-8,q0-1e-8)-e0(p0-1e-8,q0+1e-8)+e0(p0-1e-8,q0-1e-8))/(4e-16),8))
