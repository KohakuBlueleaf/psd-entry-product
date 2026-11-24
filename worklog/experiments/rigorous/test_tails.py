import sys; sys.path.insert(0,'..')
import mpmath as mp
from flint import arb, ctx
import rig, tails
import e31_criterion_v2 as e31
from rig import coeffs
n=6; p=mp.mpf(13); b=mp.mpf('0.5')
mp.mp.dps=120
d=e31.delta_seq(n,p+b,b)+[mp.mpf(0)]*3
ev=[(d[j]-2*d[j+1]+d[j+2])/mp.e**(-(n-1)*p) for j in range(n-1)]
S=(-arb(13)).exp()
ser=tails.e_series_regular(n,S,arb('0.5'),2)
for j in range(n-1): print(j, coeffs(ser[j],2)[0].str(18), mp.nstr(ev[j],18))
# strip: Phi_j at b=0 vs small b numeric
b2=mp.mpf('1e-6'); d=e31.delta_seq(n,p+b2,b2)+[mp.mpf(0)]*3
ev=[(d[j]-2*d[j+1]+d[j+2])/mp.e**(-(n-1)*p)/b2**2 for j in range(n-1)]
st=tails.e_series_strip(n,S,arb('0.06'),3,True)
for j in range(n-1): print("strip",j, coeffs(st[j],3)[0].str(12), mp.nstr(ev[j],12))
print("first-order coefficients vs finite difference:")
for j in range(n-1):
    c=coeffs(st[j],3)
    print(j, c[1].str(8), mp.nstr((ev[j]-mp.mpf(c[0].mid().str(40,radius=False)))/b2,8))
