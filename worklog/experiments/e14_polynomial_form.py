"""E14. Structure of (**).  Write s=e^u, t=e^v, tau=sqrt(st), gamma_m(u) = c_m(e^u).
 (a) Is the degree-D polynomial  W(x) = h_tau(x) - R_{s,t}(x) >= 0 on [-1,1]?   (W >= 0 implies (**) via Cohn-Kumar.)
     W = [c_0(tau) - (c_0(s)+c_0(t))/2] + sum_m [c_m(tau) - sqrt(c_m(s)c_m(t))] T_m(x).
 (b) Is each gamma_m (m>=1) log-concave in u, and gamma_0 concave?  (signs of the coefficients of W)
"""
import numpy as np, mpmath as mp
from e13c_gm_certificate_mp import coeffs
mp.mp.dps = 40
rng = np.random.default_rng(0)
xs = [mp.cos(mp.pi * k / 400) for k in range(401)]
for n in (3, 4, 5, 6, 7, 8):
    minW = mp.inf; mind0 = mp.inf; mindm = mp.inf; arg = None
    for _ in range(120):
        a = rng.uniform(-4, 4); b = rng.choice([0.05, 0.3, 1.0, 2.5])
        cs, ct, cm = coeffs(n, mp.e ** (a + b)), coeffs(n, mp.e ** (a - b)), coeffs(n, mp.e ** a)
        d = [cm[0] - (cs[0] + ct[0]) / 2] + [cm[m] - mp.sqrt(cs[m] * ct[m]) for m in range(1, len(cm))]
        scale = cs[1] + ct[1]
        mind0 = min(mind0, d[0] / scale); mindm = min(mindm, min(d[1:]) / scale)
        for x in xs:
            th = mp.acos(x)
            w = (d[0] + sum(d[m] * mp.cos(m * th) for m in range(1, len(d)))) / scale
            if w < minW: minW, arg = w, (a, b, float(x))
    print(f"n={n}: min W/scale = {mp.nstr(minW, 5)} at (a,b,x)={arg};  min delta_0 = {mp.nstr(mind0, 4)};  min delta_m(m>=1) = {mp.nstr(mindm, 4)}")
