"""E14b. With delta_0 = c_0(tau) - avg c_0,  delta_m = c_m(tau) - sqrt(c_m(s)c_m(t)) >= 0:
compare delta_0 with sum_m delta_m and with the alternating sum (value of W at x=-1)."""
import numpy as np, mpmath as mp
from e13c_gm_certificate_mp import coeffs
mp.mp.dps = 40
rng = np.random.default_rng(1)
for n in (3, 4, 5, 6, 7, 8, 11):
    r1 = mp.inf; r2 = mp.inf
    for _ in range(150):
        a = rng.uniform(-4, 4); b = rng.choice([0.02, 0.3, 1.0, 3.0])
        cs, ct, cm = coeffs(n, mp.e ** (a + b)), coeffs(n, mp.e ** (a - b)), coeffs(n, mp.e ** a)
        d0 = cm[0] - (cs[0] + ct[0]) / 2
        d = [cm[m] - mp.sqrt(cs[m] * ct[m]) for m in range(1, len(cm))]
        r1 = min(r1, d0 / sum(d))
        r2 = min(r2, (d0 + sum((-1) ** (m + 1) * d[m] for m in range(len(d)))) / (d0 + sum(d)))
    print(f"n={n}: min delta_0 / sum delta_m = {mp.nstr(r1, 5)};   min W(-1)/(delta_0+sum delta_m) = {mp.nstr(r2, 5)}")
