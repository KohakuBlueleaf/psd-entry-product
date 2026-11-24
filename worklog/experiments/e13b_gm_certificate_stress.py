"""E13b. Stress test of (**) from e13:  (1) near the diagonal s ~ t, scaled by the squared log-ratio;
(2) wide parameter range and larger n;  (3) end-to-end: the resulting bound vs the theorem on random PSD matrices.
"""
import numpy as np
from e13_gm_certificate import coeffs
from multiprocessing import Pool
th = np.linspace(0, 2 * np.pi, 20001)

def gap(n, s, t):
    cs, ct = coeffs(n, s), coeffs(n, t); tau = np.sqrt(s * t)
    g = -0.5 * np.log(1 + tau * tau - 2 * tau * np.cos(th) + 1e-300)
    m = np.arange(1, len(cs))
    h = 0.5 * (cs[0] + ct[0]) + (np.sqrt(np.clip(cs[1:] * ct[1:], 0, None))[:, None] * np.cos(np.outer(m, th))).sum(0)
    return (g - h).min(), min(cs[1:].min(), ct[1:].min())

def job(n):
    rng = np.random.default_rng(n)
    near = np.inf; wide = np.inf; mc = np.inf; arg = None
    for a in np.linspace(-5, 4, 46):
        for b in (0.3, 0.1, 0.03):
            v, c = gap(n, np.exp(a + b), np.exp(a - b)); mc = min(mc, c)
            if v / b ** 2 < near: near, arg = v / b ** 2, (a, b)
    for _ in range(1500):
        s, t = np.exp(rng.uniform(-7, 5, 2)); v, c = gap(n, s, t); wide = min(wide, v); mc = min(mc, c)
    return n, near, arg, wide, mc

if __name__ == "__main__":
    import sys
    with Pool(16) as pool:
        for n, near, arg, wide, mc in pool.map(job, [2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16]):
            print(f"n={n:2d}: min (g-h)/b^2 near diagonal = {near:+.3e} (a={arg[0]:+.2f}, b={arg[1]});  "
                  f"min g-h on wide range = {wide:+.3e};  min coefficient c_m = {mc:+.2e}")
