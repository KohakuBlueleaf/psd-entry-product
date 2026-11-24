"""E10. Weighted rank-one ("Turan-type") inequality (W_r).

Sphere averaging:  for Gram vectors v_i in C^r and e uniform on the unit sphere, x_i = <v_i, e>,
    s_m(A) = N_m E|p_m(x)|^2,   t_m(A) = N_m E sum_i |x_i|^{2m},   N_m = binom(m+r-1, m),
(p_m = power sum).  Hence the main inequality (all a_ii < 1) follows from the scalar inequality
    (W_r)   sum_{m>=1} (N_m/m) |p_m(x)|^2  >=  sum_{m: n|m} (n/m) N_m sum_i |x_i|^{2m}     for all x in D^n,
for some r >= rank(A).  r = 1 is the rank-one case of the theorem.  Test (W_r) by adversarial minimisation.
"""
import numpy as np, sys
from scipy.optimize import minimize
from scipy.special import gammaln

def gap(p, n, r, M=400, rmax=0.9):
    rad = rmax / (1 + np.exp(-p[:n])); x = rad * np.exp(1j * p[n:])
    m = np.arange(1, M + 1)
    logN = gammaln(m + r) - gammaln(m + 1) - gammaln(r)
    pw = x[None, :] ** m[:, None]
    L = np.sum(np.exp(logN) / m * np.abs(pw.sum(1)) ** 2)
    mult = (m % n == 0)
    R = np.sum((np.exp(logN) * n / m * (np.abs(pw) ** 2).sum(1))[mult])
    return L - R, R

rng = np.random.default_rng(0)
for n in (2, 3, 4, 5):
    for r in (1, 2, 3, n, n + 3):
        best = np.inf; bx = None
        for _ in range(30):
            p0 = np.concatenate([rng.normal(size=n) * 2, rng.uniform(0, 2 * np.pi, n)])
            res = minimize(lambda p: gap(p, n, r)[0], p0, method="Nelder-Mead", options={"maxiter": 3000, "xatol": 1e-8, "fatol": 1e-13})
            if res.fun < best: best, bx = res.fun, res.x
        g, R = gap(bx, n, r)
        rad = 0.9 / (1 + np.exp(-bx[:n]))
        print(f"n={n} r={r}: min(L-R) = {best:+.3e}  (R there = {R:.3e}, radii = {np.round(rad, 3)})")
