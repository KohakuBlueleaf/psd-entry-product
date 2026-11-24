"""E2. Equal diagonal a_ii = rho.  Write a_ij = rho*c_ij with C a correlation matrix (|c_ij|<=1).
Delsarte/Yudin-type certificate: find  h(z) = c_0 + sum_{m=1}^{n-1} c_m Re z^m,  c_m >= 0 (m>=1),
with h <= g_rho := -log|1 - rho z| on |z| = 1.  Since g_rho is superharmonic and h harmonic on the
disc, h <= g_rho holds on the whole disc, and by the Schur product theorem sum_{i,j} Re c_ij^m >= 0, so
    sum_{i!=j} g_rho(c_ij) >= n(n-1) c_0 - n sum_{m>=1} c_m.
The LP maximises this bound; target is -n log F_n(rho).
"""
import numpy as np
from scipy.optimize import linprog

def lp(n, rho, grid=4001, maxdeg=None):
    deg = (n - 1) if maxdeg is None else maxdeg
    th = np.linspace(1e-6, 2 * np.pi - 1e-6, grid)
    th = np.concatenate([th, 2 * np.pi * np.arange(1, n) / n])
    g = -np.log(np.abs(1 - rho * np.exp(1j * th)))
    M = np.cos(np.outer(th, np.arange(deg + 1)))
    c = -np.concatenate([[n * (n - 1)], -n * np.ones(deg)])
    res = linprog(c, A_ub=M, b_ub=g, bounds=[(None, None)] + [(0, None)] * deg, method="highs")
    return -res.fun, res.x

for n in (2, 3, 4, 5, 6, 8, 12):
    for rho in (0.3, 0.9, 1.0, 1.7):
        val, coef = lp(n, rho)
        target = -n * np.log(sum(rho ** k for k in range(n)))
        print(f"n={n:2d} rho={rho}: LP bound={val:.6f} target={target:.6f} gap={target - val:.1e} "
              f"min coef(m>=1)={coef[1:].min():.2e}")
