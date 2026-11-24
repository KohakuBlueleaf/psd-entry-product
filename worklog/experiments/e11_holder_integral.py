"""E11. Integral (finite beta) version of the generalized Hoelder form, rank-one (phases) model:
    Z_beta(rho) = E_u prod_{i<j} |1 - rho_i rho_j u_i conj(u_j)|^{2 beta},   u uniform on the torus.
Question: is  Z_beta(rho_1..rho_n) <= prod_i Z_beta(rho_i,...,rho_i)^{1/n} ?
(beta -> infinity recovers the rank-one case of the theorem; a structural 'chessboard' proof would give all beta.)
Exact up to quadrature: the integrand is a trigonometric polynomial for integer beta.
"""
import numpy as np, itertools
def Z(rho, beta, G):
    n = len(rho); th = 2 * np.pi * np.arange(G) / G
    grids = np.meshgrid(*([th] * (n - 1)), indexing="ij")
    ang = [np.zeros_like(grids[0])] + list(grids)
    logw = np.zeros_like(grids[0])
    for i in range(n):
        for j in range(i + 1, n):
            t = rho[i] * rho[j]
            logw += beta * np.log(1 + t * t - 2 * t * np.cos(ang[i] - ang[j]) + 1e-300)
    return np.exp(logw).mean()
rng = np.random.default_rng(0)
for n, G in ((2, 512), (3, 256), (4, 64)):
    for beta in (0.5, 1, 2, 4, -0.25):
        worst = -np.inf; arg = None
        for _ in range(200):
            rho = rng.uniform(0.1, 0.97, n) if beta < 0 else rng.uniform(0.1, rng.choice([0.95, 2.0]), n)
            lhs = np.log(Z(rho, beta, G)); rhs = np.mean([np.log(Z(np.full(n, r), beta, G)) for r in rho])
            if lhs - rhs > worst: worst, arg = lhs - rhs, rho
        print(f"n={n} beta={beta:5}: max of log Z(rho) - mean_i log Z(rho_i 1) = {worst:+.3e}  at rho={np.round(arg, 3)}")
