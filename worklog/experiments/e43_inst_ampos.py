"""E43 (evidence only, small; everything closed form).  Instantaneous arithmetic-mean positivity:
   F(p, C) = sum_{i,j} Pihat_{(p_i+p_j)/2}(c_ij) - (n/2) sum_i k_0(p_i)  >= 0 ?
   Pihat_x(c) = k_0(x)/2 + sum_{m=1}^{n-2} k_m(x) Re c^m,   k_m(x) = (sinh((n-m)x) - (n-m) sinh x)/(cosh(nx)-1).
If true for all p_i >= 0 and all correlation matrices C, integrating over a common shift gives (AMpos), hence the main theorem."""
import numpy as np, sys
from scipy.optimize import minimize
from multiprocessing import Pool
def kk(n, m, x):
    x = np.maximum(x, 1e-9)
    # stable form: multiply numerator and denominator by 2 e^{-n x}
    N = n - m
    num = np.exp(-m * x) - np.exp(-(2 * n - m) * x) - N * (np.exp(-(n - 1) * x) - np.exp(-(n + 1) * x))
    return num / (1 - np.exp(-n * x)) ** 2
def F(n, p, V):
    C = V @ V.conj().T
    d = np.sqrt(np.real(np.diag(C))); C = C / np.outer(d, d)
    A = (p[:, None] + p[None, :]) / 2
    tot = np.sum(kk(n, 0, A)) / 2 - n / 2 * np.sum(kk(n, 0, p))
    Cm = np.ones_like(C)
    for m in range(1, n - 1):
        Cm = Cm * C
        tot += np.sum(kk(n, m, A) * Cm.real)
    return tot
def job(a):
    n, r, seed = a
    rng = np.random.default_rng(seed); best = (np.inf, None)
    def f(x):
        p = np.abs(x[:n]) + 1e-4; V = (x[n:n + n * r] + 1j * x[n + n * r:]).reshape(n, r)
        return F(n, p, V) / n
    for t in range(40):
        scale = rng.choice([0.05, 0.3, 1.0, 3.0])
        x0 = np.concatenate([rng.exponential(scale, n), rng.normal(size=2 * n * r)])
        res = minimize(f, x0, method='BFGS', options={'maxiter': 3000, 'gtol': 1e-12})
        res = minimize(f, res.x, method='Nelder-Mead', options={'maxiter': 4000, 'xatol': 1e-10, 'fatol': 1e-15})
        if res.fun < best[0]: best = (res.fun, res.x)
    return n, r, seed, best[0], np.round(np.sort(np.abs(best[1][:n]) + 1e-4), 4)
if __name__ == "__main__":
    n = 4; V = np.exp(2j * np.pi * np.arange(n) / n).reshape(n, 1); print("sanity (should be ~0):", F(n, np.full(n, 0.4), V))
    jobs = [(n, r, s) for n in (3, 4, 5, 6, 8) for r in (1, 2, 3) for s in (1, 2)]
    with Pool(30) as pool:
        out = pool.map(job, jobs, chunksize=1)
    for o in out: print(f"n={o[0]} rank<={o[1]} seed={o[2]}: min F/n = {o[3]:.3e}  p={o[4]}")
