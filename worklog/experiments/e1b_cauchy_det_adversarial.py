"""E1b. Adversarial search for a counterexample to the Cauchy determinant inequality (CD):
minimise  log det F_n(A) - log det C(A) - sum log|1-a_ij|   (conjecturally >= 0, = 0 at rank one).
Uses mpmath-free float64 with slogdet; restricted to moderately conditioned regions.
"""
import numpy as np, sys
from scipy.optimize import minimize
from multiprocessing import Pool

def build(p, n, r):
    B = (p[:n * r] + 1j * p[n * r:2 * n * r]).reshape(n, r)
    A = B @ B.conj().T
    d = np.real(np.diag(A)).copy()
    t = 0.98 / (1 + np.exp(-p[2 * n * r:])) + 0.01          # target diagonal in (0.01, 0.99)
    s = np.sqrt(t / d)
    return A * np.outer(s, s)

def obj(p, n, r):
    A = build(p, n, r)
    C = 1 / (1 - A)
    Fm = sum(A ** k for k in range(n))
    s1, l1 = np.linalg.slogdet(Fm); s2, l2 = np.linalg.slogdet(C)
    if s1.real <= 0 or s2.real <= 0 or l1 < -25 or l2 < -25:   # avoid numerically degenerate dets
        return 10.0
    return l1 - l2 - np.sum(np.log(np.abs(1 - A)))

def run(args):
    n, r, seed = args
    rng = np.random.default_rng(seed)
    best = np.inf
    for _ in range(6):
        p0 = rng.normal(size=2 * n * r + n)
        res = minimize(obj, p0, args=(n, r), method="Nelder-Mead",
                       options={"maxiter": 4000, "xatol": 1e-9, "fatol": 1e-12})
        best = min(best, res.fun)
    return n, r, best

if __name__ == "__main__":
    jobs = [(n, r, s) for n in range(2, 7) for r in range(2, n + 1) for s in range(8)]
    with Pool(60) as pool:
        out = pool.map(run, jobs)
    agg = {}
    for n, r, b in out:
        agg[(n, r)] = min(agg.get((n, r), np.inf), b)
    for k in sorted(agg):
        print(f"n={k[0]} rank<={k[1]}: min of log-ratio found = {agg[k]:.3e}")
