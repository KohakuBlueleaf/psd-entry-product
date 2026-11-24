"""E40 (evidence only, small).  Arithmetic-mean kernel: replace sqrt(Gam_m(p)Gam_m(q)) by Gam_m((p+q)/2).
Then the pair inequality is the proved diagonal case, and what is needed is the n-point statement
  T(A) = sum_{i!=j} [Gam_0(a_ij) + sum_m Gam_m(a_ij) Re c_ij^m] - sum_i [(n-1)Gam_0(p_i) - sum_m Gam_m(p_i)] >= 0
(a_ij=(p_i+p_j)/2, c_ij = A_ij/sqrt(d_i d_j)).  Gam via its power series in s=e^{-p} (p >= 0.05)."""
import numpy as np
from scipy.optimize import minimize
J = np.arange(1, 4001)
def Gm(n, m, p):
    s = np.exp(-p); N = n - m
    def term(e): return np.where(e > 0, s ** e / np.maximum(e, 1), 0.0)
    return float(np.sum(J * (term((J - 1) * n + m) - term((J + 1) * n - m) - N * (term(J * n - 1) - term(J * n + 1)))) * (0.5 if m == 0 else 1.0))
def T(n, p, V):
    C = V @ V.conj().T
    d = np.sqrt(np.real(np.diag(C))); C = C / np.outer(d, d)
    tot = 0.0
    for i in range(n):
        tot -= (n - 1) * Gm(n, 0, p[i]) - sum(Gm(n, m, p[i]) for m in range(1, n - 1))
        for j in range(n):
            if i == j: continue
            a = (p[i] + p[j]) / 2
            tot += Gm(n, 0, a) + sum(Gm(n, m, a) * (C[i, j] ** m).real for m in range(1, n - 1))
    return tot
def run(n, r, trials, seed):
    rng = np.random.default_rng(seed); best = (np.inf, None)
    def f(x):
        p = np.abs(x[:n]) + 0.05; V = (x[n:n + n * r] + 1j * x[n + n * r:]).reshape(n, r)
        return T(n, p, V)
    for t in range(trials):
        x0 = np.concatenate([rng.exponential(0.5, n), rng.normal(size=2 * n * r)])
        res = minimize(f, x0, method='Nelder-Mead', options={'maxiter': 1500, 'xatol': 1e-7, 'fatol': 1e-13})
        if res.fun < best[0]: best = (res.fun, res.x)
    return best
if __name__ == "__main__":
    # sanity: equal p, roots of unity -> T = 0
    n = 4; V = np.exp(2j * np.pi * np.arange(n) / n).reshape(n, 1); print("sanity (should be ~0):", T(n, np.full(n, 0.4), V))
    for n, r in ((3, 1), (3, 2), (4, 1), (4, 2), (5, 1), (5, 2)):
        v, x = run(n, r, 8, 1)
        print(f"n={n} rank<={r}: min T = {v:.3e}   p = {np.round(np.abs(x[:n]) + 0.05, 4)}", flush=True)
