"""E7. Viability test of the analytic reduction 'unequal diagonal -> equal diagonal certificate'.

For each pair (i,j) use the equal-diagonal (Cohn-Kumar Hermite) certificate with parameter tau_ij = sqrt(d_i d_j):
    -log|1 - tau z| >= c_0(tau) + sum_{m>=1} c_m(tau) Re z^m      on the closed unit disc.
Then  sum_{i!=j} -log|1-a_ij| >= sum_{i!=j} c_0(tau_ij) - sum_m T_m,
where T_m = min trace of a PSD matrix whose off-diagonal entries are c_m(tau_ij)  (Schur product theorem).
Question: is this >= -sum_i log F_n(d_i)  (the theorem)?  Also report: is c_0(e^u) concave, sign of margin.
"""
import numpy as np, cvxpy as cp

def coeffs(n, tau):
    """Chebyshev coefficients of the Hermite interpolant of g(theta) = -log|1 - tau e^{i theta}| at the
    nontrivial n-th roots of unity (double contact).  Degree n-2 (n odd) or n-1 (n even)."""
    D = n - 2 if n % 2 else n - 1
    m = np.arange(D + 1); rows = []; rhs = []
    q = lambda t: 1 + tau * tau - 2 * tau * np.cos(t)
    for k in range(1, n // 2 + 1):
        t = 2 * np.pi * k / n
        rows.append(np.cos(m * t)); rhs.append(-0.5 * np.log(q(t)))
        if abs(t - np.pi) > 1e-12:
            rows.append(-m * np.sin(m * t)); rhs.append(-tau * np.sin(t) / q(t))
        else:
            rows.append(-m * m * np.cos(m * t)); rhs.append(tau / (1 + tau) ** 2)
    return np.linalg.solve(np.array(rows), np.array(rhs))

def min_trace(M):
    n = len(M); x = cp.Variable(n)
    off = M - np.diag(np.diag(M))
    p = cp.Problem(cp.Minimize(cp.sum(x)), [off + cp.diag(x) >> 0]); p.solve(solver=cp.CLARABEL)
    return p.value

def bound(d):
    d = np.array(d, float); n = len(d); tau = np.sqrt(np.outer(d, d))
    c = np.array([[coeffs(n, tau[i, j]) for j in range(n)] for i in range(n)])   # n x n x (D+1)
    off = ~np.eye(n, dtype=bool)
    val = c[:, :, 0][off].sum() - sum(min_trace(c[:, :, m]) for m in range(1, c.shape[2]))
    return val, -np.sum(np.log(sum(d ** k for k in range(n)))), c

rng = np.random.default_rng(5)
print("sanity, equal diagonal (margin should be 0):")
for n, r in ((3, .5), (4, 1.), (5, 2.)):
    v, t, c = bound([r] * n); print(f"  n={n} d={r}: bound={v:.6f} target={t:.6f} margin={v - t:+.2e}  min coef={c[0,1,1:].min():+.2e}")
print("unequal diagonal:")
worst = {}
for n in (3, 4, 5, 6):
    for regime, lo, hi in (("<1", .05, 1.), (">1", 1., 5.), ("across", .1, 5.)):
        ms = []
        for _ in range(40):
            v, t, c = bound(rng.uniform(lo, hi, n)); ms.append(v - t)
        print(f"  n={n} diag {regime:6s}: min margin over 40 random diagonals = {min(ms):+.4f}   (max {max(ms):+.4f})")
print("concavity of c_0(e^u): second differences (should be <= 0)")
for n in (3, 4, 5, 6):
    u = np.linspace(-3, 3, 121); c0 = np.array([coeffs(n, np.exp(x))[0] for x in u])
    print(f"  n={n}: max second difference = {np.diff(c0, 2).max():+.2e}")
