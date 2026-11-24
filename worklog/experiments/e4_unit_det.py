"""E4. Candidate inequalities with det F_n(A), F_n(z)=1+...+z^(n-1), by regime of the diagonal.
 (U)  prod_{i!=j}|1-a_ij| <= det F_n(A)            -- tested for unit diagonal, diag<=1, diag>=1, any
 Hadamard then gives det F_n(A) <= prod F_n(a_ii).
"""
import numpy as np
rng = np.random.default_rng(3)
def rand(n, lo, hi):
    r = rng.integers(1, n + 1)
    B = rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))
    A = B @ B.conj().T
    s = np.sqrt(rng.uniform(lo, hi, size=n) / np.real(np.diag(A)))
    return A * np.outer(s, s)
for name, lo, hi in (("unit", 1, 1), ("diag in (0,1)", .05, 1), ("diag in (1,3)", 1, 3), ("diag in (.2,3)", .2, 3)):
    for n in (2, 3, 4, 5):
        viol = 0; N = 20000; worst = 0
        for _ in range(N):
            A = rand(n, lo, hi)
            off = ~np.eye(n, dtype=bool)
            l = np.prod(np.abs(1 - A[off])); r = np.real(np.linalg.det(sum(A ** k for k in range(n))))
            if l > r * (1 + 1e-9) + 1e-12: viol += 1; worst = max(worst, l / max(r, 1e-300))
        print(f"(U) {name:15s} n={n}: violations {viol}/{N}" + (f"  worst ratio {worst:.3g}" if viol else ""))
