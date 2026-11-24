"""E1. Test the 'Cauchy determinant inequality' candidate:

    det[1/(1-a_ij)] * prod_{i,j}|1-a_ij|  <=  det[F_n(a_ij)],   F_n(z) = 1+z+...+z^(n-1),

for PSD A with a_ii < 1.  Equality for rank one (Cauchy determinant).  Combined with Oppenheim
    det[1/(1-a_ij)] >= det[F_n(a_ij)] * prod_i 1/(1-a_ii^n)
it would give the main inequality when all a_ii < 1.
"""
import numpy as np
rng = np.random.default_rng(1)

def rand_psd(n, r, maxdiag):
    B = rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))
    A = B @ B.conj().T
    d = np.real(np.diag(A))
    s = np.sqrt(rng.uniform(0.02, maxdiag, size=n) / d)   # random diagonal in (0, maxdiag)
    return A * np.outer(s, s)

def F(A, n):
    return sum(A ** k for k in range(n))

for n in range(2, 8):
    worst = -np.inf; viol = 0; N = 20000; worst_opp = np.inf
    for _ in range(N):
        r = rng.integers(1, n + 1)
        A = rand_psd(n, r, rng.choice([0.3, 0.7, 0.95, 0.999]))
        C = 1 / (1 - A)
        lhs = np.real(np.linalg.det(C)) * np.prod(np.abs(1 - A))
        rhs = np.real(np.linalg.det(F(A, n)))
        main_l = np.prod(np.abs(1 - A)); main_r = np.prod(1 - np.real(np.diag(A)) ** n)
        scale = main_r
        gap = (lhs - rhs) / scale
        worst = max(worst, gap)
        if lhs > rhs + 1e-9 * scale: viol += 1
        # Oppenheim step, as ratio (should be >= 1)
    print(f"n={n}: violations of CD {viol}/{N}, max (lhs-rhs)/prod(1-a_ii^n) = {worst:.3e}")
