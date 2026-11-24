"""E8. Operator form of the Cauchy determinant inequality (CD).

In the Drury-Arveson model, with M = span of kernel functions and T_a = P_M M_{z_a}|_M, CD reads
    |det(id - Phi)|  <=  det( I - Phi^n(I) ),      Phi(X) = sum_a T_a X T_a^*   on  B(M), dim M = n,
where Phi is completely positive with rank-one defect  I - Phi(I) = e e^*.
Question: does this hold for ARBITRARY (non-commuting) T with rank-one defect?  (r = number of Kraus operators)
"""
import numpy as np
rng = np.random.default_rng(0)

def random_tuple(n, r, enorm):
    e = rng.normal(size=n) + 1j * rng.normal(size=n); e *= enorm / np.linalg.norm(e)
    G = rng.normal(size=(n * r, n * r)) + 1j * rng.normal(size=(n * r, n * r))
    Q, _ = np.linalg.qr(G)
    W = Q[:n, :]                                    # n x nr, W W^* = I
    w, U = np.linalg.eigh(np.eye(n) - np.outer(e, e.conj()))
    R = (U * np.sqrt(np.clip(w, 0, None))) @ U.conj().T
    return [R @ W[:, a * n:(a + 1) * n] for a in range(r)], e

def sides(T, n):
    L = sum(np.kron(t, t.conj()) for t in T)
    lhs = abs(np.linalg.det(np.eye(n * n) - L))
    X = np.eye(n, dtype=complex)
    for _ in range(n): X = sum(t @ X @ t.conj().T for t in T)
    return lhs, np.real(np.linalg.det(np.eye(n) - X))

for r in (1, 2, 3):
    for n in (2, 3, 4, 5):
        viol = 0; worst = 0; N = 4000
        for _ in range(N):
            T, e = random_tuple(n, r, rng.choice([1.0, 0.9, 0.5]))
            l, rr = sides(T, n)
            if l > rr * (1 + 1e-8) + 1e-13: viol += 1; worst = max(worst, l / max(rr, 1e-300))
        print(f"r={r} n={n}: violations {viol}/{N}" + (f"  worst lhs/rhs={worst:.3g}" if viol else ""))
