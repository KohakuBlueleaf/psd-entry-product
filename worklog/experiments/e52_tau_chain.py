"""E52 (evidence only, tiny).  End-to-end check of the tau-kernel chain on random complex PSD matrices with diagonal in (0,1):
   lhs = sum_{i!=j} -log|1-a_ij|  >=  mid = sum_{i!=j} [ (Gam0_i+Gam0_j)/2 + sum_m K_m(p_i,p_j) Re c_ij^m ]  >=  rhs = -sum_i log F_n(d_i)."""
import mpmath as mp, numpy as np
import e20_closed_form as e
from e51_tau_kernel import K
mp.mp.dps = 20
rng = np.random.default_rng(3)
for n in (3, 4, 5):
    for trial in range(4):
        r = rng.integers(1, n + 1)
        V = rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))
        A = V @ V.conj().T; d0 = np.real(np.diag(A)); tgt = rng.uniform(0.05, 0.97, n)
        s = np.sqrt(tgt / d0); A = A * np.outer(s, s)
        p = [-mp.log(mp.mpf(float(x))) for x in tgt]
        lhs = mid = mp.mpf(0)
        for i in range(n):
            for j in range(n):
                if i == j: continue
                a = complex(A[i, j]); c = a / np.sqrt(tgt[i] * tgt[j])
                lhs += -mp.log(abs(1 - a))
                mid += (e.Gam(n, 0, p[i]) + e.Gam(n, 0, p[j])) / 2 + sum(K(n, m, p[i], p[j]) * (c ** m).real for m in range(1, n - 1))
        rhs = -sum(mp.log(sum(mp.mpf(float(x)) ** k for k in range(n))) for x in tgt)
        print(f"n={n} rank={r}: lhs-mid = {mp.nstr(lhs - mid, 5):>10}   mid-rhs = {mp.nstr(mid - rhs, 5):>10}   ok={lhs >= mid >= rhs}")
