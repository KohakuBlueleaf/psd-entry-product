"""E26. A LINEAR pair certificate (no square roots).  For p <= q, b = (q-p)/2, alpha = (p+q)/2 use the kernel
    K_m(p,q) = e^{-m|p-q|/2} Gamma_m(min(p,q)),
positive definite as soon as x -> e^{m x} Gamma_m(x) is nondecreasing, with diagonal Gamma_m(p).  Then
    R(theta) = (Gamma_0(p)+Gamma_0(q))/2 + sum_m e^{-m b} Gamma_m(p) cos(m theta)
             = harmonic extension of h_p to radius e^{-b}, with the constant term averaged,
and  g_alpha - R = E_p(e^{-b} e^{i theta}) - (Gamma_0(q) - Gamma_0(p))/2 ,   E_p = g_p - h_p >= 0.
Test:  (a) is e^{m x} Gamma_m(x) nondecreasing (i.e. m Gamma_m >= k_m)?   (b) is g_alpha - R >= 0 for all theta?"""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def job(args):
    n, p, q = args; mp.mp.dps = 40
    k = e.k; Gam = e.Gam
    b = (q - p) / 2; al = (p + q) / 2; tau = mp.e ** (-al)
    Gp = [Gam(n, m, p) for m in range(n - 1)]; G0q = Gam(n, 0, q)
    mono = min(m * Gp[m] - k(n, m, p) for m in range(1, n - 1))
    best = mp.inf; arg = None
    for j in range(0, 8 * n + 1):
        th = mp.pi * j / (8 * n)
        gv = -mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 if not (j == 0 and al == 0) else mp.inf
        v = gv - (Gp[0] + G0q) / 2 - sum(mp.e ** (-m * b) * Gp[m] * mp.cos(m * th) for m in range(1, n - 1))
        if v < best: best, arg = v, j / (8 * n)
    return n, float(p), float(q), best / ((G0q - Gp[0]) / 2), arg, mono >= 0

if __name__ == "__main__":
    pairs = [(0, 0.02), (0, 0.3), (0, 1.5), (0, 5), (0.1, 0.12), (0.1, 0.6), (0.4, 0.45), (0.4, 2), (0.8, 0.82), (0.8, 1.6), (1.5, 1.55), (1.5, 4), (3, 3.05), (3, 6)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (3, 4, 5, 6, 8, 12, 16, 20, 30) for p, q in pairs]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (3, 4, 5, 6, 8, 12, 16, 20, 30):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n:2d}: min of (g-R)/((Gamma_0(q)-Gamma_0(p))/2) = {mp.nstr(w[3], 5)} at p={w[1]}, q={w[2]}, theta/pi={w[4]:.3f};  e^(mx)Gamma_m nondecreasing: {all(o[5] for o in rows)}")
