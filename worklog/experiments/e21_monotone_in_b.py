"""E21. With p = alpha - b, q = alpha + b:  is  L(theta; p, q) = g_alpha - R_{p,q}  nondecreasing in b for every theta?
   2 dL/db = [kappa0(q) - kappa0(p)] + sum_m cos(m theta) sqrt(Gamma_m(p) Gamma_m(q)) (r_m(q) - r_m(p)),   r_m = k_m/Gamma_m.
If yes, (**) follows from the equal-parameter case L(b=0) = g_alpha - h_alpha >= 0.
Also test:  is kappa_w(theta) = (1/2)[P_w(theta)(1 - rho_n(w) Fej_n(theta)) - 1] increasing in w?"""
import mpmath as mp
from multiprocessing import Pool
from e20_closed_form import k, k0m1, Gam

def job(args):
    n, p, q = args
    mp.mp.dps = 30
    Gp = [Gam(n, m, p) for m in range(1, n - 1)]; Gq = [Gam(n, m, q) for m in range(1, n - 1)]
    d0 = k0m1(n, q) - k0m1(n, p)
    d = [mp.sqrt(Gp[i] * Gq[i]) * (k(n, i + 1, q) / Gq[i] - k(n, i + 1, p) / Gp[i]) for i in range(n - 2)]
    vals = [(d0 + sum(d[i] * mp.cos((i + 1) * mp.pi * j / (8 * n)) for i in range(n - 2)), j / (8 * n)) for j in range(8 * n + 1)]
    v, th = min(vals)
    return n, float(p), float(q), v / (d0 + sum(abs(x) for x in d)), th, min(d) >= 0

if __name__ == "__main__":
    pairs = [(0, 0.05), (0, 0.5), (0, 2), (0.2, 0.3), (0.2, 1.5), (0.7, 0.75), (0.7, 3), (1.5, 1.6), (1.5, 4), (3, 3.1), (3, 7)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (4, 5, 6, 7, 8, 11, 14) for p, q in pairs]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (4, 5, 6, 7, 8, 11, 14):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n:2d}: min normalised dL/db = {mp.nstr(w[3], 5)} at p={w[1]}, q={w[2]}, theta/pi={w[4]:.3f};  all coefficients >= 0: {all(o[5] for o in rows)}")
