"""E24. For which n does the Fejer (convex coefficients) criterion for D_{p,q} hold?  Scan p ~ q (the worst regime)."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
def job(args):
    n, p, dq = args; mp.mp.dps = 120
    q = p + dq; k, k0m1 = e.k, e.k0m1
    Gam = lambda m, x: mp.quad(lambda w: k(n, m, w), [x, x + mp.mpf(1) / 4, x + 1, x + 3, x + 8, x + 20, x + 60, x + 150, x + 400])
    Gp1, Gq1, Gp2, Gq2 = Gam(1, p), Gam(1, q), Gam(2, p), Gam(2, q)
    d0 = k0m1(n, q) - k0m1(n, p)
    d1 = mp.sqrt(Gp1 * Gq1) * (k(n, 1, q) / Gq1 - k(n, 1, p) / Gp1)
    d2 = mp.sqrt(Gp2 * Gq2) * (k(n, 2, q) / Gq2 - k(n, 2, p) / Gp2)
    return n, float(p), (2 * d0 - 2 * d1 + d2) / (2 * d0)
if __name__ == "__main__":
    ps = [mp.mpf(x) / 20 for x in range(0, 61)]
    jobs = [(n, p, mp.mpf('0.01')) for n in range(12, 23) for p in ps]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in range(12, 23):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[2])
        print(f"n={n}: min first second-difference (relative) = {mp.nstr(w[2], 4)} at p={w[1]:.2f}")
