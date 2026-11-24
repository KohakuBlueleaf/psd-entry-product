"""E22. Fejer-type criterion.  2 dL/db = d_0 + sum_{m>=1} d_m cos(m theta) with
   d_0 = kappa0(q) - kappa0(p),   d_m = sqrt(Gamma_m(p)Gamma_m(q)) (r_m(q) - r_m(p)).
If the sequence (2 d_0, d_1, d_2, ..., d_{n-2}, 0, 0, ...) is convex and nonincreasing, the cosine polynomial is a
nonnegative combination of Fejer kernels, hence >= 0.  Test convexity (second differences >= 0)."""
import mpmath as mp
from multiprocessing import Pool
from e20_closed_form import k, k0m1, Gam

def job(args):
    n, p, q = args
    mp.mp.dps = 30
    Gp = [Gam(n, m, p) for m in range(1, n - 1)]; Gq = [Gam(n, m, q) for m in range(1, n - 1)]
    a = [2 * (k0m1(n, q) - k0m1(n, p))] + [mp.sqrt(Gp[i] * Gq[i]) * (k(n, i + 1, q) / Gq[i] - k(n, i + 1, p) / Gp[i]) for i in range(n - 2)] + [mp.mpf(0), mp.mpf(0)]
    sd = [a[j - 1] - 2 * a[j] + a[j + 1] for j in range(1, len(a) - 1)]
    fd = [a[j] - a[j + 1] for j in range(len(a) - 1)]
    return n, float(p), float(q), min(sd) / a[0], min(fd) / a[0], [mp.nstr(x / a[0], 3) for x in sd[:4]]

if __name__ == "__main__":
    pairs = [(0, 0.05), (0, 0.5), (0, 2), (0, 6), (0.2, 0.3), (0.2, 1.5), (0.7, 0.75), (0.7, 3), (1.5, 1.6), (1.5, 4), (3, 3.1), (3, 7), (5, 5.1), (5, 12)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (4, 5, 6, 7, 8, 11, 14, 20) for p, q in pairs]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (4, 5, 6, 7, 8, 11, 14, 20):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3]); f = min(rows, key=lambda o: o[4])
        print(f"n={n:2d}: min second difference / a_0 = {mp.nstr(w[3], 4)} at (p,q)=({w[1]},{w[2]}), first few {w[5]};  min first difference / a_0 = {mp.nstr(f[4], 4)}")
