"""E50 (evidence only).  Split a = a^S + a^R  (u = k_m(p) e^{-mb} + rho_m):  second differences d2a^S (explicit part, Poisson-smoothed diagonal)
and d2a^R.  Report  max_j ( - d2a^R_j / d2a^S_j )  (must be < 1 for QC) and min_j d2a^S_j sign."""
import mpmath as mp, sys
from multiprocessing import Pool
from e31_criterion_v2 import sigma
from e47_qc_wide import chi
def job(args):
    n, p, dq = args; mp.mp.dps = 50 + int(1.0 * n * (float(p) + float(dq)))
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2; b = (q - p) / 2
    J = int(min(6000, 80 / (n * float(p)) + 8))
    uS = [chi(n, 0, p)] + [mp.e ** (-m * al) * chi(n, m, p) for m in range(1, n - 1)] + [mp.mpf(0)] * 3
    u = [chi(n, 0, p)] + [mp.e ** (-m * al) * chi(n, m, p) * mp.sqrt(sigma(n, m, q, J) / sigma(n, m, p, J)) for m in range(1, n - 1)] + [mp.mpf(0)] * 3
    def acoef(u):
        return [2 * (mp.sinh(al) - u[0] * mp.cosh(al) + u[1])] + [u[m - 1] + u[m + 1] - 2 * mp.cosh(al) * u[m] for m in range(1, n)] + [mp.mpf(0)] * 2
    a, aS = acoef(u), acoef(uS)
    d2 = lambda a: [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(n)]
    D, DS = d2(a), d2(aS)
    ratios = [(-(D[j] - DS[j]) / DS[j], j) for j in range(n) if DS[j] > 0]
    return n, float(p), float(q), min(DS) / aS[0], max(ratios) if ratios else (None, None), min(D[j] / DS[j] for j in range(n) if DS[j] > 0)
if __name__ == "__main__":
    ns = [5, 8, 16, 32]
    jobs = [(n, p, dq) for n in ns for p in ('0.03', '0.1', '0.3', '0.7', '1.5', '3') for dq in ('0.0005', '0.01', '0.1', '0.5', '2', '6')]
    with Pool(60) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in ns:
        rows = [o for o in out if o[0] == n]
        w = max(rows, key=lambda o: o[4][0])
        print(f"n={n}: min d2a^S/a^S_0 = {mp.nstr(min(o[3] for o in rows), 3)} (S-part convex in all cases: {all(o[3] >= 0 for o in rows)});"
              f"  max_j (-d2a^R/d2a^S) = {mp.nstr(w[4][0], 4)} at (p,q,j)=({w[1]},{w[2]},{w[4][1]});  min_j d2a/d2a^S = {mp.nstr(min(o[5] for o in rows), 4)}")
