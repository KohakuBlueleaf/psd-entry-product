"""E47 (evidence only).  Wide check of
 (QC): a_0 = 2(sinh al - u_0 cosh al + u_1), a_m = u_{m-1}+u_{m+1}-2cosh(al) u_m (1<=m<=n-1), a_m = 0 (m>=n) is convex,
 (TC): f(0)=a_0/(2n), f(m)=a_m/(2(n-m)) is nonneg, nonincreasing, convex on 0..n-1,
 with u_m = e^{-m al} chi_m(p) sqrt(sigma_m(q)/sigma_m(p)), u_0 = chi_0(p), u_{n-1}=u_n=0.   sigma via power series (p>=0.03)."""
import mpmath as mp, sys
from multiprocessing import Pool
from e31_criterion_v2 import sigma
def chi(n, m, x):
    t = mp.e ** (-x); N = n - m
    return (1 - t ** (2 * N) - N * t ** (N - 1) * (1 - t * t)) / (1 - t ** n) ** 2
def job(args):
    n, p, dq = args; mp.mp.dps = 50 + int(1.0 * n * (float(p) + float(dq)))
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2
    J = int(min(6000, 80 / (n * float(p)) + 8))
    u = [chi(n, 0, p)] + [mp.e ** (-m * al) * chi(n, m, p) * mp.sqrt(sigma(n, m, q, J) / sigma(n, m, p, J)) for m in range(1, n - 1)] + [mp.mpf(0)] * 3
    a = [2 * (mp.sinh(al) - u[0] * mp.cosh(al) + u[1])] + [u[m - 1] + u[m + 1] - 2 * mp.cosh(al) * u[m] for m in range(1, n)] + [mp.mpf(0)] * 2
    d2a = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(n)]
    f = [a[0] / (2 * n)] + [a[m] / (2 * (n - m)) for m in range(1, n)]
    d2f = [f[j] - 2 * f[j + 1] + f[j + 2] for j in range(n - 2)]
    d1f = [f[j] - f[j + 1] for j in range(n - 1)]
    scale = f[0]
    return (n, float(p), float(q), min(d2a) / a[0], min(d2f) / scale, min(d1f) / scale, min(f) / scale,
            min(d2f[j] / (d1f[j] + d1f[j + 1]) for j in range(1, n - 2) if d1f[j] + d1f[j + 1] != 0) if n > 4 else mp.mpf(0))
if __name__ == "__main__":
    ns = [int(x) for x in sys.argv[1:]] or [5, 8, 16, 32, 50, 80]
    jobs = [(n, p, dq) for n in ns for p in ('0.03', '0.1', '0.3', '0.7', '1.5', '3') for dq in ('0.0005', '0.01', '0.1', '0.5', '2', '6')]
    with Pool(60) as pool: out = pool.map(job, jobs, chunksize=1)
    bad = [o for o in out if o[3] < 0 or o[4] < 0 or o[5] < 0 or o[6] < 0]
    for n in ns:
        rows = [o for o in out if o[0] == n]
        print(f"n={n}: cases {len(rows)};  min d2a/a0 = {mp.nstr(min(o[3] for o in rows), 3)};  min d2f/f0 = {mp.nstr(min(o[4] for o in rows), 3)};"
              f"  min d1f/f0 = {mp.nstr(min(o[5] for o in rows), 3)};  min f/f0 = {mp.nstr(min(o[6] for o in rows), 3)};  min rel curvature d2f/(d1f+d1f') = {mp.nstr(min(o[7] for o in rows), 3)}")
    print("violations:", [(o[0], o[1], o[2], mp.nstr(o[3], 3), mp.nstr(o[4], 3), mp.nstr(o[5], 3)) for o in bad])
