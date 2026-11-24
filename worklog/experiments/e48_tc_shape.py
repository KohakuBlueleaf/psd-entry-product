"""E48 (evidence only).  Shape of f (TC): tests
  (a) f log-convex on 1..n-1 (and from 0);  (b) F(m)=e^{m b} f(m) convex / nonincreasing;  (c) F(m)=e^{m c} f(m) with c s.t. ... ;
  (d) sign pattern of higher differences of f (complete monotonicity up to order 4)."""
import mpmath as mp, sys
from multiprocessing import Pool
from e31_criterion_v2 import sigma
from e47_qc_wide import chi
def fseq(n, p, q):
    al = (p + q) / 2
    J = int(min(6000, 80 / (n * float(p)) + 8))
    u = [chi(n, 0, p)] + [mp.e ** (-m * al) * chi(n, m, p) * mp.sqrt(sigma(n, m, q, J) / sigma(n, m, p, J)) for m in range(1, n - 1)] + [mp.mpf(0)] * 3
    a = [2 * (mp.sinh(al) - u[0] * mp.cosh(al) + u[1])] + [u[m - 1] + u[m + 1] - 2 * mp.cosh(al) * u[m] for m in range(1, n)]
    return [a[0] / (2 * n)] + [a[m] / (2 * (n - m)) for m in range(1, n)]
def job(args):
    n, p, dq = args; mp.mp.dps = 50 + int(1.0 * n * (float(p) + float(dq)))
    p = mp.mpf(p); q = p + mp.mpf(dq); b = (q - p) / 2
    f = fseq(n, p, q)
    logcx = min(f[j] * f[j + 2] / f[j + 1] ** 2 for j in range(0, n - 2))
    logcx1 = min(f[j] * f[j + 2] / f[j + 1] ** 2 for j in range(1, n - 2))
    F = [mp.e ** (m * b) * f[m] for m in range(n)]
    Fcx = min((F[j] - 2 * F[j + 1] + F[j + 2]) / F[0] for j in range(n - 2)); Fdec = min((F[j] - F[j + 1]) / F[0] for j in range(n - 1))
    d = f[:]; cm = []
    for k in range(1, 5):
        d = [d[j] - d[j + 1] for j in range(len(d) - 1)]
        cm.append(min(d) >= 0)
    return n, float(p), float(q), logcx, logcx1, Fcx, Fdec, cm
if __name__ == "__main__":
    ns = [5, 8, 16, 32]
    jobs = [(n, p, dq) for n in ns for p in ('0.05', '0.3', '1.0', '2.5') for dq in ('0.001', '0.05', '0.4', '2', '6')]
    with Pool(60) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in ns:
        rows = [o for o in out if o[0] == n]
        print(f"n={n}: min f_j f_(j+2)/f_(j+1)^2 (j>=0) = {mp.nstr(min(o[3] for o in rows), 6)}, (j>=1) = {mp.nstr(min(o[4] for o in rows), 8)};"
              f"  e^(mb)f: min d2/F0 = {mp.nstr(min(o[5] for o in rows), 3)}, min d1/F0 = {mp.nstr(min(o[6] for o in rows), 3)};"
              f"  CM orders 1..4 hold in all cases: {[all(o[7][k] for o in rows) for k in range(4)]}")
