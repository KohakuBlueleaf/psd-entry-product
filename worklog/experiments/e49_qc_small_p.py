"""E49 (evidence only).  (QC)/(TC) in the corner p -> 0 (and tiny q-p), using the integral definition of Gamma (e20), high precision."""
import mpmath as mp, sys
from multiprocessing import Pool
import e20_closed_form as e
def job(args):
    n, p, dq = args; mp.mp.dps = 60
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2
    u = [e.k(n, 0, p)] + [e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)) for m in range(1, n - 1)] + [mp.mpf(0)] * 3
    a = [2 * (mp.sinh(al) - u[0] * mp.cosh(al) + u[1])] + [u[m - 1] + u[m + 1] - 2 * mp.cosh(al) * u[m] for m in range(1, n)] + [mp.mpf(0)] * 2
    d2a = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(n)]
    f = [a[0] / (2 * n)] + [a[m] / (2 * (n - m)) for m in range(1, n)]
    d2f = [f[j] - 2 * f[j + 1] + f[j + 2] for j in range(n - 2)]
    d1f = [f[j] - f[j + 1] for j in range(n - 1)]
    jmin = min(range(n), key=lambda j: d2a[j])
    return n, float(p), float(q), min(d2a) / a[0], jmin, min(d2f) / f[0], min(d1f) / f[0], [mp.nstr(x / a[0], 3) for x in d2a]
if __name__ == "__main__":
    jobs = [(n, p, dq) for n in (3, 4, 5, 7, 10, 14) for p in ('0.0001', '0.001', '0.01') for dq in ('0.00001', '0.001', '0.03', '0.3', '3', '12')]
    with Pool(60) as pool: out = pool.map(job, jobs, chunksize=1)
    for o in out:
        flag = '' if (o[3] >= 0 and o[5] >= 0 and o[6] >= 0) else '   <-- VIOLATION'
        print(f"n={o[0]:2d} p={o[1]:<7} q={o[2]:<9.5f}: min d2a/a0={mp.nstr(o[3],3):>10} at j={o[4]:<2}  min d2f/f0={mp.nstr(o[5],3):>10}  min d1f/f0={mp.nstr(o[6],3):>10}{flag}")
    print("example d2a/a0 (n=7,p=1e-4,dq=1e-3):", [o[7] for o in out if o[0] == 7 and o[1] == 0.0001 and abs(o[2] - 0.0011) < 1e-9])
