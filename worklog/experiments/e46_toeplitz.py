"""E46 (evidence only).  Q(theta) := sinh(al) - 2 (cosh(al) - cos theta) Pi_p^nu(theta)   (= 2 sinh(al) H_in / P_al),
a cosine polynomial of degree n-1:  Q = q_0 + sum_{m=1}^{n-1} q_m cos(m theta).
Toeplitz ansatz  Q = sum_{j,j'<n} f(|j-j'|) e^{i(j-j')theta},  f(0)=q_0/n, f(m)=q_m/(2(n-m)).
Check: f >= 0, decreasing, convex on 0..n-1 (second differences), and min eigenvalue of the n x n Toeplitz matrix."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
def job(args):
    n, p, dq = args; mp.mp.dps = 40
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2
    u = [e.k(n, 0, p)] + [e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)) for m in range(1, n - 1)] + [mp.mpf(0), mp.mpf(0)]
    qc = [mp.sinh(al) - u[0] * mp.cosh(al) + u[1]] + [u[m - 1] + u[m + 1] - 2 * mp.cosh(al) * u[m] for m in range(1, n)]
    f = [qc[0] / n] + [qc[m] / (2 * (n - m)) for m in range(1, n)]
    T = mp.matrix(n, n)
    for i in range(n):
        for j in range(n): T[i, j] = f[abs(i - j)]
    ev = mp.eigsy(T, eigvals_only=True); lam = min(ev) / max(ev)
    d2 = [f[j] - 2 * f[j + 1] + f[j + 2] for j in range(n - 2)]
    return (n, float(p), float(q), lam, min(f) / f[0], sum(1 for j in range(n - 1) if f[j + 1] > f[j]), sum(1 for x in d2 if x < 0),
            [mp.nstr(x / f[0], 4) for x in f[:6]] + ['..'] + [mp.nstr(x / f[0], 4) for x in f[-3:]])
if __name__ == "__main__":
    jobs = [(n, p, dq) for n in (4, 6, 10, 16, 24) for p in ('0.02', '0.2', '0.6', '1.5') for dq in ('0.01', '0.1', '0.5', '2')]
    with Pool(60) as pool: out = pool.map(job, jobs, chunksize=1)
    for o in out:
        print(f"n={o[0]:2d} p={o[1]:<4} q={o[2]:<5.2f}: lam_min/lam_max={mp.nstr(o[3],3):>10}  min f/f0={mp.nstr(o[4],3):>9}  #incr={o[5]} #nonconvex={o[6]}  f/f0={o[7]}")
