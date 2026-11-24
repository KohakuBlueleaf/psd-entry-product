"""E38 (evidence only, modest size).  (H_in):  for 0 <= p <= q,
   H_in = P_alpha/2 - k_0(p)/2 - sum_{m=1}^{n-2} k_m(p) sqrt(Gamma_m(q)/Gamma_m(p)) cos(m theta) >= 0,   alpha = (p+q)/2.
Scan p (including p = 0 and p near 0), q - p from tiny to large, theta on a grid.  Also record whether the coefficient
sequence (xi_0(p), e^{-m alpha}(1 - chi_m(p) mu_m), ...) is convex in m (Fejer criterion)."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def job(args):
    n, p, dq = args; mp.mp.dps = 30
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2
    c = [(1 - e.k(n, 0, p)) / 2]
    for m in range(1, n - 1):
        c.append(mp.e ** (-m * al) - e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)))
    r = mp.e ** (-al)
    best = mp.inf; arg = None
    for j in range(0, 8 * n + 1):
        th = mp.pi * j / (8 * n)
        if j == 0 and al == 0: continue
        tail = (r ** (n - 1) * (mp.cos((n - 1) * th) - r * mp.cos((n - 2) * th))) / (1 - 2 * r * mp.cos(th) + r * r)   # sum_{m>=n-1} r^m cos(m th)
        v = c[0] + sum(c[m] * mp.cos(m * th) for m in range(1, n - 1)) + tail
        P = (1 - r * r) / (1 - 2 * r * mp.cos(th) + r * r) if al > 0 else mp.mpf(1)
        if v / P < best: best, arg = v / P, j / (8 * n)
    seq = [2 * c[0]] + c[1:] + [r ** m for m in range(n - 1, n + 3)]
    convex = all(seq[j] - 2 * seq[j + 1] + seq[j + 2] >= 0 for j in range(len(seq) - 2))
    return n, float(p), float(q), best, arg, convex

if __name__ == "__main__":
    ps = ['0', '0.01', '0.05', '0.15', '0.4', '0.9', '2']
    dqs = ['0.001', '0.02', '0.1', '0.4', '1.2', '4']
    ns = (4, 5, 7, 10, 16, 24)
    jobs = [(n, p, dq) for n in ns for p in ps for dq in dqs]
    with Pool(24) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in ns:
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n}: min H_in/P_alpha = {mp.nstr(w[3], 4)} at (p,q,theta/pi)=({w[1]},{w[2]:.3f},{w[4]:.3f});  negative cases: {sum(1 for o in rows if o[3] < 0)};  "
              f"coefficient sequence convex in {sum(1 for o in rows if o[5])}/{len(rows)} cases")
