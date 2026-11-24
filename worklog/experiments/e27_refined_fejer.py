"""E27. Refined Fejer argument for D = a_0/2 + sum_{m>=1} a_m cos(m theta)  (a_m = 0 for m >= n-1).
Summation by parts:  D = sum_{j>=0} D2_j * sin^2((j+1) theta/2) / (2 sin^2(theta/2)),   D2_j = a_j - 2a_{j+1} + a_{j+2}.
Since sin^2(k x) + sin^2((k+1) x) >= sin^2(x)/2, D >= 0 follows from
   (A)  D2_j >= 0 for all j >= 1,      and
   (B)  sum_{j = 1,3,5,...} min(D2_j, D2_{j+1})  >=  2 * max(0, -D2_0).
Test (A) and (B) for the exact coefficients over many (n, p, q)."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def job(args):
    n, p, q = args; mp.mp.dps = 60 + 6 * n
    k, k0m1 = e.k, e.k0m1
    pts = lambda x: [x, x + mp.mpf(1) / 4, x + 1, x + 3, x + 8, x + 20, x + 60, x + 150, x + 400]
    Gam = lambda m, x: mp.quad(lambda w: k(n, m, w), pts(x))
    a = [2 * (k0m1(n, q) - k0m1(n, p))]
    for m in range(1, n - 1):
        Gp, Gq = Gam(m, p), Gam(m, q)
        a.append(mp.sqrt(Gp * Gq) * (k(n, m, q) / Gq - k(n, m, p) / Gp))
    a += [mp.mpf(0)] * 3
    D2 = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(len(a) - 2)]
    A = min(D2[1:]) >= 0
    paired = sum(min(D2[j], D2[j + 1]) for j in range(1, len(D2) - 1, 2))
    need = 2 * max(mp.mpf(0), -D2[0])
    return n, float(p), float(q), A, (paired / need if need > 0 else mp.inf), min(D2[1:]) / a[0]

if __name__ == "__main__":
    pairs = [(0, 0.01), (0, 0.4), (0, 3), (0.05, 0.06), (0.05, 1), (0.3, 0.31), (0.3, 0.9), (0.75, 0.76), (0.75, 1.2), (0.75, 4),
             (1.2, 1.21), (1.2, 2.5), (2, 2.02), (2, 5), (3.5, 3.52), (3.5, 8)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (4, 5, 6, 8, 11, 15, 16, 20, 25, 32, 40) for p, q in pairs]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (4, 5, 6, 8, 11, 15, 16, 20, 25, 32, 40):
        rows = [o for o in out if o[0] == n]
        r = min(o[4] for o in rows)
        print(f"n={n:2d}: (A) holds in all {len(rows)} cases: {all(o[3] for o in rows)};  min D2_j/a_0 (j>=1) = {mp.nstr(min(o[5] for o in rows), 3)};  "
              f"(B) min ratio = {'n/a (D2_0 >= 0 everywhere)' if r == mp.inf else mp.nstr(r, 4)}")
