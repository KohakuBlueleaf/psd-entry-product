"""E13c. High-precision (mpmath, 60 digits) check of (**) where float64 was at its noise floor (n >= 8, extreme s,t).
Reports min over theta of (g-h), normalised by c_1(s)+c_1(t) so that tiny parameters are judged on a relative scale."""
import mpmath as mp, sys
from multiprocessing import Pool
mp.mp.dps = 60

def coeffs(n, tau):
    D = n - 2 if n % 2 else n - 1
    rows, rhs = [], []
    q = lambda t: 1 + tau * tau - 2 * tau * mp.cos(t)
    for k in range(1, n // 2 + 1):
        t = 2 * mp.pi * k / n
        rows.append([mp.cos(m * t) for m in range(D + 1)]); rhs.append(-mp.log(q(t)) / 2)
        if 2 * k != n:
            rows.append([-m * mp.sin(m * t) for m in range(D + 1)]); rhs.append(-tau * mp.sin(t) / q(t))
        else:
            rows.append([-m * m * mp.cos(m * t) for m in range(D + 1)]); rhs.append(tau / (1 + tau) ** 2)
    return mp.lu_solve(mp.matrix(rows), mp.matrix(rhs))

def job(args):
    n, a, b = args
    mp.mp.dps = 60
    s, t = mp.e ** (a + b), mp.e ** (a - b); tau = mp.sqrt(s * t)
    cs, ct = coeffs(n, s), coeffs(n, t)
    mc = min(min(cs[m] for m in range(1, len(cs))), min(ct[m] for m in range(1, len(ct))))
    best = mp.inf
    G = 1200
    for k in range(G + 1):
        th = mp.pi * k / G
        g = -mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 if not (k == 0 and tau == 1) else mp.inf
        h = (cs[0] + ct[0]) / 2 + sum(mp.sqrt(cs[m] * ct[m]) * mp.cos(m * th) for m in range(1, len(cs)))
        best = min(best, g - h)
    return n, a, b, best / (cs[1] + ct[1]), mc

if __name__ == "__main__":
    jobs = [(n, a, b) for n in (8, 9, 12, 16) for a in (-6, -3, -1, 0.3, 2, 4) for b in (2.0, 0.5, 0.05)]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (8, 9, 12, 16):
        rows = [o for o in out if o[0] == n]
        w = min(rows, key=lambda o: o[3])
        print(f"n={n}: min normalised (g-h) = {mp.nstr(w[3], 6)} at a={w[1]}, b={w[2]};  "
              f"min coefficient = {mp.nstr(min(o[4] for o in rows), 4)};  all >= 0: {all(o[3] >= 0 for o in rows)}")
