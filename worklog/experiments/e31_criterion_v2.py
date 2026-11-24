"""E31. Theta-free criterion, version 2, applied directly to W = delta_0 + sum_m delta_m cos(m theta)  (W >= 0 implies Star).
Coefficients from the exact power series (fast).  e_j = second differences of (2 delta_0, delta_1, ..., delta_{n-2}, 0, ...).
Improvement over e29: the positive weights are unimodal (they rise after the sign change, then decay), so the nonincreasing
minorant is started at an optimised index J' (positive weights before J' are simply dropped)."""
import mpmath as mp, sys
from multiprocessing import Pool

def sigma(n, m, x, J):
    s = mp.e ** (-x); N = n - m
    t1 = sum(j * (s ** (j * n - 1 - m) / (j * n - 1) - s ** (j * n + 1 - m) / (j * n + 1)) for j in range(1, J))
    t2 = sum((j + 1) * s ** (j * n) / (j * n + m) for j in range(1, J))
    t3 = sum((j - 1) * s ** (j * n - 2 * m) / (j * n - m) for j in range(2, J))
    return 1 - m * (N * t1 - t2 + t3)
def gam0(n, x, J):
    s = mp.e ** (-x)
    return sum(s ** (j * n) / (j * n) for j in range(1, J)) - mp.mpf(n) / 2 * sum(j * (s ** (j * n - 1) / (j * n - 1) - s ** (j * n + 1) / (j * n + 1)) for j in range(1, J))

def delta_seq(n, al, b):
    p, q = al - b, al + b
    J = int(min(4000, 60 / (n * float(p)) + 6)) if p > 0 else 4000
    d = [2 * (gam0(n, al, J) - (gam0(n, p, J) + gam0(n, q, J)) / 2)]
    for m in range(1, n - 1):
        d.append(mp.e ** (-m * al) / m * (sigma(n, m, al, J) - mp.sqrt(sigma(n, m, p, J) * sigma(n, m, q, J))))
    return d

def criterion(a):
    a = a + [mp.mpf(0)] * 3
    ev = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(len(a) - 2)]
    L = len(ev)
    neg = [max(-x, mp.mpf(0)) for x in ev]; nneg = sum(1 for x in ev if x < 0)
    if nneg == 0: return mp.inf, 0
    ts = [mp.mpf(i) / 4 for i in range(4, 4 * (L + 3))] + [mp.mpf(10) ** k for k in range(2, 7)]
    Nt = [sum(neg[j] * min(mp.mpf(1), (j + 1) ** 2 / t ** 2) for j in range(L)) for t in ts]
    best = mp.mpf(0)
    for Jp in range(0, min(L, 40)):
        if ev[Jp] <= 0: continue
        eh = [mp.mpf(0)] * (L + 1); cur = mp.inf
        for j in range(Jp, L):
            cur = min(cur, max(ev[j], mp.mpf(0))); eh[j] = cur
        worst = mp.inf
        for t, N in zip(ts, Nt):
            P1 = sum((eh[k] - eh[k + 1]) * max(mp.mpf(0), (k - Jp + 1 - t) / 2) for k in range(Jp, L))
            P2 = 4 / (mp.pi ** 2 * t ** 2) * sum(eh[j] * (j + 1) ** 2 for j in range(Jp, L) if j + 1 <= t)
            worst = min(worst, max(P1, P2) / N)
        best = max(best, worst)
    return best, nneg

def job(args):
    n, al, b = args; mp.mp.dps = 40 + 3 * n
    r, nneg = criterion(delta_seq(n, mp.mpf(al), mp.mpf(b)))
    return n, al, b, r, nneg

if __name__ == "__main__":
    grid = [(a, bb) for a in ('0.05', '0.15', '0.3', '0.5', '0.75', '1.0', '1.4', '2.0', '3.0') for bb in ('0.01', '0.3')]
    grid = [(a, str(min(float(bb), float(a) * (0.95 if bb == '0.3' else 0.5)))) for a, bb in grid]
    ns = (16, 25, 32, 40, 50, 64, 80)
    jobs = [(n, a, bb) for n in ns for a, bb in grid]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in ns:
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n}: worst criterion ratio = {'inf' if w[3] == mp.inf else mp.nstr(w[3], 4)} at (alpha,b)=({w[1]},{w[2]});  max #negative second differences = {max(o[4] for o in rows)}")
