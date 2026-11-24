"""E29. A theta-free sufficient condition for D >= 0 that tolerates several negative second differences.
D(theta) = sum_{j>=0} e_j * sin^2((j+1)x)/(2 sin^2 x),  x = theta/2,  e_j = a_j - 2a_{j+1} + a_{j+2}  (a_0 = 2 d_0).
Let t = 1/sin x >= 1.  Split e = e^+ - e^-.  Let J = first index with e_j > 0, and ehat_j = min_{J<=i<=j} e_i^+ (nonincreasing).
  positive part * 2 sin^2 x >= P1(t) = sum_{k>=J} (ehat_k - ehat_{k+1}) * max(0, (k-J+1 - t)/2)       [sum of sin^2 over a block]
  positive part * 2 sin^2 x >= P2(t) = (4/(pi^2 t^2)) * sum_{J<=j<=t-1} ehat_j (j+1)^2                 [sin(Mx) >= 2Mx/pi]
  negative part * 2 sin^2 x <= N(t)  = sum_j e_j^- * min(1, (j+1)^2/t^2)
Criterion:  max(P1(t), P2(t)) >= N(t) for all t >= 1.   Report the worst ratio max(P1,P2)/N over t and over (p,q)."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def coeff_seq(n, p, q):
    k, k0m1 = e.k, e.k0m1
    pts = lambda x: [x, x + mp.mpf(1) / 4, x + 1, x + 3, x + 8, x + 20, x + 60, x + 150, x + 400]
    Gam = lambda m, x: mp.quad(lambda w: k(n, m, w), pts(x))
    a = [2 * (k0m1(n, q) - k0m1(n, p))]
    for m in range(1, n - 1):
        Gp, Gq = Gam(m, p), Gam(m, q)
        a.append(mp.sqrt(Gp * Gq) * (k(n, m, q) / Gq - k(n, m, p) / Gp))
    return a

def criterion(a):
    a = a + [mp.mpf(0)] * 3
    ev = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(len(a) - 2)]
    pos = [max(x, mp.mpf(0)) for x in ev]; neg = [max(-x, mp.mpf(0)) for x in ev]
    J = next(j for j, x in enumerate(ev) if x > 0)
    eh = []; cur = mp.inf
    for j in range(len(ev)):
        if j < J: eh.append(mp.mpf(0)); continue
        cur = min(cur, pos[j]); eh.append(cur)
    eh.append(mp.mpf(0))
    nneg = sum(1 for x in ev if x < 0)
    if sum(neg) == 0: return mp.inf, nneg
    worst = mp.inf
    ts = [mp.mpf(i) / 8 for i in range(8, 8 * (len(ev) + 3))] + [mp.mpf(10) ** k for k in range(2, 7)]
    for t in ts:
        P1 = sum((eh[k] - eh[k + 1]) * max(mp.mpf(0), (k - J + 1 - t) / 2) for k in range(J, len(ev)))
        P2 = 4 / (mp.pi ** 2 * t ** 2) * sum(eh[j] * (j + 1) ** 2 for j in range(J, len(ev)) if j + 1 <= t)
        N = sum(neg[j] * min(mp.mpf(1), (j + 1) ** 2 / t ** 2) for j in range(len(ev)))
        worst = min(worst, max(P1, P2) / N)
    return worst, nneg

def job(args):
    n, p, q = args; mp.mp.dps = 50 + 6 * n
    r, nneg = criterion(coeff_seq(n, p, q))
    return n, float(p), float(q), r, nneg

if __name__ == "__main__":
    pairs = [(0, 0.01), (0, 0.4), (0, 3), (0.02, 0.03), (0.05, 0.06), (0.05, 1), (0.15, 0.16), (0.3, 0.31), (0.3, 0.9), (0.5, 0.51),
             (0.75, 0.76), (0.75, 1.2), (0.75, 4), (1.0, 1.01), (1.2, 1.21), (1.2, 2.5), (1.6, 1.61), (2, 2.02), (2, 5), (3.5, 3.52), (3.5, 8)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (16, 20, 25, 32, 40, 50) for p, q in pairs]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (16, 20, 25, 32, 40, 50):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n}: worst criterion ratio = {'inf' if w[3] == mp.inf else mp.nstr(w[3], 4)} at (p,q)=({w[1]},{w[2]});  max number of negative second differences = {max(o[4] for o in rows)}")
