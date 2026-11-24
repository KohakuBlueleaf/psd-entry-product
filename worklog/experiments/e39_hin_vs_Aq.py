"""E39 (evidence only).  Is  H_in(p, q; theta) >= H_in(q, q; theta) = (1/2) rho_n(q) Fej_n(theta) P_q(theta)  for p <= q ?
(equivalently: is L convex in the smaller parameter p?)"""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def Hin(n, p, q, ths):
    al = (p + q) / 2; r = mp.e ** (-al)
    c = [(1 - e.k(n, 0, p)) / 2]
    for m in range(1, n - 1):
        c.append(r ** m - e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)))
    out = []
    for th in ths:
        tail = (r ** (n - 1) * (mp.cos((n - 1) * th) - r * mp.cos((n - 2) * th))) / (1 - 2 * r * mp.cos(th) + r * r)
        out.append(c[0] + sum(c[m] * mp.cos(m * th) for m in range(1, n - 1)) + tail)
    return out
def Aq(n, q, th):
    rho = (mp.cosh(q) - 1) / (mp.cosh(n * q) - 1)
    fej = (1 - mp.cos(n * th)) / (1 - mp.cos(th))
    return rho * fej * mp.sinh(q) / (mp.cosh(q) - mp.cos(th)) / 2
def job(args):
    n, p, dq = args; mp.mp.dps = 30
    p = mp.mpf(p); q = p + mp.mpf(dq)
    ths = [mp.pi * j / (6 * n) for j in range(1, 6 * n + 1)]
    H = Hin(n, p, q, ths)
    worst = min((H[i] - Aq(n, q, th)) / (H[i] + Aq(n, q, th)) for i, th in enumerate(ths))
    return n, float(p), float(q), worst
if __name__ == "__main__":
    jobs = [(n, p, dq) for n in (4, 6, 10, 16) for p in ('0.02', '0.2', '0.6', '1.5') for dq in ('0.01', '0.1', '0.5', '2')]
    with Pool(16) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in (4, 6, 10, 16):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n}: min of (H_in(p,q) - A_q/2)/(sum) = {mp.nstr(w[3], 4)} at (p,q)=({w[1]},{w[2]:.2f});  negative cases {sum(1 for o in rows if o[3] < 0)}/{len(rows)}")
