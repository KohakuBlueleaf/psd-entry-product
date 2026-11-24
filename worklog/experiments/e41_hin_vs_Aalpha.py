"""E41 (evidence only).  Compare H_in(p,q;theta) with product-form candidates:
   (a) A_alpha/2 = rho_n(alpha) Fej_n P_alpha / 2      (b) rho_n(p) Fej_n P_alpha / 2     (c) rho_n(q) Fej_n P_alpha/2 ."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
from e39_hin_vs_Aq import Hin
def rho(n, x): return (mp.cosh(x) - 1) / (mp.cosh(n * x) - 1)
def job(args):
    n, p, dq = args; mp.mp.dps = 30
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2
    ths = [mp.pi * (j + mp.mpf('0.37')) / (4 * n) for j in range(0, 4 * n)]
    H = Hin(n, p, q, ths)
    res = []
    for x in (al, p, q):
        w = min(H[i] / (rho(n, x) * (1 - mp.cos(n * th)) / (1 - mp.cos(th)) * mp.sinh(al) / (mp.cosh(al) - mp.cos(th)) / 2) for i, th in enumerate(ths))
        res.append(w)
    return n, float(p), float(q), res
if __name__ == "__main__":
    jobs = [(n, p, dq) for n in (4, 6, 10, 16) for p in ('0.02', '0.2', '0.6', '1.5') for dq in ('0.01', '0.1', '0.5', '2')]
    with Pool(16) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in (4, 6, 10, 16):
        rows = [o for o in out if o[0] == n]
        for i, name in enumerate(("rho(alpha)", "rho(p)", "rho(q)")):
            w = min(rows, key=lambda o: o[3][i])
            print(f"n={n}: min over theta,(p,q) of H_in / (1/2 {name} Fej P_alpha) = {mp.nstr(w[3][i], 5)} at (p,q)=({w[1]},{w[2]:.2f})")
