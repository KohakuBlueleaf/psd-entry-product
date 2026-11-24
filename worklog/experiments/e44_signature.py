"""E44 (evidence only).  For fixed theta, the kernel (p,q) -> L(theta;p,q) (gap of Star) on a grid of p-values:
eigenvalue signature, and the reverse Cauchy-Schwarz ratio  L(p,q)/sqrt(E_p E_q)."""
import mpmath as mp, numpy as np
from multiprocessing import Pool
import e20_closed_form as e
def job(args):
    n, thfrac = args; mp.mp.dps = 30
    th = mp.pi * mp.mpf(thfrac)
    ps = [mp.mpf(x) for x in ('0.05', '0.15', '0.3', '0.5', '0.8', '1.2', '1.8', '2.6')]
    G = {p: [e.Gam(n, m, p) for m in range(n - 1)] for p in ps}
    def L(p, q):
        a = (p + q) / 2
        return (-mp.log(abs(1 - mp.e ** (-a) * mp.e ** (1j * th))) - (G[p][0] + G[q][0]) / 2
                - sum(mp.sqrt(G[p][m] * G[q][m]) * mp.cos(m * th) for m in range(1, n - 1)))
    M = mp.matrix(len(ps), len(ps))
    for i, p in enumerate(ps):
        for j, q in enumerate(ps): M[i, j] = L(p, q)
    ev = sorted([float(x) for x in mp.eigsy(M, eigvals_only=True)], reverse=True)
    rcs = min(M[i, j] / mp.sqrt(M[i, i] * M[j, j]) for i in range(len(ps)) for j in range(i)) if all(M[i, i] > 0 for i in range(len(ps))) else None
    return n, thfrac, ev, rcs
if __name__ == "__main__":
    jobs = [(n, t) for n in (5, 8, 12) for t in ('0.13', '0.31', '0.55', '0.77', '1.0')]
    with Pool(15) as pool: out = pool.map(job, jobs, chunksize=1)
    for n, t, ev, rcs in out:
        print(f"n={n} theta/pi={t}: #pos={sum(1 for x in ev if x > 1e-14 * abs(ev[0]))}  top eigs {['%.2e' % x for x in ev[:3]]} bottom {['%.2e' % x for x in ev[-2:]]}   min L/sqrt(E_p E_q) = {mp.nstr(rcs, 5) if rcs is not None else 'n/a'}")
