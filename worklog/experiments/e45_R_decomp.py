"""E45 (evidence only).  Decomposition  H_in = S - R,
   S = P_b * (A_p/2)  (Poisson smoothing of the diagonal error kernel; >= 0),
   R = sum_{m=1}^{n-2} rho_m cos(m theta),  rho_m = k_m(p) (nu_m - e^{-m b}) >= 0.
Report: max_theta R/S, the set where R > 0 (largest theta with R>0, in units of pi/n), and sign of R at the nodes."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
def job(args):
    n, p, dq = args; mp.mp.dps = 30
    p = mp.mpf(p); q = p + mp.mpf(dq); al = (p + q) / 2; b = (q - p) / 2; r = mp.e ** (-al)
    u = [None] + [e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)) for m in range(1, n - 1)]
    rho = [None] + [u[m] - e.k(n, m, p) * mp.e ** (-m * b) for m in range(1, n - 1)]
    k0 = e.k(n, 0, p)
    def R(th): return sum(rho[m] * mp.cos(m * th) for m in range(1, n - 1))
    def H(th):
        return (mp.sinh(al) / (mp.cosh(al) - mp.cos(th))) / 2 - k0 / 2 - sum(u[m] * mp.cos(m * th) for m in range(1, n - 1))
    G = 16 * n
    worst = -mp.inf; lastpos = 0; negR = all(rho[m] >= 0 for m in range(1, n - 1))
    for j in range(0, G + 1):
        th = mp.pi * j / G
        Rv = R(th); Sv = H(th) + Rv
        if Rv / Sv > worst: worst = Rv / Sv
        if Rv > 0: lastpos = j * n / G
    nodes = max(R(2 * mp.pi * kk / n) / abs(R(0)) for kk in range(1, n // 2 + 1))
    return n, float(p), float(q), worst, lastpos, nodes, negR
if __name__ == "__main__":
    jobs = [(n, p, dq) for n in (6, 12, 24, 40) for p in ('0.01', '0.1', '0.4', '1.0', '2.5') for dq in ('0.002', '0.05', '0.3', '1.5', '6')]
    with Pool(50) as pool: out = pool.map(job, jobs, chunksize=1)
    for o in out:
        print(f"n={o[0]:2d} p={o[1]:<5} q={o[2]:<6.3f}: max R/S = {mp.nstr(o[3], 4):>9}  last theta with R>0: {o[4]:.2f} pi/n   max_k R(theta_k)/R(0) = {mp.nstr(o[5], 3):>10}  rho>=0: {o[6]}")
