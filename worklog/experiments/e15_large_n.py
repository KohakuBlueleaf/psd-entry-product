"""E15. Does (**) (and the stronger polynomial form W >= 0) persist for large n?  High precision."""
import mpmath as mp, sys
from multiprocessing import Pool
from e13c_gm_certificate_mp import coeffs

def job(args):
    n, a, b = args
    mp.mp.dps = 90
    s, t, tau = mp.e ** (a + b), mp.e ** (a - b), mp.e ** a
    cs, ct, cm = coeffs(n, s), coeffs(n, t), coeffs(n, tau)
    D = len(cs)
    R = [(cs[0] + ct[0]) / 2] + [mp.sqrt(cs[m] * ct[m]) for m in range(1, D)]
    mc = min(min(cs[m] for m in range(1, D)), min(ct[m] for m in range(1, D)))
    G = 6 * n
    wmin = mp.inf; smin = mp.inf; xw = None
    for k in range(G + 1):
        th = mp.pi * k / G
        cosm = [mp.cos(m * th) for m in range(D)]
        Rv = sum(R[m] * cosm[m] for m in range(D)); hv = sum(cm[m] * cosm[m] for m in range(D))
        if hv - Rv < wmin: wmin, xw = hv - Rv, k / G
        if not (k == 0 and tau == 1):
            smin = min(smin, -mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 - Rv)
    scale = sum(abs(cm[m] - R[m]) for m in range(D))
    return n, a, b, wmin / scale, xw, smin / scale, mc

if __name__ == "__main__":
    jobs = [(n, a, b) for n in (12, 16, 20, 25, 30, 40) for a in (-1.5, -0.5, 0.0, 0.2, 1.0) for b in (0.05, 0.5)]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (12, 16, 20, 25, 30, 40):
        rows = [o for o in out if o[0] == n]
        w = min(rows, key=lambda o: o[3]); s = min(rows, key=lambda o: o[5])
        print(f"n={n}: min W/scale = {mp.nstr(w[3], 5)} (a={w[1]}, b={w[2]}, theta/pi={w[4]:.3f});  "
              f"min (g-R)/scale = {mp.nstr(s[5], 5)} (a={s[1]}, b={s[2]});  min coeff >= 0: {min(o[6] for o in rows) >= 0}")
