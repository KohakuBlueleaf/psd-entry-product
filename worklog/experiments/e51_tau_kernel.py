"""E51 (evidence only).  New kernel  K_m(p,q) = Gam_m(q) + (1/2) int_p^q k_m(x) e^{-m(q-x)/2} dx   (p <= q; symmetric extension).
Claims to test:
 (1) [K_m(p_i,p_j)] is positive semidefinite with diagonal Gam_m(p_i);
 (2) pair inequality:  g_al(theta) >= (Gam_0(p)+Gam_0(q))/2 + sum_m K_m(p,q) cos(m theta);
 (3) representation  K_m(p,q) = (1/m) int_0^inf chi_m'(tau) e^{-m max(p,tau)/2} e^{-m max(q,tau)/2} dtau."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
mp.mp.dps = 25
def K(n, m, p, q):
    if p > q: p, q = q, p
    if p == q: return e.Gam(n, m, q)
    return e.Gam(n, m, q) + mp.quad(lambda x: e.k(n, m, x) * mp.e ** (-m * (q - x) / 2), [p, q]) / 2
def chi_prime(n, m, x):
    return mp.diff(lambda y: mp.e ** (m * y) * e.k(n, m, y), x)
def job(args):
    kind, n = args; mp.mp.dps = 25
    if kind == 'psd':
        ps = [mp.mpf(x) for x in ('0.02', '0.1', '0.25', '0.5', '0.9', '1.5', '2.5')]
        out = []
        for m in range(1, n - 1):
            M = mp.matrix(len(ps), len(ps))
            for i, p in enumerate(ps):
                for j, q in enumerate(ps): M[i, j] = K(n, m, p, q)
            ev = mp.eigsy(M, eigvals_only=True); out.append(min(ev) / max(ev))
        return kind, n, min(out)
    if kind == 'pair':
        worst = mp.inf
        for p, q in (('0', '0.3'), ('0.05', '0.06'), ('0.05', '1'), ('0.3', '0.5'), ('0.5', '3'), ('1', '1.1'), ('2', '5')):
            p, q = mp.mpf(p), mp.mpf(q); al = (p + q) / 2
            c0 = (e.Gam(n, 0, p) + e.Gam(n, 0, q)) / 2
            Ks = [K(n, m, p, q) for m in range(1, n - 1)]
            for j in range(0, 6 * n + 1):
                th = mp.pi * j / (6 * n)
                if j == 0 and al == 0: continue
                gap = -mp.log(abs(1 - mp.e ** (-al) * mp.e ** (1j * th))) - c0 - sum(Ks[m - 1] * mp.cos(m * th) for m in range(1, n - 1))
                worst = min(worst, gap)
        return kind, n, worst
    if kind == 'rep':
        err = mp.mpf(0)
        for m in (1, n - 2):
            for p, q in (('0.2', '0.7'), ('0.05', '2')):
                p, q = mp.mpf(p), mp.mpf(q)
                rep = mp.quad(lambda t: chi_prime(n, m, t) * mp.e ** (-m * max(p, t) / 2) * mp.e ** (-m * max(q, t) / 2), [0, p, q, q + 5, q + 40]) / m
                err = max(err, abs(rep - K(n, m, p, q)) / K(n, m, p, q))
        return kind, n, err
if __name__ == "__main__":
    jobs = [(k, n) for k in ('psd', 'pair', 'rep') for n in (3, 4, 5, 7, 10, 16)]
    with Pool(18) as pool: out = pool.map(job, jobs, chunksize=1)
    for kind in ('psd', 'pair', 'rep'):
        print(kind, {o[1]: mp.nstr(o[2], 4) for o in out if o[0] == kind})
