"""E20. Closed form for the 'Fejer' certificate (degree n-2, all n).  For s = e^{-p}, p >= 0:
    g_s(theta) - h_s(theta) = (1/2) * Fej_n(theta) * int_p^inf rho_n(w) P_w(theta) dw,
    Fej_n = (1-cos n theta)/(1-cos theta),  rho_n(w) = (cosh w - 1)/(cosh nw - 1),  P_w = sinh w/(cosh w - cos theta),
and the Chebyshev coefficients are tail integrals of explicit positive kernels:
    c_m(s) = Gamma_m(p) = int_p^inf k_m(w) dw,   k_m(w) = (sinh((n-m)w) - (n-m) sinh w)/(cosh nw - 1),  1 <= m <= n-2,
    c_0(s) = Gamma_0(p) = int_p^inf (k_0(w) - 1)/2 dw.
Checks: (1) agreement with n=3,4 closed forms; (2) interpolation at the roots of unity; (3) (**) for many n."""
import mpmath as mp, sys
from multiprocessing import Pool
mp.mp.dps = 30
def k(n, m, w):
    if w == 0: return mp.mpf(0)
    return (mp.sinh((n - m) * w) - (n - m) * mp.sinh(w)) / (2 * mp.sinh(n * w / 2) ** 2)
def k0m1(n, w):
    """(k_0(w) - 1)/2 in a cancellation-free form."""
    if w == 0: return mp.mpf(-1) / 2
    return (1 - mp.e ** (-n * w) - n * mp.sinh(w)) / (4 * mp.sinh(n * w / 2) ** 2)
def Gam(n, m, p):
    f = (lambda w: k(n, m, w)) if m >= 1 else (lambda w: k0m1(n, w))
    return mp.quad(f, [p, p + mp.mpf(1) / 4, p + 1, p + 3, p + 8, p + 20, p + 60, p + 150])
def g(s, th): return -mp.log(1 + s * s - 2 * s * mp.cos(th)) / 2

def check_basic():
    p = mp.mpf('0.7'); s = mp.e ** (-p)
    print("n=3 c_1:", mp.nstr(Gam(3, 1, p), 15), "closed form", mp.nstr(s / (1 + s + s * s), 15))
    y = 1 / mp.cosh(p)
    print("n=4 c_1:", mp.nstr(Gam(4, 1, p), 15), "closed form y/2 =", mp.nstr(y / 2, 15))
    print("n=4 c_2:", mp.nstr(Gam(4, 2, p), 15), "closed form (y-log(1+y))/4 =", mp.nstr((y - mp.log(1 + y)) / 4, 15))
    for n in (5, 8):
        cs = [Gam(n, m, p) for m in range(n - 1)]
        err = max(abs(g(s, 2 * mp.pi * j / n) - sum(cs[m] * mp.cos(2 * mp.pi * j * m / n) for m in range(n - 1))) for j in range(1, n))
        tot = (n - 1) * cs[0] - sum(cs[1:]) + mp.log(sum(s ** j for j in range(n)))
        print(f"n={n}: max interpolation error at nontrivial roots = {mp.nstr(err, 3)};  total identity defect = {mp.nstr(tot, 3)}")

def job(args):
    n, p, q = args
    mp.mp.dps = 30
    a = (p + q) / 2; tau = mp.e ** (-a)
    cp_, cq = [Gam(n, m, p) for m in range(n - 1)], [Gam(n, m, q) for m in range(n - 1)]
    R = [(cp_[0] + cq[0]) / 2] + [mp.sqrt(cp_[m] * cq[m]) for m in range(1, n - 1)]
    best = mp.inf; arg = None
    for j in range(1, 6 * n + 1):
        th = mp.pi * j / (6 * n)
        v = g(tau, th) - sum(R[m] * mp.cos(m * th) for m in range(n - 1))
        if v < best: best, arg = v, j / (6 * n)
    return n, float(p), float(q), best / (cp_[1] + cq[1]) / (p - q) ** 2, arg

if __name__ == "__main__":
    check_basic()
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (4, 5, 6, 8, 10, 12, 16, 24)
            for (p, q) in ((0, 0.1), (0, 1), (0.3, 0.5), (0.5, 2.5), (1, 1.2), (2, 2.3), (3, 6), (4, 4.2), (0, 5))]
    with Pool(60) as pool: out = pool.map(job, jobs)
    for n in (4, 5, 6, 8, 10, 12, 16, 24):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3])
        print(f"n={n:2d}: min normalised (g-R)/(p-q)^2 = {mp.nstr(w[3], 5)} at p={w[1]}, q={w[2]}, theta/pi={w[4]:.3f};  all >= 0: {all(o[3] >= 0 for o in rows)}")
