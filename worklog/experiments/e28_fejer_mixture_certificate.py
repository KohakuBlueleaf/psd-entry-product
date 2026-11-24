"""E28. A different rank structure.  Second differences in m:  k_{m-1} - 2k_m + k_{m+1} = 2 rho_n(w) sinh((n-m)w), hence
    Gamma_m(x) = 2 sum_{j=1}^{n-m-1} (n-m-j) B_j(x),     B_j(x) = int_x^inf rho_n(w) sinh(j w) dw   (1 <= j <= n-2),
i.e. the certificate is a POSITIVE MIXTURE OF FEJER KERNELS:  h_x = const + sum_j B_j(x) Fej_{n-j}(theta).
Take the geometric mean in this representation:   K_m(p,q) = 2 sum_j (n-m-j)_+ sqrt(B_j(p) B_j(q))   (PD, diagonal Gamma_m).
Pair certificate:  R(theta) = (Gamma_0(p)+Gamma_0(q))/2 - sum_j (n-j) beta_j + sum_j beta_j Fej_{n-j}(theta),  beta_j = sqrt(B_j(p)B_j(q)).
Tests:  (i) g_alpha >= R for all theta ?    (ii) theta-free sufficient condition (needs B_j log-concave):
        Btil(alpha) - (Btil(p)+Btil(q))/2  >=  (1/2) sum_j (n-j) (sqrt(B_j(p)) - sqrt(B_j(q)))^2,   Btil(x) = int_x^inf (rho_n sinh((n-1)w) - 1/2) dw."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e

def rho(n, w): return (mp.sinh(w / 2) / mp.sinh(n * w / 2)) ** 2 if w != 0 else mp.mpf(1) / n ** 2
def pts(x): return [x, x + mp.mpf(1) / 4, x + 1, x + 3, x + 8, x + 20, x + 60, x + 150]
def B(n, j, x): return mp.quad(lambda w: rho(n, w) * mp.sinh(j * w), pts(x))
def Btil(n, x):
    f = lambda w: rho(n, w) * mp.sinh((n - 1) * w) - mp.mpf(1) / 2
    return mp.quad(f, pts(x))
def fej(M, th): return (1 - mp.cos(M * th)) / (1 - mp.cos(th)) if th != 0 else mp.mpf(M) ** 2

def job(args):
    n, p, q = args; mp.mp.dps = 40
    al = (p + q) / 2; tau = mp.e ** (-al)
    Bp = [B(n, j, p) for j in range(1, n - 1)]; Bq = [B(n, j, q) for j in range(1, n - 1)]; Ba = [B(n, j, al) for j in range(1, n - 1)]
    beta = [mp.sqrt(x * y) for x, y in zip(Bp, Bq)]
    G0p, G0q = e.Gam(n, 0, p), e.Gam(n, 0, q)
    # consistency: Gamma_1 = 2 sum (n-1-j) B_j
    cons = abs(e.Gam(n, 1, p) - 2 * sum((n - 1 - j) * Bp[j - 1] for j in range(1, n - 1)))
    const = (G0p + G0q) / 2 - sum((n - j) * beta[j - 1] for j in range(1, n - 1))
    best = mp.inf; arg = None
    for i in range(1, 8 * n + 1):
        th = mp.pi * i / (8 * n)
        v = -mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 - const - sum(beta[j - 1] * fej(n - j, th) for j in range(1, n - 1))
        if v < best: best, arg = v, i / (8 * n)
    scale = sum((n - j) * Bp[j - 1] for j in range(1, n - 1))
    lhs = Btil(n, al) - (Btil(n, p) + Btil(n, q)) / 2
    rhs = sum((n - j) * (mp.sqrt(Bp[j - 1]) - mp.sqrt(Bq[j - 1])) ** 2 for j in range(1, n - 1)) / 2
    logc = all(Ba[j] ** 2 >= Bp[j] * Bq[j] for j in range(n - 2))
    return n, float(p), float(q), best / scale / (p - q) ** 2, arg, (lhs - rhs) / scale / (p - q) ** 2, logc, cons < mp.mpf(10) ** (-25)

if __name__ == "__main__":
    pairs = [(0, 0.05), (0, 0.6), (0, 3), (0.1, 0.15), (0.1, 1), (0.4, 0.45), (0.4, 1.5), (0.8, 0.85), (0.8, 3), (1.5, 1.6), (1.5, 4), (3, 3.1), (3, 7)]
    jobs = [(n, mp.mpf(p), mp.mpf(q)) for n in (3, 4, 5, 6, 8, 12, 16, 20) for p, q in pairs]
    with Pool(32) as pool: out = pool.map(job, jobs)
    for n in (3, 4, 5, 6, 8, 12, 16, 20):
        rows = [o for o in out if o[0] == n]; w = min(rows, key=lambda o: o[3]); s = min(rows, key=lambda o: o[5])
        print(f"n={n:2d}: (i) min normalised g-R = {mp.nstr(w[3], 4)} at (p,q,th/pi)=({w[1]},{w[2]},{w[4]:.3f});  "
              f"(ii) min normalised slack = {mp.nstr(s[5], 4)} at ({s[1]},{s[2]});  B_j log-concave: {all(o[6] for o in rows)};  formula check: {all(o[7] for o in rows)}")
