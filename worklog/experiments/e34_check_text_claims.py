"""E34. Small checks of statements written in docs/THEORY.md §4 (evidence only, single process).
 (1) normalised form  D = (chi_0(q)-chi_0(p))/2 + sum_m e^{-m alpha} sqrt(sigma_m(p) sigma_m(q)) (kappa_m(q)-kappa_m(p)) cos(m theta),
     kappa_m = k_m/(m Gamma_m) = chi_m/sigma_m in [0,1).
 (2) the 'ideal' monotonicity (candidate D): x -> Phi(x) = chi_0(x)/2 + sum_m e^{-m alpha} chi_m(x) cos(m theta) nondecreasing?  (expected: false)
 (3) coefficientwise Aczel:  ell_m >= sqrt(A_m(p) A_m(q))."""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 30
n = 8; al, b = mp.mpf('0.5'), mp.mpf('0.2'); p, q = al - b, al + b
chi = lambda m, x: mp.e ** (m * x) * e.k(n, m, x)
G = {(m, x): e.Gam(n, m, x) for m in range(1, n - 1) for x in (p, q)}
sig = lambda m, x: m * mp.e ** (m * x) * G[(m, x)]
kap = lambda m, x: chi(m, x) / sig(m, x)
for th in (mp.pi, mp.pi / 3):
    D1 = (e.k(n, 0, q) - e.k(n, 0, p)) / 2 + sum(mp.sqrt(G[(m, p)] * G[(m, q)]) * (e.k(n, m, q) / G[(m, q)] - e.k(n, m, p) / G[(m, p)]) * mp.cos(m * th) for m in range(1, n - 1))
    D2 = (chi(0, q) - chi(0, p)) / 2 + sum(mp.e ** (-m * al) * mp.sqrt(sig(m, p) * sig(m, q)) * (kap(m, q) - kap(m, p)) * mp.cos(m * th) for m in range(1, n - 1))
    print(f"(1) theta={mp.nstr(th,4)}: D (original) = {mp.nstr(D1, 15)},  normalised form = {mp.nstr(D2, 15)}")
print("    kappa_m(p), m=1..n-2:", [mp.nstr(kap(m, p), 4) for m in range(1, n - 1)])
# (2)
al2 = mp.mpf('0.15')
Phi = lambda x, th: chi(0, x) / 2 + sum(mp.e ** (-m * al2) * chi(m, x) * mp.cos(m * th) for m in range(1, n - 1))
th = 2 * mp.pi * mp.mpf(3) / (2 * n - 3)
vals = [(x, Phi(mp.mpf(x), th)) for x in ('0.15', '0.3', '0.6', '1.2', '3', '8')]
print("(2) Phi(x) at alpha=0.15, theta=%s:" % mp.nstr(th, 4), [(x, mp.nstr(v, 4)) for x, v in vals])
# (3)
ok = True
for m in range(1, n - 1):
    Ap, Aq = mp.e ** (-m * p) / m - G[(m, p)], mp.e ** (-m * q) / m - G[(m, q)]
    ell = mp.e ** (-m * al) / m - mp.sqrt(G[(m, p)] * G[(m, q)])
    ok = ok and ell >= mp.sqrt(Ap * Aq)
print("(3) ell_m >= sqrt(A_m(p)A_m(q)) for all m:", ok)
