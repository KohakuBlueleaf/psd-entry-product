"""E32. Compact exact formulas (to be verified) and the sign of second differences, family by family.
  Upsilon(x) = int_x^inf sinh(w)/(cosh(n w) - 1) dw,
  V_m(x) = e^{m x} int_x^inf e^{-m w} [ (1-e^{-n w})^{-2} - 1 ] dw,     Z_m(x) = e^{m x} int_x^inf e^{m w} e^{-2 n w} (1-e^{-n w})^{-2} dw,
  A_m(x) = e^{-m x}/m - Gamma_m(x) = (n-m) Upsilon(x) - e^{-m x} (V_m(x) - Z_m(x))            [coefficients of the error E_x]
  c_m = D_b[ x -> A_m(x) e^{m (x - alpha)} ](alpha),   D_b[f](alpha) = (f(alpha-b) + f(alpha+b))/2 - f(alpha).
Then: for each family, how many second differences (in m) are negative, for several (n, alpha, b) including p = alpha - b near 0."""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 40
def pts(x): return [x, x + mp.mpf(1) / 8, x + mp.mpf(1) / 2, x + 2, x + 6, x + 20, x + 60]
def Ups(n, x): return mp.quad(lambda w: mp.sinh(w) / (2 * mp.sinh(n * w / 2) ** 2) if w != 0 else mp.mpf(0), pts(x))
def V(n, m, x): return mp.e ** (m * x) * mp.quad(lambda w: mp.e ** (-m * w) * ((1 - mp.e ** (-n * w)) ** -2 - 1), pts(x))
def Z(n, m, x): return mp.e ** (m * x) * mp.quad(lambda w: mp.e ** (m * w - 2 * n * w) * (1 - mp.e ** (-n * w)) ** -2, pts(x))
n = 9; x = mp.mpf('0.4')
for m in (1, 4, 7):
    lhs = mp.e ** (-m * x) / m - e.Gam(n, m, x)
    rhs = (n - m) * Ups(n, x) - mp.e ** (-m * x) * (V(n, m, x) - Z(n, m, x))
    print(f"A_{m}: {mp.nstr(lhs, 18)}  formula {mp.nstr(rhs, 18)}")
def fams(n, al, b):
    p, q = al - b, al + b
    D = lambda f: (f(p) + f(q)) / 2 - f(al)
    U = {x: Ups(n, x) for x in (p, al, q)}
    f1 = [(n - m) * D(lambda x: mp.e ** (m * (x - al)) * U[x]) for m in range(0, n - 1)]
    f2 = [-D(lambda x: mp.e ** (-m * al) * V(n, m, x)) for m in range(0, n - 1)]
    f3 = [D(lambda x: mp.e ** (-m * al) * Z(n, m, x)) for m in range(0, n - 1)]
    return f1, f2, f3
def negs(seq):
    a = seq + [mp.mpf(0)] * 3
    ev = [a[j] - 2 * a[j + 1] + a[j + 2] for j in range(len(a) - 2)]
    return [j for j, v in enumerate(ev) if v < 0]
print("indices j with negative second difference, per family (family 1 = 'cubic', 2 = 'geometric', 3 = higher order):")
for n, al, b in ((12, '1.0', '0.2'), (12, '1.0', '0.999'), (12, '0.3', '0.29'), (12, '0.1', '0.05'), (24, '0.6', '0.01'), (24, '0.6', '0.59'), (24, '0.05', '0.049')):
    f1, f2, f3 = fams(n, mp.mpf(al), mp.mpf(b))
    tot = [x + y + z for x, y, z in zip(f1, f2, f3)]
    print(f"  n={n} alpha={al} b={b}:  fam1 {negs(f1)[:6]}  fam2 #neg={len(negs(f2))}  fam3 {negs(f3)[:6]}   lin total {negs(tot)[:8]}   |f3|/|f1| at m=1: {mp.nstr(abs(f3[1] / f1[1]), 3)}")
