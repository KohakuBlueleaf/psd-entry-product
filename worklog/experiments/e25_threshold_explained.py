"""E25. Leading-order (in e^{-n alpha}) formula for the coefficients of D_{p,q}, p = alpha-b, q = alpha+b, N = n-m:
   a_m ~ 2 e^{-n alpha} { N[ (N-1)/(n-1) e^{alpha} sinh((N-1)b) - (N+1)/(n+1) e^{-alpha} sinh((N+1)b) ] - (2n/(n+m)) e^{-m alpha} sinh(n b) }
(a_0 = 2 d_0).  Compare with the exact coefficients; then the predicted Fejer threshold
   n*(alpha) = 6 sinh(alpha) / (1 - e^{-alpha})^2   (first second-difference changes sign), minimised over alpha."""
import mpmath as mp, numpy as np
import e20_closed_form as e
mp.mp.dps = 80
def exact(n, p, q):
    k, k0m1 = e.k, e.k0m1
    Gam = lambda m, x: mp.quad(lambda w: k(n, m, w), [x, x + mp.mpf(1) / 4, x + 1, x + 3, x + 8, x + 20, x + 60, x + 150])
    a = [2 * (k0m1(n, q) - k0m1(n, p))]
    for m in range(1, n - 1):
        Gp, Gq = Gam(m, p), Gam(m, q)
        a.append(mp.sqrt(Gp * Gq) * (k(n, m, q) / Gq - k(n, m, p) / Gp))
    return a
def approx(n, al, b):
    out = []
    for m in range(0, n - 1):
        N = n - m
        out.append(2 * mp.e ** (-n * al) * (N * ((N - 1) / mp.mpf(n - 1) * mp.e ** al * mp.sinh((N - 1) * b) - (N + 1) / mp.mpf(n + 1) * mp.e ** (-al) * mp.sinh((N + 1) * b)) - 2 * n / mp.mpf(n + m) * mp.e ** (-m * al) * mp.sinh(n * b)))
    return out
for n, al, b in ((20, mp.mpf('0.755'), mp.mpf('0.005')), (20, mp.mpf('1.5'), mp.mpf('0.3')), (30, mp.mpf('0.755'), mp.mpf('0.005'))):
    ex, ap = exact(n, al - b, al + b), approx(n, al, b)
    print(f"n={n} alpha={al} b={b}: exact/approx for m=0..5: {[mp.nstr(ex[m] / ap[m], 6) for m in range(6)]};  "
          f"rel. first second difference: exact {mp.nstr((ex[0]-2*ex[1]+ex[2])/ex[0], 4)}, approx {mp.nstr((ap[0]-2*ap[1]+ap[2])/ap[0], 4)}")
al = np.linspace(0.2, 2.5, 2301); f = 6 * np.sinh(al) / (1 - np.exp(-al)) ** 2
print(f"leading-order threshold: min over alpha of 6 sinh(a)/(1-e^-a)^2 = {f.min():.3f} at alpha = {al[f.argmin()]:.3f}")
