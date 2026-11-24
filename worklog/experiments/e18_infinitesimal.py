"""E18. Infinitesimal form of (**).  With gamma_m(u) = c_m(e^u), Lambda_0(u) = c_0(e^u):
   w(x) = -Lambda_0''(a) - sum_m gamma_m (log gamma_m)''(a) T_m(x)
is the b^2-coefficient of W.  Print its coefficients, its values at the nodes, and its minimum on [-1,1].
Also: is (g - R)/b^2 increasing in b (so that the infinitesimal inequality would imply the finite one)?"""
import mpmath as mp
from e13c_gm_certificate_mp import coeffs
mp.mp.dps = 40
def gam(n, u): return coeffs(n, mp.e ** u)
for n in (4, 5, 6, 7):
    for a in (-2.0, -0.7, 0.0):
        D = len(gam(n, a))
        d2 = [mp.diff(lambda u, m=m: (gam(n, u)[m] if m == 0 else mp.log(gam(n, u)[m])), a, 2) for m in range(D)]
        g = gam(n, a)
        co = [-d2[0]] + [-g[m] * d2[m] for m in range(1, D)]
        w = lambda th: sum(co[m] * mp.cos(m * th) for m in range(D))
        vals = [w(mp.pi * k / 400) for k in range(401)]
        kmin = min(range(401), key=lambda k: vals[k])
        nodes = [mp.nstr(w(2 * mp.pi * k / n) / co[0], 4) for k in range(1, n // 2 + 1)]
        print(f"n={n} a={a:+.1f}: coeffs/co0 = {[mp.nstr(c / co[0], 4) for c in co]}  min w/co0 = {mp.nstr(vals[kmin] / co[0], 4)} at theta/pi={kmin/400:.3f}; at nodes {nodes}")
print("monotonicity of min_x (g-R)/b^2 in b:")
for n in (4, 5):
    for a in (-1.0, 0.0):
        row = []
        for b in (0.05, 0.2, 0.5, 1.0, 2.0):
            cs, ct = gam(n, a + b), gam(n, a - b); tau = mp.e ** a
            R = [(cs[0] + ct[0]) / 2] + [mp.sqrt(cs[m] * ct[m]) for m in range(1, len(cs))]
            v = min(-mp.log(1 + tau * tau - 2 * tau * mp.cos(mp.pi * k / 300)) / 2 - sum(R[m] * mp.cos(m * mp.pi * k / 300) for m in range(len(R))) for k in range(1, 301))
            row.append(mp.nstr(v / b ** 2, 4))
        print(f"  n={n} a={a:+.1f}: {row}")
