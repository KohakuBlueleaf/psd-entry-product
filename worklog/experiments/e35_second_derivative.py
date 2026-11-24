"""E35 (evidence only, one process).  Exact formula
   L''(y) = (k_0'(p)+k_0'(q))/4 + sum_m cos(m theta) sqrt(Gamma_m(p)Gamma_m(q)) [ (r_m'(p)+r_m'(q))/2 - (r_m(q)-r_m(p))^2/4 ],
p = alpha - y, q = alpha + y, r_m = k_m/Gamma_m.  (1) check against a finite difference of L;  (2) is L'' >= 0 for all theta?"""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 30
def L(n, al, y, th):
    p, q = al - y, al + y; tau = mp.e ** (-al)
    return -mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 - (e.Gam(n, 0, p) + e.Gam(n, 0, q)) / 2 - sum(mp.sqrt(e.Gam(n, m, p) * e.Gam(n, m, q)) * mp.cos(m * th) for m in range(1, n - 1))
def Lpp_coeffs(n, al, y):
    p, q = al - y, al + y
    dk = lambda m, x: mp.diff(lambda w: e.k(n, m, w), x)
    out = [(dk(0, p) + dk(0, q)) / 4]
    for m in range(1, n - 1):
        Gp, Gq = e.Gam(n, m, p), e.Gam(n, m, q)
        rp, rq = e.k(n, m, p) / Gp, e.k(n, m, q) / Gq
        rpp, rqp = dk(m, p) / Gp + rp ** 2, dk(m, q) / Gq + rq ** 2
        out.append(mp.sqrt(Gp * Gq) * ((rpp + rqp) / 2 - (rq - rp) ** 2 / 4))
    return out
n, al, y, th = 7, mp.mpf('0.8'), mp.mpf('0.3'), mp.mpf('2.1'); h = mp.mpf('1e-5')
c = Lpp_coeffs(n, al, y)
fd = (L(n, al, y + h, th) - 2 * L(n, al, y, th) + L(n, al, y - h, th)) / h ** 2
print("(1) formula:", mp.nstr(c[0] + sum(c[m] * mp.cos(m * th) for m in range(1, n - 1)), 12), "  finite difference:", mp.nstr(fd, 12))
print("(2) min over theta of L''/sum|coeff|, and sign of coefficients:")
for n in (6, 12, 20):
    for al, y in (('0.8', '0.05'), ('0.8', '0.4'), ('0.8', '0.79'), ('0.2', '0.19'), ('2.0', '1.5')):
        c = Lpp_coeffs(n, mp.mpf(al), mp.mpf(y))
        v = min(c[0] + sum(c[m] * mp.cos(m * mp.pi * j / (6 * n)) for m in range(1, n - 1)) for j in range(6 * n + 1))
        print(f"   n={n} alpha={al} y={y}: min = {mp.nstr(v / sum(abs(x) for x in c), 4)};  #negative coefficients = {sum(1 for x in c[1:] if x < 0)}")
