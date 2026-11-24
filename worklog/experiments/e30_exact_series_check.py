"""E30. Check the exact power series for zeta_m and Gamma_0, and the decomposition W = W_lin + W_rho (notes/exact-series.md)."""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 40
def zeta_series(n, m, x, J=400):
    s = mp.e ** (-x); N = n - m
    t1 = sum(j * (s ** (j * n - 1 - m) / (j * n - 1) - s ** (j * n + 1 - m) / (j * n + 1)) for j in range(1, J))
    t2 = sum((j + 1) * s ** (j * n) / (j * n + m) for j in range(1, J))
    t3 = sum((j - 1) * s ** (j * n - 2 * m) / (j * n - m) for j in range(2, J))
    return m * (N * t1 - t2 + t3)
def gam0_series(n, x, J=400):
    s = mp.e ** (-x)
    return sum(s ** (j * n) / (j * n) for j in range(1, J)) - mp.mpf(n) / 2 * sum(j * (s ** (j * n - 1) / (j * n - 1) - s ** (j * n + 1) / (j * n + 1)) for j in range(1, J))
ch = lambda y: mp.cosh(y) - 1
def c_lin(n, m, al, b, J=400):
    N = n - m; tot = mp.mpf(0)
    for j in range(1, J):
        tot += N * j * (mp.e ** (-(j * n - 1) * al) * ch((j * n - 1 - m) * b) / (j * n - 1) - mp.e ** (-(j * n + 1) * al) * ch((j * n + 1 - m) * b) / (j * n + 1))
        tot -= (j + 1) * mp.e ** (-(j * n + m) * al) * ch(j * n * b) / (j * n + m)
        tot += (j - 1) * mp.e ** (-(j * n - m) * al) * ch((j * n - 2 * m) * b) / (j * n - m)
    return tot
n = 7; x = mp.mpf('0.6')
for m in (1, 3, 5):
    exact = 1 - m * mp.e ** (m * x) * e.Gam(n, m, x)
    print(f"zeta_{m}: integral {mp.nstr(exact, 20)}  series {mp.nstr(zeta_series(n, m, x), 20)}")
print("Gamma_0: integral", mp.nstr(e.Gam(n, 0, x), 20), " series", mp.nstr(gam0_series(n, x), 20))
al, b = mp.mpf('0.9'), mp.mpf('0.35'); p, q = al - b, al + b
d0 = e.Gam(n, 0, al) - (e.Gam(n, 0, p) + e.Gam(n, 0, q)) / 2
print("delta_0:", mp.nstr(d0, 18), " c_0/2:", mp.nstr(c_lin(n, 0, al, b) / 2, 18))
for m in (1, 2, 4, 5):
    Ga, Gp, Gq = e.Gam(n, m, al), e.Gam(n, m, p), e.Gam(n, m, q)
    delta = Ga - mp.sqrt(Gp * Gq)
    sp_, sq_ = m * mp.e ** (m * p) * Gp, m * mp.e ** (m * q) * Gq
    rho = mp.e ** (-m * al) / (2 * m) * (mp.sqrt(sp_) - mp.sqrt(sq_)) ** 2
    print(f"m={m}: delta_m = {mp.nstr(delta, 16)}   c_m + rho_m = {mp.nstr(c_lin(n, m, al, b) + rho, 16)}   (c_m = {mp.nstr(c_lin(n, m, al, b), 6)}, rho_m = {mp.nstr(rho, 6)})")
