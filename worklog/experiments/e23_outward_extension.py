"""E23. Pieces of the exact decomposition
    L = (1/2)[E_p(e^{-b} e^{i th}) + E_q(e^{b} e^{i th})] + (1/2) sum_m eps_m^2 cos(m th).
 (i)  I_w(beta, th) = harmonic extension to radius e^beta of (1/2) rho_n(w) Fej_n(th) P_w(th):  is it >= 0 for 0 <= beta < w ?
 (ii) is  S = (1/2)[E_p(e^{-b}.) + E_q(e^{b}.)]  >= 0 ?   is  S >= E_alpha (convexity of F at the midpoint) ?
 (iii) size of the third term relative to S."""
import numpy as np
def S_m(n, m, w):
    l = np.arange(-(n - 1), n)
    return np.sum((n - np.abs(l)) * np.exp(-np.abs(m - l) * w))
def I(n, w, beta, th, M=400):
    rho = (np.cosh(w) - 1) / (np.cosh(n * w) - 1)
    tot = 0.5 * rho * S_m(n, 0, w)
    for m in range(1, M):
        c = rho * S_m(n, m, w) if m < n else np.exp(-m * w)
        tot = tot + c * np.exp(m * beta) * np.cos(m * th)
    return tot
th = np.linspace(0, np.pi, 721)
for n in (4, 6, 9):
    worst = np.inf; arg = None
    for w in (0.3, 0.8, 1.5, 3.0):
        for frac in (0.2, 0.5, 0.8, 0.95):
            v = I(n, w, frac * w, th); j = np.argmin(v)
            if v[j] / v.max() < worst: worst, arg = v[j] / v.max(), (w, frac, th[j] / np.pi)
    print(f"n={n}: min over (w, beta/w, theta) of I/max I = {worst:+.4e} at {arg}")
