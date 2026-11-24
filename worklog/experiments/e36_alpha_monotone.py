"""E36 (evidence only).  For fixed b, is the gap L(alpha, b; theta) nonincreasing in alpha?
   -2 dL/dalpha = P_alpha(theta) - Pi_p^{1/lam}(theta) - Pi_q^{lam}(theta)
               = 1 - (k_0(p)+k_0(q))/2 + sum_{m>=1} [ 2 e^{-m alpha} - k_m(p)/lam_m - lam_m k_m(q) ] cos(m theta),
 p = alpha-b, q = alpha+b, lam_m = sqrt(Gamma_m(p)/Gamma_m(q)) (for m <= n-2; the bracket is 2 e^{-m alpha} for m >= n-1).
Since L -> 0 as alpha -> infinity, this would give Star directly."""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 30
def coeffs(n, al, b):
    p, q = al - b, al + b
    c0 = -(e.k(n, 0, p) + e.k(n, 0, q)) / 2
    cm = []
    for m in range(1, n - 1):
        Gp, Gq = e.Gam(n, m, p), e.Gam(n, m, q)
        lam = mp.sqrt(Gp / Gq)
        cm.append(e.k(n, m, p) / lam + lam * e.k(n, m, q))
    return c0, cm
def neg2dL(n, al, cf, th):
    c0, cm = cf
    r = mp.e ** (-al)
    P = (1 - r * r) / (1 - 2 * r * mp.cos(th) + r * r)
    return P + c0 - sum(cm[m - 1] * mp.cos(m * th) for m in range(1, n - 1)), P
for n in (4, 6, 10, 16):
    worst = mp.inf; arg = None
    for al, b in (('0.3', '0.0'), ('0.3', '0.1'), ('0.3', '0.29'), ('0.8', '0.3'), ('0.8', '0.79'), ('1.5', '0.5'), ('1.5', '1.49'), ('3', '2.9'), ('0.05', '0.04')):
        cf = coeffs(n, mp.mpf(al), mp.mpf(b))
        for j in range(1, 6 * n + 1):
            th = mp.pi * j / (6 * n)
            v, P = neg2dL(n, mp.mpf(al), cf, th)
            if v / P < worst: worst, arg = v / P, (al, b, j / (6 * n))
    print(f"n={n}: min of (-2 dL/dalpha)/P_alpha = {mp.nstr(worst, 5)} at (alpha,b,theta/pi)={arg}")
