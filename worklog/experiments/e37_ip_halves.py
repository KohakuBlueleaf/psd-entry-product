"""E37 (evidence only).  (IP):  P_a >= Pi_p^{1/lam} + Pi_q^{lam}.   Do the two halves hold separately?
   (H_in)   P_a/2 - Pi_p^{1/lam} = xi_0(p)/2 + sum_m e^{-m a} (1 - chi_m(p) mu_m) cos(m th)   >= 0 ?
   (H_out)  P_a/2 - Pi_q^{lam}   = xi_0(q)/2 + sum_m e^{-m a} (1 - chi_m(q)/mu_m) cos(m th)   >= 0 ?
 mu_m = sqrt(sigma_m(q)/sigma_m(p)) >= 1,  chi_m(x) = e^{m x} k_m(x)  (chi = 0, i.e. coefficient e^{-m a}, for m >= n-1)."""
import mpmath as mp
import e20_closed_form as e
mp.mp.dps = 30
def halves(n, al, b):
    p, q = al - b, al + b
    cin = [(1 - e.k(n, 0, p)) / 2]; cout = [(1 - e.k(n, 0, q)) / 2]
    for m in range(1, n - 1):
        Gp, Gq = e.Gam(n, m, p), e.Gam(n, m, q)
        lam = mp.sqrt(Gp / Gq)
        cin.append(mp.e ** (-m * al) - e.k(n, m, p) / lam); cout.append(mp.e ** (-m * al) - lam * e.k(n, m, q))
    return cin, cout
def val(c, n, al, th):
    r = mp.e ** (-al)
    tail = sum(r ** m * mp.cos(m * th) for m in range(n - 1, 400))
    return c[0] + sum(c[m] * mp.cos(m * th) for m in range(1, n - 1)) + tail
for n in (4, 6, 10, 16):
    wi = wo = mp.inf; ai = ao = None
    for al, b in (('0.3', '0.1'), ('0.3', '0.29'), ('0.8', '0.05'), ('0.8', '0.3'), ('0.8', '0.79'), ('1.5', '0.5'), ('1.5', '1.49'), ('3', '2.9'), ('0.05', '0.04')):
        cin, cout = halves(n, mp.mpf(al), mp.mpf(b))
        for j in range(1, 6 * n + 1):
            th = mp.pi * j / (6 * n)
            r = mp.e ** (-mp.mpf(al)); P = (1 - r * r) / (1 - 2 * r * mp.cos(th) + r * r)
            vi, vo = val(cin, n, mp.mpf(al), th) / P, val(cout, n, mp.mpf(al), th) / P
            if vi < wi: wi, ai = vi, (al, b, j / (6 * n))
            if vo < wo: wo, ao = vo, (al, b, j / (6 * n))
    print(f"n={n}: min (H_in)/P = {mp.nstr(wi, 4)} at {ai};   min (H_out)/P = {mp.nstr(wo, 4)} at {ao}")
