"""E42 (evidence only).  (H*):  Delta(theta) = (k_0(al)-k_0(p))/2 + sum_{m=1}^{n-2} d_m cos(m theta) >= 0,
   d_m = k_m(al) - k_m(p) sqrt(Gam_m(q)/Gam_m(p)),  al=(p+q)/2,  p<=q.
Print the coefficient sequence (d_0 := k_0(al)-k_0(p)), its signs, first/second differences, and min of Delta."""
import mpmath as mp, sys
import e20_closed_form as e
mp.mp.dps = 30
def coeffs(n, p, q):
    al = (p + q) / 2
    d = [e.k(n, 0, al) - e.k(n, 0, p)]
    for m in range(1, n - 1):
        d.append(e.k(n, m, al) - e.k(n, m, p) * mp.sqrt(e.Gam(n, m, q) / e.Gam(n, m, p)))
    return d
def report(n, p, q, show=False):
    p, q = mp.mpf(p), mp.mpf(q); d = coeffs(n, p, q)
    seq = d + [mp.mpf(0), mp.mpf(0)]
    neg = sum(1 for x in d if x < 0)
    noninc = sum(1 for j in range(len(d) - 1) if d[j + 1] > d[j] and j >= 1)
    nonconv = sum(1 for j in range(len(seq) - 2) if seq[j] - 2 * seq[j + 1] + seq[j + 2] < 0)
    mn = min(d[0] / 2 + sum(d[m] * mp.cos(m * mp.pi * j / (8 * n)) for m in range(1, n - 1)) for j in range(8 * n + 1))
    print(f"n={n} p={float(p)} q={float(q)}: #neg={neg} #increase={noninc} #nonconvex={nonconv}  min Delta={mp.nstr(mn,4)}  d0/2={mp.nstr(d[0]/2,4)}")
    if show: print("   d/d1:", [mp.nstr(x / d[1], 4) for x in d])
if __name__ == "__main__":
    for n in (4, 6, 10, 16):
        for p, q in (('0.02', '0.03'), ('0.02', '0.5'), ('0.2', '0.3'), ('0.2', '1.2'), ('0.6', '0.61'), ('0.6', '2.6'), ('1.5', '1.6'), ('1.5', '5')):
            report(n, p, q, show=(n == 6 and p in ('0.2',)))
