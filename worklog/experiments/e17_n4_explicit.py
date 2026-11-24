"""E17. n = 4 with the degree-2 certificate  P_s(x) = alpha + beta x + gamma x^2,
    y = 1/cosh u (s = e^u),  beta = y/2,  gamma = (y - log(1+y))/2,  alpha = -log(1+s^2)/2.
(**) for n = 4 follows from  Q(x) = A + B x + q x^2 >= 0 on [-1,1], where (worst case u, v >= 0, a = (u+v)/2)
    A = (1/2) log(y_a / sqrt(y_u y_v)) - (1/4)(sqrt(gamma_u) - sqrt(gamma_v))^2,
    B = (y_a - sqrt(y_u y_v))/2,      q = gamma(y_a) - sqrt(gamma_u gamma_v).
Sufficient:  (I) Q(-1) = A - B + q >= 0   and   (II) B >= 2q   (given B >= 0).   Check on a grid, 50 digits."""
import mpmath as mp
mp.mp.dps = 50
gam = lambda y: (y - mp.log(1 + y)) / 2
def quantities(u, v):
    yu, yv, ya = 1 / mp.cosh(u), 1 / mp.cosh(v), 1 / mp.cosh((u + v) / 2)
    gu, gv = gam(yu), gam(yv)
    A = mp.log(ya / mp.sqrt(yu * yv)) / 2 - (mp.sqrt(gu) - mp.sqrt(gv)) ** 2 / 4
    B = (ya - mp.sqrt(yu * yv)) / 2
    q = gam(ya) - mp.sqrt(gu * gv)
    return A, B, q
wI = mp.inf; wII = mp.inf; wq = mp.inf; aI = aII = None
N = 60
for i in range(N + 1):
    for j in range(i):
        for scale in (8, 2, 0.5, 0.05):
            u, v = mp.mpf(i) * scale / N, mp.mpf(j) * scale / N
            A, B, q = quantities(u, v)
            b2 = (u - v) ** 2
            if (A - B + q) / b2 / B * b2 < wI: wI, aI = (A - B + q) / B, (float(u), float(v))
            if (B - 2 * q) / B < wII: wII, aII = (B - 2 * q) / B, (float(u), float(v))
            wq = min(wq, q / B)
print("min (A-B+q)/B =", mp.nstr(wI, 6), "at", aI)
print("min (B-2q)/B  =", mp.nstr(wII, 6), "at", aII)
print("min q/B       =", mp.nstr(wq, 6))
