"""E16. For even n the LP optimum is already reached in degree n-2 (see README of notes): Hermite interpolation
with double nodes at cos(2 pi k/n), 1 <= k < n/2, and a SIMPLE node at x = -1.  Does (**) hold for this family?
n = 4 is the first case with two nodes:  P_s(x) = alpha + beta x + gamma x^2."""
import mpmath as mp
mp.mp.dps = 40
def coeffs(n, tau):
    D = n - 2; rows, rhs = [], []
    q = lambda t: 1 + tau * tau - 2 * tau * mp.cos(t)
    for k in range(1, (n + 1) // 2 + (0 if n % 2 else 1)):
        t = 2 * mp.pi * k / n
        if 2 * k > n: break
        rows.append([mp.cos(m * t) for m in range(D + 1)]); rhs.append(-mp.log(q(t)) / 2)
        if 2 * k != n:
            rows.append([-m * mp.sin(m * t) for m in range(D + 1)]); rhs.append(-tau * mp.sin(t) / q(t))
    return mp.lu_solve(mp.matrix(rows), mp.matrix(rhs))
import random
random.seed(0)
for n in (4, 6, 8, 10):
    worst = mp.inf; mc = mp.inf; arg = None
    for _ in range(150):
        a = random.uniform(-4, 4); b = random.choice([0.03, 0.3, 1.0, 3.0])
        s, t, tau = mp.e ** (a + b), mp.e ** (a - b), mp.e ** a
        cs, ct = coeffs(n, s), coeffs(n, t)
        mc = min(mc, min(cs[m] for m in range(1, len(cs))) / cs[1])
        R = [(cs[0] + ct[0]) / 2] + [mp.sqrt(cs[m] * ct[m]) if cs[m] * ct[m] >= 0 else mp.nan for m in range(1, len(cs))]
        for k in range(1, 241):
            th = mp.pi * k / 240
            v = (-mp.log(1 + tau * tau - 2 * tau * mp.cos(th)) / 2 - sum(R[m] * mp.cos(m * th) for m in range(len(R)))) / (cs[1] + ct[1])
            if v < worst: worst, arg = v, (round(a, 2), b, k / 240)
    print(f"n={n} (degree {n-2}): min normalised g-R = {mp.nstr(worst, 5)} at (a,b,theta/pi)={arg};  min c_m/c_1 = {mp.nstr(mc, 4)}")
