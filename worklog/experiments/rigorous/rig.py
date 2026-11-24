"""Rigorous verification of the Fejer convexity criterion for W on the region 0 <= p <= q <= Q.

All arithmetic is ball arithmetic (python-flint / Arb).  See notes/rigorous-B.md for the mathematics.

Notation:  a_m(x) = rho_n(x) S_m(x) >= 0,   A_m(x) = int_x^oo a_m,   zeta_m(x) = m e^{m x} A_m(x)  (m >= 1),
           Gamma_0 = -A_0/2,   delta_m = e^{-m alpha}/m * tau_m,   2 delta_0 = A_0(p)/2 + A_0(q)/2 - A_0(alpha),
           tau_m = (zeta_p + zeta_q)/2 - zeta_alpha + (1/2)(zeta_p - zeta_q)^2 / (sqrt(1-zeta_p) + sqrt(1-zeta_q))^2,
           e_j = forward second differences of (2 delta_0, delta_1, ..., delta_{n-2}, 0, 0),  j = 0..n-2.
Criterion: e_j >= 0 for all j  ==>  W(theta) >= 0 for all theta.
"""
import sys, math
from flint import arb, arb_series, ctx

PREC = 320
ctx.prec = PREC


# ---------------------------------------------------------------------------------------------------------------
# one-variable jets (lists of arb, index = Taylor coefficient)
# ---------------------------------------------------------------------------------------------------------------
def ser(X, D):
    return arb_series([X, arb(1)], prec=D + 1)

def coeffs(s, D):
    c = s.coeffs()
    return [c[i] if i < len(c) else arb(0) for i in range(D + 1)]

def sinhc_series(y, D):
    """Jet of sinh(y)/y where y is an arb_series with ball constant term.  Rigorous for all real balls."""
    y0 = y.coeffs()[0]
    if y0.abs_upper() <= 0.5:
        y2 = y * y
        acc = arb_series([arb(0)], prec=D + 1)
        term = arb_series([arb(1)], prec=D + 1)
        K = 40
        for k in range(K):
            acc = acc + term * (arb(1) / arb.fac_ui(2 * k + 1))     # y^(2k)/(2k+1)!
            term = term * y2
        # tail sum_{k>=40} y^(2k)/(2k+1)!: every Taylor coefficient of order <= 16 at |y| <= 0.5 is < 1e-100 (see notes)
        assert D <= 16
        c = coeffs(acc, D)
        err = arb(0, 1e-100)
        return arb_series([ci + err for ci in c], prec=D + 1)
    if y0.abs_lower() < 0.1:
        raise ValueError("sinhc: ball straddles the switching region; use smaller cells")
    return ((y.exp() - (-y).exp()) / 2) / y

def a_jet(n, m, X, D):
    """Taylor coefficients (degree <= D) of a_m(x) = rho_n(x) S_m(x) at the ball X >= 0."""
    x = ser(X, D)
    r = sinhc_series(x * arb(0.5), D) / (sinhc_series(x * (arb(n) / 2), D) * n)
    rho = r * r
    S = arb_series([arb(0)], prec=D + 1)
    E = (-x).exp()
    pw = {0: arb_series([arb(1)], prec=D + 1)}
    cur = pw[0]
    for c in range(1, m + n):
        cur = cur * E
        pw[c] = cur
    for l in range(-(n - 1), n):
        S = S + pw[abs(m - l)] * (n - abs(l))
    return coeffs(rho * S, D)

def A_series_top(n, m, X):
    """A_m(X) from the power series in s = e^{-X}; requires s^n small.  Tail bound (N+2) s^{Jn}/(1-s^n)."""
    s = (-X).exp(); N = n - m
    sn = s ** n
    J = 4
    while float((sn ** J).abs_upper()) > 1e-110:
        J += 1
    tot = arb(0)
    for j in range(1, J + 1):
        tot += N * j * (s ** (j * n - 1) / (j * n - 1) - s ** (j * n + 1) / (j * n + 1))
        tot -= (j + 1) * s ** (j * n + m) / (j * n + m)
        if j >= 2:
            tot += (j - 1) * s ** (j * n - m) / (j * n - m)
    tail = (N + 2) * sn ** J / (1 - sn)
    return tot + arb(0, float(tail.abs_upper()) * 1.0001)

def integral_a(n, m, lo, hi, K=14):
    """Enclosure of int_lo^hi a_m by Taylor expansion at the midpoint (degree K-1) with interval remainder."""
    mid = (lo + hi) / 2; d = (hi - lo) / 2
    cp = a_jet(n, m, mid, K - 1)
    cb = a_jet(n, m, mid + arb(0, float(d.abs_upper()) * 1.0000001), K)
    tot = arb(0)
    for k in range(0, K, 2):
        tot += cp[k] * 2 * d ** (k + 1) / (k + 1)
    rem = cb[K].abs_upper() * 2 * d ** (K + 1) / (K + 1)
    return tot + arb(0, float(rem.abs_upper()) * 1.0001)


# ---------------------------------------------------------------------------------------------------------------
# tables on the half grid y_l = l*h/2
# ---------------------------------------------------------------------------------------------------------------
class Table:
    """A_m on the quarter grid t_i = i*h/4;  y_l = l*h/2 = t_{2l}."""
    def __init__(self, n, h_num, h_den, Q, d, extra=4):
        self.n, self.d, self.Q = n, d, Q
        self.h = arb(h_num) / h_den
        self.half = self.h / 2
        self.g = self.h / 4
        self.L = int(round(2 * Q * h_den / h_num))          # y_L = Q
        self.Ltop = self.L + extra
        top = 2 * self.Ltop
        self.A = [[None] * (top + 1) for _ in range(n - 1)]             # A[m][i] = A_m(t_i)
        for m in range(0, n - 1):
            self.A[m][top] = A_series_top(n, m, self.g * top)
            for i in range(top - 1, -1, -1):
                self.A[m][i] = self.A[m][i + 1] + integral_a(n, m, self.g * i, self.g * (i + 1))

    def y(self, l):
        return self.half * l

    def _jet(self, m, X, D, A0):
        aj = a_jet(self.n, m, X, max(D - 1, 0))
        Aj = [A0] + [-aj[k - 1] / k for k in range(1, D + 1)]
        if m == 0:
            return Aj, aj
        s = arb_series(Aj, prec=D + 1) * (ser(X, D) * m).exp() * m
        return coeffs(s, D), aj

    def zjet_point_q(self, m, qi, D):
        """Taylor coefficients (degree <= D) of Z_m (= zeta_m for m >= 1, A_0 for m = 0) at the quarter-grid point t_qi."""
        return self._jet(m, self.g * qi, D, self.A[m][qi])[0]

    def zjet_point(self, m, l, D):
        return self.zjet_point_q(m, 2 * l, D)

    def zjet_ball(self, m, qc, r, D):
        """Enclosures over [t_qc - r, t_qc + r] of the Taylor coefficients (degree <= D) of Z_m.
        Crude ball evaluation to degree D+1, then refined downwards by the mean value theorem
        z_k(x) in z_k(t_qc) + (k+1) z_{k+1}(ball) * [-r, r]   (d/dx of the k-th Taylor coefficient is (k+1) z_{k+1})."""
        xc = self.g * qc
        rr = float(arb(r).abs_upper()) * 1.0000001
        X = xc + arb(0, rr)
        aj0 = a_jet(self.n, m, X, 0)[0]
        A0 = self.A[m][qc] + aj0 * arb(0, rr)                 # A(x) = A(xc) - a(xi)(x - xc)
        crude, _ = self._jet(m, X, D + 1, A0)
        pt = self.zjet_point_q(m, qc, D)
        out = [None] * (D + 1)
        nxt = crude[D + 1]
        for k in range(D, -1, -1):
            ref = pt[k] + nxt * (k + 1) * arb(0, rr)
            lo = max(float(ref.lower()), float(crude[k].lower())); hi = min(float(ref.upper()), float(crude[k].upper()))
            # intersection of the two enclosures (both valid); keep ref if the float intersection is degenerate
            out[k] = ref if not (lo <= hi) else ref.intersection(crude[k]) if hasattr(ref, "intersection") else ref
            nxt = out[k]
        return out


# ---------------------------------------------------------------------------------------------------------------
# two-variable truncated jets: dict {(i,j): arb}, total degree <= D
# ---------------------------------------------------------------------------------------------------------------
class J2:
    __slots__ = ("c", "D")
    def __init__(self, D, c=None):
        self.D = D; self.c = c if c is not None else {}
    @staticmethod
    def const(D, v):
        return J2(D, {(0, 0): v})
    def get(self, i, j):
        return self.c.get((i, j), arb(0))
    def __add__(self, o):
        r = dict(self.c)
        for k, v in o.c.items():
            r[k] = r[k] + v if k in r else v
        return J2(self.D, r)
    def __sub__(self, o):
        r = dict(self.c)
        for k, v in o.c.items():
            r[k] = r[k] - v if k in r else -v
        return J2(self.D, r)
    def scale(self, a):
        return J2(self.D, {k: v * a for k, v in self.c.items()})
    def __mul__(self, o):
        D = self.D; r = {}
        for (i1, j1), v1 in self.c.items():
            for (i2, j2), v2 in o.c.items():
                if i1 + j1 + i2 + j2 <= D:
                    k = (i1 + i2, j1 + j2)
                    t = v1 * v2
                    r[k] = r[k] + t if k in r else t
        return J2(D, r)
    def _nilpotent_series(self, f0, coef_fn):
        """f = f0*(1+g), g without constant term; return f0-dependent sum_k coef_fn(k) g^k."""
        D = self.D
        g = J2(D, {k: v / f0 for k, v in self.c.items() if k != (0, 0)})
        acc = J2.const(D, coef_fn(0)); pw = J2.const(D, arb(1))
        for k in range(1, D + 1):
            pw = pw * g
            acc = acc + pw.scale(coef_fn(k))
        return acc
    def sqrt(self):
        f0 = self.get(0, 0)
        def binom_half(k):
            r = arb(1)
            for t in range(k):
                r = r * (arb(0.5) - t) / (t + 1)
            return r
        return self._nilpotent_series(f0, binom_half).scale(f0.sqrt())
    def inv(self):
        f0 = self.get(0, 0)
        return self._nilpotent_series(f0, lambda k: arb(-1) ** k).scale(1 / f0)


def lift(z, D, kind, sgn=1):
    """2-variable jet from the 1-variable Taylor coefficients z of a function of one linear form.
    kind 'x': function of the first variable;  'y': of the second;  'mid': of (x+y)/2;
    kind 'ab_p': of (x - y) [alpha - b];  'ab_q': of (x + y)."""
    r = {}
    if kind == "x":
        for i in range(D + 1): r[(i, 0)] = z[i]
    elif kind == "y":
        for j in range(D + 1): r[(0, j)] = z[j]
    else:
        for i in range(D + 1):
            for j in range(D + 1 - i):
                c = z[i + j] * math.comb(i + j, i)
                if kind == "mid": c = c / (2 ** (i + j))
                elif kind == "ab_p" and j % 2 == 1: c = -c
                r[(i, j)] = c
    return J2(D, r)


def e_jets(n, D, Zp, Zq, Za, Ea):
    """Jets of e_0..e_{n-2}.  Zp[m], Zq[m], Za[m]: J2 jets of Z_m at p, q, alpha;  Ea[m]: jet of e^{-m alpha}."""
    one = J2.const(D, arb(1))
    delta = [None] * (n + 1)
    delta[0] = Zp[0].scale(arb(0.5)) + Zq[0].scale(arb(0.5)) - Za[0]          # = 2 delta_0
    for m in range(1, n - 1):
        zp, zq, za = Zp[m], Zq[m], Za[m]
        T1 = (zp + zq).scale(arb(0.5)) - za
        dz = zp - zq
        den = (one - zp).sqrt() + (one - zq).sqrt()
        T2 = (dz * dz * (den * den).inv()).scale(arb(0.5))
        delta[m] = ((T1 + T2) * Ea[m]).scale(arb(1) / m)
    zero = J2(D, {})
    delta[n - 1] = zero; delta[n] = zero
    return [delta[j] - delta[j + 1].scale(arb(2)) + delta[j + 2] for j in range(n - 1)]


def exp_lin_jet(m, X, D):
    """Taylor coefficients of exp(-m x) at ball X."""
    return coeffs((ser(X, D) * (-m)).exp(), D)


def strip_jets(n, D, zB, zP, zQ, eA, point):
    """Jets (in d alpha, d b) of  Phi_j = e_j / b^2,  j = 0..n-2.
    zB[m]: 1-variable Taylor coefficients (degree <= D+2) of Z_m, at the point alpha (point=True) or enclosures over the
           ball B = hull of all p, q, alpha in the strip box (point=False);
    zP, zQ: same at the p-ball and q-ball (degree <= D), used only for den = sqrt(1-zeta_p)+sqrt(1-zeta_q);
    eA[m]: Taylor coefficients of e^{-m alpha}.
    Etilde = [(Z(alpha-b)+Z(alpha+b))/2 - Z(alpha)]/b^2,   Dtilde = [Z(alpha-b) - Z(alpha+b)]/b."""
    def Et(z):
        r = {}
        for i in range(D + 1):
            for j in range(D + 1 - i):
                c = z[i + j + 2] * math.comb(i + j + 2, i)
                if j % 2 == 1:
                    if point: continue
                    c = arb(0, float(c.abs_upper()) * 1.0000001)
                r[(i, j)] = c
        return J2(D, r)
    def Dt(z):
        r = {}
        for i in range(D + 1):
            for j in range(D + 1 - i):
                c = z[i + j + 1] * (-2 * math.comb(i + j + 1, i))
                if j % 2 == 1:
                    if point: continue
                    c = arb(0, float(c.abs_upper()) * 1.0000001)
                r[(i, j)] = c
        return J2(D, r)
    one = J2.const(D, arb(1))
    delta = [None] * (n + 1)
    delta[0] = Et(zB[0])
    for m in range(1, n - 1):
        den = (one - lift(zP[m], D, "ab_p")).sqrt() + (one - lift(zQ[m], D, "ab_q")).sqrt()
        dt = Dt(zB[m])
        T = Et(zB[m]) + (dt * dt * (den * den).inv()).scale(arb(0.5))
        delta[m] = (T * lift(eA[m], D, "x")).scale(arb(1) / m)
    zero = J2(D, {})
    delta[n - 1] = zero; delta[n] = zero
    return [delta[j] - delta[j + 1].scale(arb(2)) + delta[j + 2] for j in range(n - 1)]
