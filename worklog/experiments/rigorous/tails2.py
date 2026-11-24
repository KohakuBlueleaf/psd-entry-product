"""Unbounded parts of the domain {0 <= p <= q}.  See notes/rigorous-B.md, sections 6 and 7.

Chart S' :  p >= P1  (s = e^{-p} in (0, s0]),  q = p + 2b,  b in [0, oo).
Chart R' :  0 <= p <= P1,  q >= QC.

usage: tails.py n P1 QC B hb_den KD h_den
"""
import sys, json, os
from flint import arb, arb_series, ctx
import rig
from rig import Table, coeffs

ctx.prec = rig.PREC


# ------------------------------------------------------------------------------------------------ series in X = e^{-x}
def monomials(n, m, J):
    """zeta_m(x) (m>=1) or A_0(x) (m=0) = sum_e coef * X^e, X = e^{-x}; list of (coef (arb), e) for j <= J."""
    N = n - m; out = []
    if m == 0:
        for j in range(1, J + 1):
            out.append((arb(n * j) / (j * n - 1), j * n - 1))
            out.append((-arb(n * j) / (j * n + 1), j * n + 1))
            out.append((-arb(2) / (j * n), j * n))
        return out
    for j in range(1, J + 1):
        out.append((arb(m * N * j) / (j * n - 1), j * n - 1 - m))
        out.append((-arb(m * N * j) / (j * n + 1), j * n + 1 - m))
        out.append((-arb(m * (j + 1)) / (j * n + m), j * n))
        if j >= 2:
            out.append((arb(m * (j - 1)) / (j * n - m), j * n - 2 * m))
    return out

def tail_radius(n, m, J, s0, K):
    """Bound for |Taylor coefficient of order <= K (in beta >= 0)| of the normalised tail (terms j > J) of H_m.
    Each tail monomial has |coef| <= n^2 j, normalised exponent >= (j-1)n - m and exponent e <= jn + 2, e^{-e beta} <= 1,
    and |(-e)^k/k!| <= (jn+2)^K.  The sum over j > J is at most twice its first term because the ratio of consecutive
    terms is at most 2 * 2^K * s0^n < 1/2 (checked below)."""
    assert float((arb(2) ** (K + 1) * s0 ** n).abs_upper()) < 0.5
    j = J + 1
    first = arb(n * n * j) * arb(j * n + 2) ** K * s0 ** ((j - 1) * n - m) * 4      # 4 monomials per j
    return float((2 * first).abs_upper()) * 1.0001

def H_series(n, m, S, Bball, D, J=4, positive_only=False):
    """Taylor coefficients (degree <= D) in beta, at the ball Bball, of
       H_m(beta) = Z_m(p + beta) / s^{c},   c = N-1 (m>=1) or n-1 (m=0),   s in the ball S = [0, s0]."""
    N = n - m; c = (N - 1) if m >= 1 else (n - 1)
    b = arb_series([Bball, arb(1)], prec=D + 1)
    acc = arb_series([arb(0)], prec=D + 1)
    for coef, e in monomials(n, m, J):
        if positive_only and not (coef > 0): continue
        acc = acc + (b * (-e)).exp() * (coef * S ** (e - c))
    cs = coeffs(acc, D)
    rad = tail_radius(n, m, J, arb(float(S.abs_upper())), D)
    return [x + arb(0, rad) for x in cs]


def exp_series(c, Bball, D):
    return (arb_series([Bball, arb(1)], prec=D + 1) * c).exp()

def scale_series(cs, k, D):
    """Taylor coefficients of f(k*b) from those of f."""
    return arb_series([cs[i] * (k ** i) for i in range(D + 1)], prec=D + 1)

def e_series_regular(n, S, bc_ball, D):
    """arb_series (in db, at the ball bc_ball) of e_j / s^{n-1}, j = 0..n-2."""
    one = arb_series([arb(1)], prec=D + 1)
    delta = [None] * (n + 1)
    zero_ball = arb(0)
    for m in range(0, n - 1):
        N = n - m
        h0 = H_series(n, m, S, zero_ball, 0)[0]                                   # H_m(0) (interval in s)
        H1 = arb_series(H_series(n, m, S, bc_ball, D), prec=D + 1)                # H_m(b)
        H2 = scale_series(H_series(n, m, S, bc_ball * 2, D), 2, D)                # H_m(2b)
        if m == 0:
            delta[0] = H2 * arb(0.5) - H1 + h0 * arb(0.5)                          # = 2 F_0
            continue
        sN = S ** (N - 1)
        den = arb_series([(1 - sN * h0).sqrt()], prec=D + 1) + (one - H2 * sN).sqrt()
        dz = H2 * (-1) + h0
        T = H2 * arb(0.5) - H1 + h0 * arb(0.5) + (dz * dz / (den * den)) * (sN * arb(0.5))
        delta[m] = T * exp_series(-m, bc_ball, D) * (arb(1) / m)
    z = arb_series([arb(0)], prec=D + 1)
    delta[n - 1] = z; delta[n] = z
    return [delta[j] - delta[j + 1] * 2 + delta[j + 2] for j in range(n - 1)]

def e_series_strip(n, S, bs, D, point):
    """arb_series (in b, expansion at b = 0 if point, else enclosures valid at every b in [0, bs]) of
       Phi_j = e_j / (s^{n-1} b^2)."""
    one = arb_series([arb(1)], prec=D + 1)
    B1 = arb(0) if point else bs / 2 + arb(0, float((bs / 2).abs_upper()) * 1.0000001)       # beta in [0, bs]
    B2 = arb(0) if point else bs + arb(0, float(bs.abs_upper()) * 1.0000001)                 # beta in [0, 2 bs]
    delta = [None] * (n + 1)
    for m in range(0, n - 1):
        N = n - m
        h1 = H_series(n, m, S, B1, D + 2)
        h2 = H_series(n, m, S, B2, D + 2)
        # phi/b^2 = [H(0)/2 + H(2b)/2 - H(b)]/b^2 : coefficient i is 2^{i+1} h_{i+2}(2b-ball) - h_{i+2}(b-ball)
        E = arb_series([h2[i + 2] * (2 ** (i + 1)) - h1[i + 2] for i in range(D + 1)], prec=D + 1)
        if m == 0:
            delta[0] = E
            continue
        h0 = H_series(n, m, S, arb(0), 0)[0]
        sN = S ** (N - 1)
        Dt = arb_series([h2[i + 1] * (-(2 ** (i + 1))) for i in range(D + 1)], prec=D + 1)   # (H(0)-H(2b))/b
        H2 = scale_series(h2, 2, D)
        den = arb_series([(1 - sN * h0).sqrt()], prec=D + 1) + (one - H2 * sN).sqrt()
        T = E + (Dt * Dt / (den * den)) * (sN * arb(0.5))
        bb = arb(0) if point else B1
        delta[m] = T * exp_series(-m, bb, D) * (arb(1) / m)
    z = arb_series([arb(0)], prec=D + 1)
    delta[n - 1] = z; delta[n] = z
    return [delta[j] - delta[j + 1] * 2 + delta[j + 2] for j in range(n - 1)]


def decide(los):
    L = [x.lower() for x in los]
    for j in range(1, len(L)):
        if not (L[j] >= 0): return -1.0
    if L[0] >= 0:
        return 1.0
    pairs = arb(0)
    for j in range(1, len(L) - 1, 2):
        pairs += (L[j] + L[j + 1] - abs(L[j] - L[j + 1])) / 2          # min(a,b), rigorous for balls
    margin = pairs + 2 * L[0]
    if not (margin > 0): return -1.0
    return float((margin / pairs).mid())

def chart_S(n, P1, B, hb_den, KD, d=3, DS=4):
    s0 = (-arb(P1)).exp()
    S = s0 / 2 + arb(0, float((s0 / 2).abs_upper()) * 1.0000001)          # s in [0, s0]
    hb = arb(1) / hb_den
    res = dict(min_ratio_strip=None, min_ratio_regular=None, failed=0, min_ratio_far=None)
    # strip 0 <= b <= bs
    bs = hb * KD
    pt = e_series_strip(n, S, bs, DS - 1, True)
    bx = e_series_strip(n, S, bs, DS, False)
    los = []
    for j in range(n - 1):
        cp = coeffs(pt[j], DS - 1); cb = coeffs(bx[j], DS)
        lo = cp[0]
        for k in range(1, DS): lo = lo - cp[k].abs_upper() * bs ** k
        lo = lo - cb[DS].abs_upper() * bs ** DS
        los.append(lo)
    r = decide(los)
    if not (r > 0): res["failed"] += 1
    res["min_ratio_strip"] = r
    # regular cells [b_i, b_i + hb], i = KD .. B*hb_den - 1
    worst = None
    for i in range(KD, B * hb_den):
        bc = hb * i + hb / 2
        cell = bc + arb(0, float((hb / 2).abs_upper()) * 1.0000001)
        pt = e_series_regular(n, S, bc, d - 1)
        bx = e_series_regular(n, S, cell, d)
        los = []
        for j in range(n - 1):
            cp = coeffs(pt[j], d - 1); cb = coeffs(bx[j], d)
            lo = cp[0]
            for k in range(1, d): lo = lo - cp[k].abs_upper() * (hb / 2) ** k
            lo = lo - cb[d].abs_upper() * (hb / 2) ** d
            los.append(lo)
        r = decide(los)
        if not (r > 0): res["failed"] += 1
        worst = r if worst is None else min(worst, r)
    res["min_ratio_regular"] = worst
    # far part b >= B: dominance
    Bb = arb(B)
    G_low = [None] * (n + 1); G_up = [None] * (n + 1)
    for m in range(1, n - 1):
        N = n - m; sN = S ** (N - 1)
        h0 = H_series(n, m, S, arb(0), 0)[0]
        supB = H_series(n, m, S, Bb, 0, positive_only=True)[0]           # H(beta) <= H^+(B) for beta >= B
        sup2B = H_series(n, m, S, Bb * 2, 0, positive_only=True)[0]
        den_low = (1 - sN * h0).sqrt() + (1 - sN * sup2B).sqrt()
        hmax = max(float(h0.abs_upper()), float(sup2B.abs_upper())) * 1.0000001
        T2_up = sN * arb(hmax) ** 2 / (2 * den_low * den_low)
        G_low[m] = h0 / 2 - supB.abs_upper()
        G_up[m] = h0 / 2 + sup2B.abs_upper() / 2 + T2_up
    G_low[n - 1] = arb(0); G_up[n - 1] = arb(0); G_up[n] = arb(0)
    worst = None
    eB = (-Bb).exp()
    for j in range(1, n - 1):
        lo = G_low[j] / j - 2 * eB * (G_up[j + 1].abs_upper() / (j + 1) if j + 1 <= n - 2 else 0)
        if not (lo > 0) or not (G_low[j] > 0): res["failed"] += 1
        r = float((lo / (G_low[j] / j)).lower()) if G_low[j] > 0 else -1.0
        worst = r if worst is None else min(worst, r)
    h00 = H_series(n, 0, S, arb(0), 0)[0]
    sup0 = H_series(n, 0, S, Bb, 0, positive_only=True)[0]
    lo0 = h00 / 2 - sup0.abs_upper() - 2 * eB * G_up[1].abs_upper()
    if not (lo0 > 0): res["failed"] += 1
    worst = min(worst, float((lo0 / (h00 / 2)).lower()))
    res["min_ratio_far"] = worst
    return res


def zeta_plus(n, m, x0):
    """Upper bound for sup_{x >= x0} Z_m(x): the positive monomials only (decreasing in x), with tail."""
    s = (-arb(x0)).exp() if not isinstance(x0, arb) else (-x0).exp()
    tot = arb(0)
    for coef, e in monomials(n, m, 6):
        if coef > 0: tot += coef * s ** e
    j = 7
    tail = 2 * arb(n * n * j) * 4 * s ** ((j - 2) * n)                 # |coef| <= n^2 j, exponent >= jn - 2m >= (j-2)n, ratio <= 2 s^n
    assert float((2 * s ** n).abs_upper()) < 0.5
    return tot + tail

def chart_R(n, P1, QC, h_den):
    """0 <= p <= P1, q >= QC.  Uses the table of zeta_m and A_0 on [0, P1]."""
    T = Table(n, 1, h_den, P1, 1, extra=4)
    h = T.h
    v0 = (-arb(QC) / 2).exp()
    res = dict(failed=0, min_ratio=None)
    worst = None
    ncell = P1 * h_den
    for i in range(ncell):
        plo = h * i
        Z = [T.zjet_ball(m, 4 * i + 2, h / 2, 0)[0] for m in range(n - 1)]        # cell [t_{4i}, t_{4i+4}]
        xa = (plo + QC) / 2                                                       # alpha >= xa
        tau_low = [None] * (n + 1); tau_up = [None] * (n + 1)
        for m in range(1, n - 1):
            za_up = zeta_plus(n, m, xa).abs_upper()
            zq_up = zeta_plus(n, m, arb(QC)).abs_upper()
            tau_low[m] = 1 - za_up - (1 - Z[m]).sqrt()
            tau_up[m] = 1 - ((1 - Z[m]) * (1 - zq_up)).sqrt()
        tau_up[n - 1] = arb(0); tau_low[n - 1] = arb(0)
        ep = (-plo / 2).exp()                                                     # e^{-p/2} <= e^{-plo/2}
        for j in range(1, n - 1):
            if not (tau_low[j] > 0): res["failed"] += 1; continue
            lo = tau_low[j] / j - 2 * v0 * ep * (tau_up[j + 1].abs_upper() / (j + 1))
            if not (lo > 0): res["failed"] += 1
            r = float((lo / (tau_low[j] / j)).lower())
            worst = r if worst is None else min(worst, r)
        # j = 0:  e_0 >= A_0(p)/2 - A_0(alpha) - 2 delta_1,  delta_1 <= v0 e^{-p/2} tau_1^up,  A_0 decreasing
        A0p = Z[0]
        A0a_up = zeta_plus(n, 0, xa).abs_upper()
        lo0 = A0p / 2 - A0a_up - 2 * v0 * ep * tau_up[1].abs_upper()
        if not (lo0 > 0): res["failed"] += 1
        r = float((lo0 / (A0p / 2)).lower())
        worst = r if worst is None else min(worst, r)
    res["min_ratio"] = worst
    return res


if __name__ == "__main__":
    n = int(sys.argv[1]); P1 = int(sys.argv[2]); QC = int(sys.argv[3]); B = int(sys.argv[4])
    hb_den = int(sys.argv[5]); KD = int(sys.argv[6]); h_den = int(sys.argv[7])
    rs = chart_S(n, P1, B, hb_den, KD)
    rr = chart_R(n, P1, QC, h_den)
    out = dict(n=n, P1=P1, QC=QC, B=B, hb=f"1/{hb_den}", KD=KD, chart_S=rs, chart_R=rr)
    print(json.dumps(out))
    os.makedirs("logs", exist_ok=True)
    with open(f"logs/B_tails_n{n}_P{P1}_Q{QC}_B{B}.json", "w") as f:
        json.dump(out, f)
