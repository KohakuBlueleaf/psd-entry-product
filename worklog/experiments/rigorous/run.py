"""Driver.  usage: run.py n Q h_den KD [d] [nproc]     (h = 1/h_den)
Verifies e_j > 0 (regular boxes) and e_j/b^2 > 0 (strip along the diagonal) on  {0 <= p <= q <= Q}.
"""
import sys, time, os, json
from multiprocessing import Pool
from flint import arb, ctx
import rig
from rig import Table, J2, lift, e_jets, exp_lin_jet

n = int(sys.argv[1]); Q = int(sys.argv[2]); h_den = int(sys.argv[3]); KD = int(sys.argv[4])
d = int(sys.argv[5]) if len(sys.argv) > 5 else 3
nproc = int(sys.argv[6]) if len(sys.argv) > 6 else 32
ctx.prec = rig.PREC

T = None; PJ = None; CJ = None; EP = None; EC = None; HJ = None

DS = 4          # Taylor order of the strip model

def hull(a, b_):
    mid = (a + b_) / 2
    return mid + arb(0, float(((b_ - a) / 2).abs_upper()) * 1.0000001)

def build():
    """Per half-index l: point jets (degree d-1) at the centre of the cell [y_l, y_l + h], cell jets (degree d)."""
    global T, PJ, CJ, EP, EC, HJ
    T = Table(n, 1, h_den, Q, d, extra=KD + 8)
    h = T.h
    Lmax = T.L
    PJ = [None] * Lmax; CJ = [None] * Lmax; EP = [None] * Lmax; EC = [None] * Lmax
    for l in range(Lmax):
        centre = T.y(l + 1)                                  # y_l + h/2 = y_{l+1} = t_{2l+2}
        ball = centre + arb(0, float((h / 2).abs_upper()) * 1.0000001)
        PJ[l] = [T.zjet_point(m, l + 1, d - 1) for m in range(n - 1)]
        CJ[l] = [T.zjet_ball(m, 2 * l + 2, h / 2, d) for m in range(n - 1)]
        EP[l] = [exp_lin_jet(m, centre, d - 1) for m in range(n - 1)]
        EC[l] = [exp_lin_jet(m, ball, d) for m in range(n - 1)]
    # jets (degree DS+2) over each half cell [y_k, y_{k+1}], used (as unions) for the strip boxes
    HJ = [None] * (Lmax + KD + 3)
    for k in range(Lmax + KD + 3):
        HJ[k] = [T.zjet_ball(m, 2 * k + 1, h / 4, DS + 2) for m in range(n - 1)]

def union_jets(k0, k1, m, D):
    """Enclosure over [y_k0, y_k1] of the Taylor coefficients (degree <= D) of Z_m: union over the half cells."""
    out = list(HJ[k0][m][:D + 1])
    for k in range(k0 + 1, k1):
        out = [a.union(b_) for a, b_ in zip(out, HJ[k][m][:D + 1])]
    return out

def lower_bound_regular(i, k):
    """Lower bounds of e_j over the box p in [x_i, x_i+h], q in [x_k, x_k+h]; returns min_j (bound / |centre value|)."""
    lp, lq, la = 2 * i, 2 * k, i + k
    hh = T.h / 2
    D = d - 1
    ep = e_jets(n, D, [lift(PJ[lp][m], D, "x") for m in range(n - 1)], [lift(PJ[lq][m], D, "y") for m in range(n - 1)],
                [lift(PJ[la][m], D, "mid") for m in range(n - 1)], [lift(EP[la][m], D, "mid") for m in range(n - 1)])
    eb = e_jets(n, d, [lift(CJ[lp][m], d, "x") for m in range(n - 1)], [lift(CJ[lq][m], d, "y") for m in range(n - 1)],
                [lift(CJ[la][m], d, "mid") for m in range(n - 1)], [lift(EC[la][m], d, "mid") for m in range(n - 1)])
    worst = None
    for j in range(n - 1):
        c0 = ep[j].get(0, 0)
        lo = c0
        for (a, b_), v in ep[j].c.items():
            if a + b_ >= 1:
                lo = lo - v.abs_upper() * hh ** (a + b_)
        for (a, b_), v in eb[j].c.items():
            if a + b_ == d:
                lo = lo - v.abs_upper() * hh ** d
        if not (c0 > 0) or not (lo > 0):          # rigorous decision: ball comparison
            return -1.0
        r = float((lo / c0).mid()) - float((lo / c0).rad())
        if worst is None or r < worst: worst = r
    return worst

def row(i):
    Ncell = Q * h_den
    worst = None; bad = []
    for k in range(i + KD, Ncell):
        r = lower_bound_regular(i, k)
        if not (r > 0): bad.append((i, k, r))
        if worst is None or r < worst: worst = r
    return i, worst, bad

def strip(l):
    """alpha in [y_l, y_{l+1}], 0 <= b <= b_s = KD*h/2 (and p = alpha - b >= 0).
    Lower bound of Phi_j = e_j/b^2 by a Taylor model of order DS around (y_l, 0); returns min_j bound/centre value."""
    h = T.h; bs = h * KD / 2
    y0 = T.y(l); y1 = T.y(l + 1)
    D = DS - 1
    zc = [T.zjet_point(m, l, D + 2) for m in range(n - 1)]
    ec = [exp_lin_jet(m, y0, D) for m in range(n - 1)]
    pj = rig.strip_jets(n, D, zc, zc, zc, ec, True)
    Ab = hull(y0, y1)
    kp = max(l - KD, 0)                                # p in [y_kp, y_{l+1}], q in [y_l, y_{l+1+KD}]
    zB = [union_jets(kp, l + 1 + KD, m, DS + 2) for m in range(n - 1)]
    zP = [union_jets(kp, l + 1, m, DS) for m in range(n - 1)]
    zQ = [union_jets(l, l + 1 + KD, m, DS) for m in range(n - 1)]
    eA = [exp_lin_jet(m, Ab, DS) for m in range(n - 1)]
    bj = rig.strip_jets(n, DS, zB, zP, zQ, eA, False)
    ra = h / 2; rb = bs
    worst = None
    for j in range(n - 1):
        c0 = pj[j].get(0, 0)
        lo = c0
        for (a, b_), v in pj[j].c.items():
            if a + b_ >= 1:
                lo = lo - v.abs_upper() * ra ** a * rb ** b_
        for (a, b_), v in bj[j].c.items():
            if a + b_ == DS:
                lo = lo - v.abs_upper() * ra ** a * rb ** b_
        if not (c0 > 0) or not (lo > 0):          # rigorous decision: ball comparison
            return l, -1.0
        r = float((lo / c0).mid()) - float((lo / c0).rad())
        if worst is None or r < worst: worst = r
    return l, worst

if __name__ == "__main__":
    t0 = time.time()
    build()
    t1 = time.time()
    Ncell = Q * h_den
    with Pool(nproc) as pool:
        rows = pool.map(row, range(0, Ncell - KD), chunksize=4)
        strips = pool.map(strip, range(0, T.L), chunksize=8)
    t2 = time.time()
    bad = [b for _, _, bl in rows for b in bl]
    wr = min((w for _, w, _ in rows if w is not None), default=None)
    ws = min(w for _, w in strips)
    bad_s = [l for l, w in strips if not (w > 0)]
    nbox = sum(max(0, Ncell - i - KD) for i in range(Ncell - KD))
    res = dict(n=n, Q=Q, h=f"1/{h_den}", KD=KD, order=d, regular_boxes=nbox, regular_failed=len(bad), min_ratio_regular=wr,
               strips=T.L, strips_failed=len(bad_s), min_ratio_strip=ws, table_sec=round(t1 - t0, 1), verify_sec=round(t2 - t1, 1),
               bad_regular=bad[:20], bad_strips=bad_s[:20],
               fail_qmax=max([(k + 1) / h_den for _, k, _ in bad] + [(l + 1 + KD) / (2 * h_den) for l in bad_s] + [0.0]))
    print(json.dumps(res))
    os.makedirs("logs", exist_ok=True)
    with open(f"logs/n{n}_Q{Q}_h{h_den}_KD{KD}_d{d}.json", "w") as f:
        json.dump(res, f)
