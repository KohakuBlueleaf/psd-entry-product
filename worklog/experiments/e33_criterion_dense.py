"""E33. Dense (floating, high precision) scan of criterion v2 on W, including the edges p = alpha - b -> 0, b -> 0, alpha small/large.
Coefficients via the integral representation (robust at p = 0).  Reports, per n, the worst ratio and where it occurs."""
import mpmath as mp
from multiprocessing import Pool
import e20_closed_form as e
from e31_criterion_v2 import criterion

def delta_seq(n, al, b):
    p, q = al - b, al + b
    d = [2 * (e.Gam(n, 0, al) - (e.Gam(n, 0, p) + e.Gam(n, 0, q)) / 2)]
    for m in range(1, n - 1):
        d.append(e.Gam(n, m, al) - mp.sqrt(e.Gam(n, m, p) * e.Gam(n, m, q)))
    return d

def job(args):
    n, al, fr = args; mp.mp.dps = 50 + 4 * n
    al = mp.mpf(al); b = al * mp.mpf(fr)
    try:
        r, nneg = criterion(delta_seq(n, al, b))
    except Exception as ex:
        return n, float(al), fr, None, str(ex)[:60]
    return n, float(al), fr, r, nneg

if __name__ == "__main__":
    als = ['0.01', '0.03', '0.08', '0.15', '0.25', '0.4', '0.6', '0.8', '1.1', '1.5', '2.2', '3.5', '6']
    frs = ['0.001', '0.2', '0.5', '0.8', '0.95', '1']
    ns = (5, 8, 12, 16, 20, 25, 32, 40)
    jobs = [(n, a, f) for n in ns for a in als for f in frs]
    with Pool(30) as pool: out = pool.map(job, jobs, chunksize=1)
    for n in ns:
        rows = [o for o in out if o[0] == n]
        bad = [o for o in rows if o[3] is None]
        ok = [o for o in rows if o[3] is not None]
        w = min(ok, key=lambda o: o[3])
        fails = [(o[1], o[2], mp.nstr(o[3], 3)) for o in ok if o[3] < 1]
        print(f"n={n}: worst ratio = {'inf' if w[3] == mp.inf else mp.nstr(w[3], 4)} at (alpha, b/alpha)=({w[1]},{w[2]});  cases with ratio<1: {fails[:6]};  errors: {len(bad)}", flush=True)
