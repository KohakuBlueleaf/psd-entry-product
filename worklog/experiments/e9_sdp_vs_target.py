"""E9. Is the harmonic SDP dual bound (see e6) always >= the theorem's bound -sum_i log F_n(d_i)?
If yes, the theorem is equivalent to a linear statement about 'relaxed' families (Y_m), and a harmonic
certificate proof exists in principle.  If no for some diagonal, harmonic certificates cannot prove the theorem.
Random and near-equal diagonals, n = 4..7.  margin = SDP bound - target  (need >= 0).
"""
import numpy as np, sys
from multiprocessing import Pool
from e6_sdp_certificate import sdp_bound

def job(args):
    tag, d = args
    d = np.array(d); n = len(d)
    val, _, _ = sdp_bound(d, D=3 * n, grid=720)
    target = -np.sum(np.log(sum(d ** k for k in range(n))))
    return tag, n, val - target, d

if __name__ == "__main__":
    rng = np.random.default_rng(2)
    jobs = []
    for n in (4, 5, 6, 7):
        for k in range(5):
            jobs.append(("rand<1", rng.uniform(.05, 1, n)))
            jobs.append(("rand across", rng.uniform(.1, 4, n)))
            base = rng.choice([.5, .9, 1.0, 1.5])
            jobs.append(("near-equal 1e-1", base * (1 + .1 * rng.normal(size=n))))
            jobs.append(("near-equal 1e-2", base * (1 + .01 * rng.normal(size=n))))
            jobs.append(("two-level", np.where(rng.random(n) < .5, .3, 1.2)))
            jobs.append(("one-big", np.concatenate([[rng.uniform(2, 6)], rng.uniform(.05, .5, n - 1)])))
    with Pool(60) as pool: out = pool.map(job, jobs)
    agg = {}
    for tag, n, m, d in out:
        key = (n, tag); cur = agg.get(key)
        if cur is None or m < cur[0]: agg[key] = (m, d)
    for key in sorted(agg):
        m, d = agg[key]
        print(f"n={key[0]} {key[1]:16s}: min margin = {m:+.3e}   at d={np.round(d, 3)}")
