"""E3. For a fixed diagonal d, maximise  f(A) = sum_{i!=j} log|1-a_ij|  over PSD A with diag(A)=d.
Report: best value over all ranks, best value over rank one, the bound sum_i log F_n(d_i),
and the numerical rank (eigenvalues) of the best maximiser found.
"""
import numpy as np
from scipy.optimize import minimize
from multiprocessing import Pool

def gram(p, d, r):
    n = len(d)
    V = (p[:n * r] + 1j * p[n * r:]).reshape(n, r)
    V = V / np.linalg.norm(V, axis=1, keepdims=True) * np.sqrt(d)[:, None]
    return V @ V.conj().T

def negf(p, d, r):
    A = gram(p, d, r)
    n = len(d)
    off = ~np.eye(n, dtype=bool)
    return -np.sum(np.log(np.abs(1 - A[off]) + 1e-300))

def best(d, r, seed, tries=40):
    rng = np.random.default_rng(seed)
    n = len(d); bv = np.inf; bp = None
    for _ in range(tries):
        res = minimize(negf, rng.normal(size=2 * n * r), args=(d, r), method="BFGS",
                       options={"gtol": 1e-10, "maxiter": 5000})
        if res.fun < bv: bv, bp = res.fun, res.x
    return -bv, gram(bp, d, r)

def job(args):
    name, d = args
    d = np.array(d, float); n = len(d)
    vfull, Afull = best(d, n, 0)
    v1, _ = best(d, 1, 1)
    bound = np.sum(np.log(sum(d ** k for k in range(n))))
    ev = np.linalg.eigvalsh(Afull)[::-1]
    return name, d, vfull, v1, bound, ev / ev[0]

if __name__ == "__main__":
    rng = np.random.default_rng(7)
    cases = [("n3 equal .5", [.5] * 3), ("n3 unit", [1] * 3), ("n3 equal 2", [2] * 3),
             ("n3 mixed", [.3, .6, .9]), ("n3 mixed across 1", [.5, 1.0, 2.0]),
             ("n4 unit", [1] * 4), ("n4 equal .7", [.7] * 4), ("n4 mixed", [.2, .5, .8, .95]),
             ("n4 mixed across 1", [.3, .9, 1.5, 3.0]), ("n5 unit", [1] * 5),
             ("n5 mixed", [.1, .4, .6, .8, .99]), ("n5 mixed across 1", [.2, .7, 1.0, 1.6, 4.0]),
             ("n6 unit", [1] * 6), ("n6 mixed", list(rng.uniform(.1, 1, 6))),
             ("n6 mixed across 1", list(rng.uniform(.2, 3, 6))),
             ("n7 mixed across 1", list(rng.uniform(.2, 3, 7)))]
    with Pool(len(cases)) as pool:
        for name, d, vf, v1, b, ev in pool.map(job, cases):
            print(f"{name:20s} max(all ranks)={vf:.8f}  max(rank1)={v1:.8f}  bound={b:.8f}  "
                  f"slack={b - vf:.2e}  eig ratios={np.array2string(ev[:4], precision=2, suppress_small=True)}")
