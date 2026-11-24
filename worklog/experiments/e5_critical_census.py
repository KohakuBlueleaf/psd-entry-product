"""E5. Census of critical points of  f(A) = sum_{i!=j} log|1-a_ij|  on {A PSD, diag A = d}.

Part 1 (local maxima): many random full-rank starts, BFGS ascent; report the distinct limit values and the
        numerical rank of each limit.  R1 predicts: every local max we care about (the global one) is rank one;
        we also learn whether higher-rank local maxima exist at all.
Part 2 (all critical points): solve grad f = 0 by least squares from random starts; for each critical point of
        rank >= 2 report the largest Hessian eigenvalue (positive => not a local maximum).
"""
import numpy as np, torch, sys
from scipy.optimize import minimize, least_squares
from multiprocessing import Pool
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)

def f_torch(p, d, r):
    n = len(d)
    V = torch.complex(p[:n * r], p[n * r:]).reshape(n, r)
    V = V / torch.linalg.norm(V, dim=1, keepdim=True) * torch.sqrt(d)[:, None]
    A = V @ V.conj().T
    off = ~torch.eye(n, dtype=torch.bool)
    return torch.log(torch.abs(1 - A[off])).sum(), A

def make(d, r):
    dt = torch.tensor(d)
    def val(p):  return f_torch(torch.tensor(p), dt, r)[0].item()
    def grad(p):
        x = torch.tensor(p, requires_grad=True); y = f_torch(x, dt, r)[0]; y.backward(); return x.grad.numpy()
    def hess(p): return torch.autograd.functional.hessian(lambda x: f_torch(x, dt, r)[0], torch.tensor(p)).numpy()
    def gram(p): return f_torch(torch.tensor(p), dt, r)[1].numpy()
    return val, grad, hess, gram

def rank_of(A, tol=1e-6):
    ev = np.linalg.eigvalsh(A)[::-1]; return int((ev > tol * ev[0]).sum()), ev / ev[0]

def job(args):
    name, d, seed = args
    d = np.array(d, float); n = len(d); r = n
    val, grad, hess, gram = make(d, r)
    rng = np.random.default_rng(seed)
    maxima = []; crits = []
    for _ in range(12):
        res = minimize(lambda p: -val(p), rng.normal(size=2 * n * r), jac=lambda p: -grad(p), method="BFGS",
                       options={"gtol": 1e-11, "maxiter": 20000})
        A = gram(res.x); rk, ev = rank_of(A)
        maxima.append((round(-res.fun, 7), rk, float(ev[1])))
    for _ in range(12):
        p0 = rng.normal(size=2 * n * r)
        res = least_squares(grad, p0, jac=hess, method="lm", xtol=1e-15, ftol=1e-15, gtol=1e-15, max_nfev=3000)
        g = np.linalg.norm(grad(res.x)); A = gram(res.x)
        if g < 1e-8 and np.all(np.isfinite(A)) and np.abs(1 - A[~np.eye(n, dtype=bool)]).min() > 1e-6:
            rk, ev = rank_of(A)
            top = np.linalg.eigvalsh(hess(res.x))[-1]
            crits.append((round(val(res.x), 6), rk, float(top)))
    return name, maxima, crits

if __name__ == "__main__":
    rng = np.random.default_rng(11)
    cases = {"n3 unit": [1.] * 3, "n3 mixed<1": [.3, .6, .9], "n3 across1": [.5, 1., 2.],
             "n4 unit": [1.] * 4, "n4 mixed<1": [.2, .5, .8, .95], "n4 across1": [.3, .9, 1.5, 3.],
             "n5 mixed<1": [.1, .4, .6, .8, .99], "n5 across1": [.2, .7, 1., 1.6, 4.],
             "n6 rand<1": list(rng.uniform(.1, 1, 6)), "n6 rand": list(rng.uniform(.2, 3, 6))}
    jobs = [(k, v, s) for k, v in cases.items() for s in range(12)]
    with Pool(64) as pool: out = pool.map(job, jobs)
    for k in cases:
        mx = [m for name, ms, cs in out if name == k for m in ms]
        cr = [c for name, ms, cs in out if name == k for c in cs]
        vals = sorted({(v, rk) for v, rk, _ in mx}, reverse=True)
        print(f"== {k}: {len(mx)} ascents -> {len(vals)} distinct (value, rank) limits")
        for v, rk in vals[:6]:
            cnt = sum(1 for a, b, _ in mx if (a, b) == (v, rk)); print(f"     local max value={v:.7f} rank={rk} hits={cnt}")
        hi = [c for c in cr if c[1] >= 2]
        print(f"   critical points found: {len(cr)}; rank>=2: {len(hi)}; "
              f"of those with Hessian top eig <= 1e-7 (candidate local max): {sum(1 for c in hi if c[2] <= 1e-7)}")
        for rk in sorted({c[1] for c in hi}):
            tops = [c[2] for c in hi if c[1] == rk]
            print(f"     rank {rk}: {len(tops)} critical pts, min top-Hessian-eig = {min(tops):.3e}")
