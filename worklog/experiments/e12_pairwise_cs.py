"""E12. Pairwise Cauchy-Schwarz for M(d) = max over PSD A with diag d of prod_{i!=j}|1-a_ij|:
        (PC)   M(s, t, h)^2  <=  M(s, s, h) * M(t, t, h)        (h = remaining n-2 diagonal entries).
If (PC) holds, the standard iteration gives  M(d)^n <= prod_i M(d_i,...,d_i) = prod_i F_n(d_i)^n,
i.e. the theorem follows from the equal-diagonal case.  M is computed by multi-start ascent over all ranks.
"""
import numpy as np, torch
from scipy.optimize import minimize
from multiprocessing import Pool
torch.set_default_dtype(torch.float64); torch.set_num_threads(1)

def logM(d, tries=40, seed=0):
    d = np.asarray(d, float); n = len(d); r = n; dt = torch.tensor(d)
    off = ~torch.eye(n, dtype=torch.bool)
    def f(p):
        V = torch.complex(p[:n * r], p[n * r:]).reshape(n, r)
        V = V / torch.linalg.norm(V, dim=1, keepdim=True) * torch.sqrt(dt)[:, None]
        return -torch.log(torch.abs(1 - (V @ V.conj().T)[off])).sum()
    def fg(p):
        x = torch.tensor(p, requires_grad=True); y = f(x); y.backward(); return y.item(), x.grad.numpy()
    rng = np.random.default_rng(seed)
    return max(-minimize(fg, rng.normal(size=2 * n * r), jac=True, method="L-BFGS-B",
                         options={"maxiter": 3000, "ftol": 1e-15, "gtol": 1e-10}).fun for _ in range(tries))

def job(args):
    k, s, t, h = args
    a = logM([s, t] + list(h)); b = logM([s, s] + list(h)); c = logM([t, t] + list(h))
    return 2 * a - b - c, s, t, h

if __name__ == "__main__":
    rng = np.random.default_rng(4); jobs = []
    for n in (3, 4, 5, 6):
        for k in range(40):
            hi = rng.choice([1.0, 3.0])
            s, t = rng.uniform(.05, hi, 2); h = rng.uniform(.05, hi, n - 2)
            jobs.append((k, s, t, tuple(h)))
    with Pool(64) as pool: out = pool.map(job, jobs)
    for n in (3, 4, 5, 6):
        rows = [o for o in out if len(o[3]) == n - 2]
        w = max(rows, key=lambda o: o[0])
        print(f"n={n}: max of 2logM(s,t,h)-logM(s,s,h)-logM(t,t,h) = {w[0]:+.3e} over {len(rows)} cases "
              f"(at s={w[1]:.3f} t={w[2]:.3f} h={np.round(w[3], 3)}); #positive>1e-6: {sum(o[0] > 1e-6 for o in rows)}")
