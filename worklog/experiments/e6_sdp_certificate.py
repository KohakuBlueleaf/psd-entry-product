"""E6. SDP dual certificate for a fixed, possibly unequal diagonal d (rho_i = sqrt(d_i)).

Write a_ij = rho_i rho_j c_ij, C a complex correlation matrix.  Energy  E(C) = sum_{i!=j} g_ij(c_ij),
g_ij(z) = -log|1 - rho_i rho_j z|  (superharmonic on the unit disc).  Certificate:
    h_ij(z) = C0[i,j] + sum_{m=1}^{D} Re( conj(Cm[i,j]) z^m ),   Cm Hermitian PSD,   h_ij <= g_ij on |z|=1.
Then h_ij <= g_ij on the disc (minimum principle) and <Cm, C^{(m)}> >= 0 (Schur product theorem), hence
    E(C) >= sum_{i!=j} C0[i,j] - sum_m tr(Cm)        for every correlation matrix C of any rank.
The SDP maximises this bound.  We compare it with the true minimum energy (found by direct optimisation,
attained at rank one in all runs of E3).  Equality  <=>  the harmonic relaxation is tight  =>  R1 and the bound.
"""
import numpy as np, cvxpy as cp, sys
from scipy.optimize import minimize
from multiprocessing import Pool

def min_energy(d, r, tries=60, seed=0):
    n = len(d); rng = np.random.default_rng(seed); off = ~np.eye(n, dtype=bool)
    def E(p):
        V = (p[:n * r] + 1j * p[n * r:]).reshape(n, r)
        V = V / np.linalg.norm(V, axis=1, keepdims=True) * np.sqrt(d)[:, None]
        return -np.sum(np.log(np.abs(1 - (V @ V.conj().T)[off]) + 1e-300))
    return min(minimize(E, rng.normal(size=2 * n * r), method="BFGS", options={"gtol": 1e-10}).fun for _ in range(tries))

def sdp_bound(d, D, grid=1440):
    n = len(d); rho = np.sqrt(d)
    th = (np.arange(grid) + 0.5) * 2 * np.pi / grid
    C0 = cp.Variable((n, n), symmetric=True)
    Cm = [cp.Variable((n, n), hermitian=True) for _ in range(D)]
    cons = [X >> 0 for X in Cm]
    for i in range(n):
        for j in range(i + 1, n):
            g = -np.log(np.abs(1 - rho[i] * rho[j] * np.exp(1j * th)))
            expr = C0[i, j] + sum(cp.real(cp.conj(Cm[m - 1][i, j]) * np.exp(1j * m * th)) for m in range(1, D + 1))
            cons.append(expr <= g)
    obj = 2 * sum(C0[i, j] for i in range(n) for j in range(i + 1, n)) - sum(cp.real(cp.trace(X)) for X in Cm)
    prob = cp.Problem(cp.Maximize(obj), cons)
    prob.solve(solver=cp.CLARABEL)
    ranks = [int((np.linalg.eigvalsh(X.value) > 1e-7 * max(1e-12, np.trace(X.value).real)).sum()) for X in Cm]
    return prob.value, ranks, [np.trace(X.value).real for X in Cm]

def job(args):
    name, d, D = args
    d = np.array(d, float); n = len(d)
    emin = min(min_energy(d, n), min_energy(d, 1, seed=1))
    val, ranks, tr = sdp_bound(d, D)
    target = -np.sum(np.log(sum(d ** k for k in range(n))))
    return name, D, emin, val, target, ranks, tr

if __name__ == "__main__":
    cases = {"n3 unit": [1.] * 3, "n3 equal .5": [.5] * 3, "n3 mixed<1": [.3, .6, .9], "n3 across1": [.5, 1., 2.],
             "n3 mild": [.5, .55, .6], "n4 mixed<1": [.2, .5, .8, .95], "n4 across1": [.3, .9, 1.5, 3.],
             "n4 mild": [.5, .6, .7, .8], "n5 mixed<1": [.1, .4, .6, .8, .99]}
    jobs = [(k, v, D) for k, v in cases.items() for D in (len(v) - 1, 2 * len(v), 24)]
    with Pool(len(jobs)) as pool: out = pool.map(job, jobs)
    for name, D, emin, val, target, ranks, tr in out:
        print(f"{name:12s} D={D:2d}: true min energy={emin:.6f}  SDP bound={val:.6f}  gap={emin - val:.2e}  "
              f"(theorem's bound {target:.6f})  ranks(Cm)={ranks}")
