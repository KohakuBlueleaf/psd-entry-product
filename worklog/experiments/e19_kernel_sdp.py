"""E19. Which positive definite kernels make the pairwise certificate work?  Over a grid of parameters s_1..s_N:
unknowns  K_m (N x N PSD, m = 1..D),  L0 (N x N symmetric),  e (N).   Constraints
   L0[a,b] + sum_m K_m[a,b] cos(m theta) <= g_{sqrt(s_a s_b)}(theta) - eps * (u_a-u_b)^2      (all pairs, theta grid)
   L0[a,b] >= (e_a + e_b)/2,        (n-1) e_a - sum_m K_m[a,a] >= -log F_n(s_a).
These imply the theorem for every diagonal with entries in the grid.  Maximise eps and inspect the optimum:
ranks of K_m, how K_m[a,b] compares with sqrt(c_m(s_a) c_m(s_b)) and with c_m(sqrt(s_a s_b))."""
import numpy as np, cvxpy as cp, sys
from e13_gm_certificate import coeffs

def solve(n, D, us, grid=720):
    N = len(us); s = np.exp(us)
    th = (np.arange(grid) + 0.5) * np.pi / grid
    K = [cp.Variable((N, N), PSD=True) for _ in range(D)]
    L0 = cp.Variable((N, N), symmetric=True); e = cp.Variable(N); eps = cp.Variable()
    cons = []
    cosm = np.cos(np.outer(np.arange(1, D + 1), th))
    for a in range(N):
        cons.append((n - 1) * e[a] - sum(K[m][a, a] for m in range(D)) >= -np.log(sum(s[a] ** k for k in range(n))))
        for b in range(a, N):
            tau = np.sqrt(s[a] * s[b])
            g = -0.5 * np.log(1 + tau * tau - 2 * tau * np.cos(th))
            cons.append(L0[a, b] + sum(K[m][a, b] * cosm[m] for m in range(D)) <= g - eps * (us[a] - us[b]) ** 2)
            cons.append(L0[a, b] >= (e[a] + e[b]) / 2)
    prob = cp.Problem(cp.Maximize(eps), cons); prob.solve(solver=cp.CLARABEL)
    return eps.value, [k.value for k in K], L0.value, e.value

us = np.array([-1.6, -0.9, -0.4, 0.0, 0.5, 1.1])
np.set_printoptions(precision=4, suppress=True, linewidth=160)
for n, D in ((4, 3), (4, 8), (5, 3), (5, 10), (6, 5)):
    eps, K, L0, e = solve(n, D, us)
    print(f"\n=== n={n}, degree D={D}: max eps = {eps:.5f}")
    cm = np.array([coeffs(n, np.exp(u)) for u in us])           # CK coefficients on the grid
    Dck = cm.shape[1] - 1
    for m in range(min(D, 3)):
        ev = np.linalg.eigvalsh(K[m])[::-1]
        line = f"  m={m+1}: eig(K_m)/max = {np.round(ev / ev[0], 3)}  diag(K_m) = {np.round(np.diag(K[m]), 4)}"
        if m + 1 <= Dck: line += f"  CK c_m = {np.round(cm[:, m + 1], 4)}"
        print(line)
    # reference: slack of the geometric-mean certificate in the same normalisation
