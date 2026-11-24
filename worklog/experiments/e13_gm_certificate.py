"""E13. 'Geometric mean of coefficients' certificate.  Let h_s = c_0(s) + sum_m c_m(s) cos(m theta) be the
equal-diagonal (Cohn-Kumar) certificate for g_s(theta) = -log|1 - s e^{i theta}|.  Test the pointwise inequality
  (**)  g_{sqrt(st)}(theta) >= (c_0(s)+c_0(t))/2 + sum_{m>=1} sqrt(c_m(s) c_m(t)) cos(m theta)   for all s,t>0, theta.
If (**) holds then, with C_m = phi_m phi_m^T, phi_m(i) = sqrt(c_m(d_i)) (rank one PSD), the Schur product theorem
gives the theorem for ALL diagonals directly from the equal-diagonal certificate.
"""
import numpy as np

def coeffs(n, tau):
    """Chebyshev coefficients of the Hermite interpolant of g at the nontrivial n-th roots of unity."""
    D = n - 2 if n % 2 else n - 1
    m = np.arange(D + 1); rows = []; rhs = []
    q = lambda t: 1 + tau * tau - 2 * tau * np.cos(t)
    for k in range(1, n // 2 + 1):
        t = 2 * np.pi * k / n
        rows.append(np.cos(m * t)); rhs.append(-0.5 * np.log(q(t)))
        if abs(t - np.pi) > 1e-12:
            rows.append(-m * np.sin(m * t)); rhs.append(-tau * np.sin(t) / q(t))
        else:
            rows.append(-m * m * np.cos(m * t)); rhs.append(tau / (1 + tau) ** 2)
    return np.linalg.solve(np.array(rows), np.array(rhs))
if __name__ == "__main__":
    th = np.linspace(0, 2 * np.pi, 4001)
    rng = np.random.default_rng(1)
    for n in (2, 3, 4, 5, 6, 8):
        worst = np.inf; arg = None; neg = 0; N = 3000
        for _ in range(N):
            s, t = np.exp(rng.uniform(-3, 2, 2))
            cs, ct = coeffs(n, s), coeffs(n, t)
            tau = np.sqrt(s * t)
            g = -0.5 * np.log(1 + tau * tau - 2 * tau * np.cos(th) + 1e-300)
            m = np.arange(1, len(cs))
            h = 0.5 * (cs[0] + ct[0]) + (np.sqrt(np.clip(cs[1:] * ct[1:], 0, None))[:, None] * np.cos(np.outer(m, th))).sum(0)
            v = (g - h).min()
            if v < -1e-9: neg += 1
            if v < worst: worst, arg = v, (s, t)
        print(f"n={n}: min over (s,t,theta) of g-h = {worst:+.3e} at s={arg[0]:.3f}, t={arg[1]:.3f};  violations {neg}/{N}")

