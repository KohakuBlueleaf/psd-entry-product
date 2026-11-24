import numpy as np
rng = np.random.default_rng(0)
def lhs_rhs(A):
    n = A.shape[0]
    return np.prod(np.abs(1 - A)), np.prod(np.abs(1 - np.diag(A) ** n))
worst = -np.inf; cnt = 0
for n in range(1, 8):
    for trial in range(40000):
        r = rng.integers(1, n + 1)
        B = (rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))) * rng.choice([0.2, 0.5, 1, 2])
        A = B @ B.conj().T
        l, rr = lhs_rhs(A)
        cnt += 1
        if rr > 0:
            worst = max(worst, (l - rr) / max(rr, 1e-300))
        assert l <= rr * (1 + 1e-9) + 1e-12, (n, l, rr)
print("trials", cnt, "max relative (lhs-rhs)/rhs:", worst)
# equality family: a_ij = r^2 w^(i-j)
for n in (2, 3, 5, 7):
    w = np.exp(2j * np.pi / n); x = 0.8 * w ** np.arange(n)
    print(n, *lhs_rhs(np.outer(x, x.conj())))
# alternative misreadings should fail: e.g. RHS with a_ii (no power), n>=2
bad = 0
for trial in range(20000):
    n = 3; B = (rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))) * 0.5
    A = B @ B.conj().T
    if np.prod(np.abs(1 - A)) > np.prod(np.abs(1 - np.diag(A))) * (1 + 1e-9): bad += 1
print("violations of the no-power variant (expected >0):", bad)
