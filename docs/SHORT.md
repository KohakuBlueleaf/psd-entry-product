# The short proof

[`Short.lean`](../Short.lean) is a second, self-contained Lean proof of the same theorem: one file,
457 lines, importing only Mathlib. It does not use `MatrixIneq/`.

It was written in response to a one-page sum-of-squares proof that a community of readers produced
after the first version.
That proof keeps the kernels $\chi_m$ of [`PROOF.md`](PROOF.md) and replaces the two-radius inequality by
a single integral identity whose integrands are visibly nonnegative. `Short.lean` proves the same thing
in differential form: instead of an identity between integrals, it shows that one explicit function of
a real parameter is nondecreasing. There are no integrals in the file.

This document is the mathematical content of `Short.lean`, in the order of the file.

## Notation

Throughout, $n \ge 1$ is the size of the matrix and $0 < t < 1$. Put

$$
S_n(z) = 1 + z + \dots + z^{n-1} .
$$

For $K \ge 0$ and $0 \le m < n$ define

$$
\nu_K(t) = 1 - t^{2K+2} - (K+1)\,t^{K}(1-t^2)
$$

$$
\chi_m(t) = \frac{\nu_{n-1-m}(t)}{(1-t^n)^2}
$$

and, for a complex number $a \ne 1$,

$$
g_t(a) = \frac{a}{1-a} + \frac{1+\chi_0(t)}{2} - \sum_{m=0}^{n-1} \chi_m(t)\,a^m .
$$

With $t = e^{-w}$ this $\chi_m$ is the function $\chi_m(w) = e^{mw}k_m(w)$ of `PROOF.md`. Note that
$\nu_0 = 0$, so $\chi_{n-1} = 0$.

## 1. Four facts about the kernels

**K1. Sign.** For $0 \le t \le 1$,

$$
\nu_K(t) \ge 0 .
$$

This follows by induction from

$$
\nu_{K+1}(t) = t\,\nu_K(t) + (1-t)(1-t^{K+1})(1-t^{K+2}) .
$$

Hence $\chi_m \ge 0$. (`ν_nonneg`)

**K2. Monotonicity.** Each $\chi_m$ is nonincreasing on $(0,1)$. Write $n = m+1+K$. The sign of the
derivative reduces to

$$
2n\,t^{m+1}\,\nu_K(t) \le (K+1)\,B\,(1-t^n), \qquad B = K(1-t^2) - 2t^2(1-t^K),
$$

and this is the product of two elementary inequalities,

$$
2t\,\nu_K(t) \le B\,(1-t^{K+1}), \qquad n\,t^m(1-t^{K+1}) \le (K+1)(1-t^n) .
$$

The first is an induction on $K$ using Bernoulli's inequality, the second is Bernoulli's inequality twice.
(`J`, `χ_deriv`, `cf_deriv`)

**K3. The circle identity.** For $|z| = 1$,

$$
2\,\mathrm{Re}\,g_t(tz) = \frac{t^{n-1}(1-t^2)(1-t)^2}{(1-t^n)^2}\cdot\frac{|S_n(z)|^2}{|1-tz|^2} \ge 0 .
$$

This is a polynomial identity in $z$ and $\bar z = 1/z$: a Fejér kernel times a Poisson kernel. In Lean
it is proved for any $z, w$ with $zw = 1$ from three geometric sums and the Fejér identity

$$
\sum_{m=0}^{n-1} (n-m)(z^m + w^m) = n + S_n(z)\,S_n(w) .
$$

(`refl'`, `fej`, `ksum`, `circ`, `circ_re`)

**K4. The disc.** The function $g_t$ is holomorphic on a neighbourhood of the closed disc $|a| \le t$. By
K3 the function $e^{-g_t}$ has modulus at most one on the circle $|a| = t$, so by the maximum modulus
principle

$$
\mathrm{Re}\,g_t(a) \ge 0 \qquad (|a| \le t) .
$$

At the point $a = t$ the identity K3 with $z = 1$ gives the exact value

$$
g_t(t) = \frac{n\,t^n}{1-t^n} + n\cdot\frac{1-\chi_0(t)}{2} .
$$

(`disc`, `diag`)

## 2. Capping the diagonal

Let $A$ be positive semidefinite, $r_i = \sqrt{a_{ii}}$, and for $s \ge 0$ let

$$
\lambda_i(s) = \frac{\min(r_i, s)}{r_i}, \qquad a_{ij}(s) = \lambda_i(s)\,\lambda_j(s)\,a_{ij} .
$$

So $A(s)$ is $A$ with every diagonal entry larger than $s^2$ scaled down to $s^2$. It is a congruence of
$A$ by a real diagonal matrix, hence positive semidefinite, and:

- $a_{ii}(s) = \min(r_i, s)^2$, and $|a_{ij}(s)| \le s^2$ (from the $2\times 2$ minors);
- $A(0) = 0$, and $A(1) = A$ when all $a_{ii} \le 1$;
- every entrywise power of $A(s)$ has nonnegative entry sum (Schur product theorem);
- with $\varepsilon_i = 1$ if $s < r_i$ and $\varepsilon_i = 0$ otherwise, the right derivative is

$$
\frac{d}{ds}\,a_{ij}(s) = k_{ij}\,a_{ij}(s), \qquad k_{ij} = \frac{\varepsilon_i + \varepsilon_j}{s} .
$$

Call the index $i$ *capped* at $s$ when $\varepsilon_i = 1$; then $a_{ii}(s) = s^2$.
(`sc`, `sc_psd`, `nle`, `schur`, `lam`, `al`, `al_deriv`, `al_diag`, `al_norm`)

## 3. The monotone quantity

For $0 \le s < 1$ put $t = s^2$ and

$$
\Psi(s) = \sum_i \log\bigl(1-a_{ii}(s)^n\bigr)
 - \sum_{i,j}\Bigl[\log\bigl(1-a_{ij}(s)\bigr) + \sum_{m=1}^{n-1} \frac{\chi_m(s^2)}{m}\,a_{ij}(s)^m\Bigr] .
$$

Its real part is

$$
\mathrm{Re}\,\Psi(s) = \log\frac{\prod_i |1-a_{ii}(s)^n|}{\prod_{i,j}|1-a_{ij}(s)|}
 - \sum_{m=1}^{n-1} \frac{\chi_m(s^2)}{m}\,Q_m(s), \qquad Q_m(s) = \sum_{i,j}\mathrm{Re}\,a_{ij}(s)^m \ge 0 .
$$

**Claim.** $\mathrm{Re}\,\Psi$ has a nonnegative right derivative at every $s \in (0,1)$. (`entry`, `step`)

Differentiate term by term. Since

$$
\frac{a}{1-a} - \sum_{m=1}^{n-1}\chi_m a^m = g_t(a) - \frac{1-\chi_0}{2},
$$

the right derivative of $\mathrm{Re}\,\Psi$ is

$$
-\sum_i k_{ii}\,\mathrm{Re}\,\frac{n\,a_{ii}^n}{1-a_{ii}^n}
 + \sum_{i,j} k_{ij}\Bigl(\mathrm{Re}\,g_t(a_{ij}) - \frac{1-\chi_0}{2}\Bigr)
 - \sum_{m=1}^{n-1} \frac{1}{m}\,\frac{d\chi_m(s^2)}{ds}\,Q_m .
$$

Now use three things.

First, $\sum_{i,j} k_{ij} = n \sum_i k_{ii}$, because $k_{ij}$ is a function of $i$ plus a function of $j$.

Second, the diagonal terms cancel. If $i$ is capped then $a_{ii} = t$, and the value of $g_t(t)$ in K4
says exactly that

$$
k_{ii}\,g_t(a_{ii}) = k_{ii}\Bigl(\frac{n\,a_{ii}^n}{1-a_{ii}^n} + n\cdot\frac{1-\chi_0}{2}\Bigr) .
$$

If $i$ is not capped then $k_{ii} = 0$ and both sides vanish.

Third, the last sum is nonnegative by K2 and $Q_m \ge 0$.

What remains is

$$
\frac{d}{ds}\,\mathrm{Re}\,\Psi \ge \sum_{i \ne j} k_{ij}\,\mathrm{Re}\,g_t(a_{ij}) \ge 0,
$$

by K4, since $k_{ij} \ge 0$ and $|a_{ij}| \le t$.

## 4. Conclusion

$\mathrm{Re}\,\Psi$ is continuous on $[0,1)$, vanishes at $0$, and has a nonnegative right derivative on
$(0,1)$. So $\mathrm{Re}\,\Psi(s) \ge 0$ for $0 \le s < 1$. As $\chi_m \ge 0$ (K1) and $Q_m \ge 0$,

$$
\prod_{i,j} |1-a_{ij}(s)| \le \prod_i |1-a_{ii}(s)^n| \qquad (0 < s < 1).
$$

(`flow`) Both sides are continuous in $s$. Letting $s \to 1$ proves the theorem for every $A$ whose
diagonal entries are at most one. (`core`)

For general $A$ put $\mu_i = \max(1, r_i)$ and $b_{ij} = a_{ij}/(\mu_i\mu_j)^2$. Then $B$ is positive
semidefinite with $b_{ii} = \min(a_{ii}, 1/a_{ii}) \le 1$. For $|z| \le \mu$ and $\mu \ge 1$,

$$
|1-z| \le \mu\,\Bigl|1-\frac{z}{\mu^2}\Bigr|,
$$

applied with $\mu = \mu_i\mu_j$ and $z = a_{ij}$, and on the diagonal

$$
\mu_i^{2n}\,|1-b_{ii}^n| = |1-a_{ii}^n| .
$$

Multiplying over all entries,

$$
\prod_{i,j}|1-a_{ij}| \le \prod_i \mu_i^{2n} \prod_{i,j}|1-b_{ij}| \le \prod_i \mu_i^{2n} \prod_i |1-b_{ii}^n|
 = \prod_i |1-a_{ii}^n| .
$$

(`scal`, `main`)

## Relation to the integral identity

When all diagonal entries are at most one, integrating the derivative computed in Section 3 from $0$
to $1$ gives an identity of the form

$$
\log\frac{\prod_i |1-a_{ii}^n|}{\prod_{i,j}|1-a_{ij}|}
 = \sum_{i\ne j}\int k_{ij}\,\mathrm{Re}\,g_t(a_{ij}(s))\,ds
 + \sum_{m=1}^{n-1} \int \frac{1}{m}\Bigl(-\frac{d\chi_m(s^2)}{ds}\Bigr)\,Q_m(s)\,ds ,
$$

with both integrands nonnegative. Up to the change of variable $s^2 = e^{-x}$ this is the identity of the
sum-of-squares proof, and it also says
what the gap in the theorem is made of. `Short.lean` only needs the sign of the integrands, so it never
integrates. The price is one use of the maximum modulus principle (K4) in place of an explicit
sum-of-squares formula inside the disc.

## Checking

`Comparator/SolutionShort.lean` states `Statement.MainTheorem` and proves it by `Short.main`.
`scripts/verify.sh` checks this file too: source scan, axioms (`propext`, `Classical.choice`,
`Quot.sound`), `leanchecker`, and `lake comparator --paranoid` with `comparator-short.json`.
