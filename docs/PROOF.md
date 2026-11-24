# The proof: idea, obstacle, resolution

**Theorem.** Let $A$ be a positive semidefinite complex $n \times n$ matrix with entries $a_{ij}$. Then

$$
\prod_{i,j=1}^{n} |1-a_{ij}| \le \prod_{i=1}^{n} |1-a_{ii}^{n}| .
$$

This document explains the idea of the proof, where the first version of that idea got stuck, and how
it was completed. Sections 1 to 4 are the proof itself, as formalized in `MatrixIneq/`. Routine
verifications (differentiation under the integral, integrability, finite algebra) are left to the Lean
files.

## Notation

The geometric sum, the Poisson kernel at radius $e^{-w}$, and the Fejér kernel:

$$
F_n(t) = 1+t+\dots+t^{n-1}
$$

$$
P_w(\theta) = \frac{\sinh w}{\cosh w-\cos\theta} = 1+2\sum_{m\ge 1} e^{-mw}\cos m\theta
$$

$$
\mathrm{Fej}_n(\theta) = \frac{1-\cos n\theta}{1-\cos\theta}
$$

## The idea

The diagonal entries of $A$ are real and nonnegative. Call them $d_i$. For $d \ge 0$ the modulus of
$1-d^n$ is the modulus of $1-d$ times $F_n(d)$, so the diagonal factors on the left cancel and the
theorem becomes

$$
\prod_{i\ne j} |1-a_{ij}| \le \prod_i F_n(d_i). \qquad \text{(R)}
$$

Normalize the off-diagonal entries:

$$
a_{ij} = \sqrt{d_i d_j}\; c_{ij} .
$$

The matrix $C$ of the $c_{ij}$ is positive semidefinite with unit diagonal, and every entry has modulus
at most one. Equality holds in (R) when all $d_i$ are equal and the $c_{ij}$ are the powers of an $n$-th
root of unity, that is, for a regular $n$-gon.

This is the setting of linear-programming bounds for point configurations (Delsarte, Yudin,
Cohn–Kumar), with one difference: the points lie on circles of different radii. So we look for a *pair
inequality*, valid for all radii $s$, $t$ and all $c$ in the closed unit disc:

$$
-\log\left|1-\sqrt{st}\,c\right| \ge \frac{\gamma_0(s)+\gamma_0(t)}{2} + \sum_{m=1}^{n-2} \kappa_m(s,t)\,\mathrm{Re}\,c^m . \qquad \text{(P)}
$$

Here each $\kappa_m$ must be a positive semidefinite kernel in the two radii. Sum (P) over all pairs
$i \ne j$. For each $m$, the matrix of values of $\kappa_m$ at the $d_i$ and the entrywise power of $C$ are
both positive semidefinite, so by the Schur product theorem the full double sum over $i,j$ is
nonnegative. Only the diagonal values of the kernels survive, and (R) follows provided that

$$
(n-1)\,\gamma_0(s) - \sum_{m=1}^{n-2} \kappa_m(s,s) = -\log F_n(s) .
$$

On the diagonal $s=t$ there is essentially no choice. Tightness at the regular $n$-gon forces the
polynomial on the right of (P) to touch the left side at the nontrivial $n$-th roots of unity, and the
polynomial of degree $n-2$ that does this is the Hermite interpolant. Its coefficients and the
positivity of the interpolation error are in Section 1. They already prove the theorem when all
diagonal entries are equal.

## Where it got stuck

It remains to extend the diagonal coefficients $\Gamma_m$ to a positive semidefinite kernel for which
(P) holds. The first choice is the rank-one kernel given by the geometric mean:

$$
\kappa_m(s,t) = \sqrt{\Gamma_m(s)\,\Gamma_m(t)} .
$$

It is positive semidefinite for free, and the constant term works automatically. Everything then rests
on (P), which becomes a two-parameter family of trigonometric inequalities. With $\alpha = (p+q)/2$:

$$
-\log\left|1-e^{-\alpha}e^{i\theta}\right| \ge \frac{\Gamma_0(p)+\Gamma_0(q)}{2} + \sum_{m=1}^{n-2} \sqrt{\Gamma_m(p)\,\Gamma_m(q)}\;\cos m\theta . \qquad \text{(Star)}
$$

Numerically (Star) holds for every $n$ tested, but we did not find a proof. What we learned:

- **A threshold at 15.** The difference of the two sides is a cosine series whose coefficient sequence
  is convex for $n \le 15$, so the classical Fejér criterion proves (Star) there. From $n = 16$ on the
  sequence is no longer convex: it is a convex polynomial part minus a geometric part with a kink at
  index zero. This agrees with the remark in the source that the inequality was known for $n \le 15$.
- **A one-sided form.** The gap is monotone in the smaller of the two parameters, so (Star) follows from
  a one-sided inequality (`HIn` in Lean), which has slack everywhere except on the diagonal.
- **A form without the angle.** Multiplying that inequality by $\cosh\alpha-\cos\theta$, that is,
  dividing by the Poisson kernel, removes the geometric part exactly. The statement becomes the
  convexity of an explicit sequence, with no angle variable (`QC` in Lean). Numerically it holds for all
  $n \le 80$ tested.
- **The obstruction.** `QC` is a statement about ratios of hazard rates of the densities $k_m$, and the
  square root is what makes it hard. In one limiting regime it reduces to the numerical inequality
  $5\zeta(5) \ge 3\zeta(3)^2$. It is true for quantitative reasons, not structural ones, and we did not
  prove it.

The reductions from `QC` to `HIn` to (Star) to the theorem are formalized in `Exploration/`. The
statement `QC` itself remains open.

## What resolved it

The last reduction has a probabilistic reading. The normalized kernel

$$
\chi_m(w) = e^{mw}\,k_m(w)
$$

is a distribution function in $w$ (Section 1, fact K4). Let $\tau$ be a random variable with this
distribution. Then the diagonal coefficient is an expectation:

$$
m\,\Gamma_m(p) = \mathbb{E}\; e^{-m\max(p,\tau)} .
$$

There are two ways to split this into a kernel in two variables. One takes the square root outside the
expectation; that is the geometric mean, which led to (Star). The other takes it inside:

$$
m\,K_m(p,q) = \mathbb{E}\; e^{-m\max(p,\tau)/2}\; e^{-m\max(q,\tau)/2} .
$$

This is a mixture of rank-one kernels, hence positive semidefinite, and it has the same diagonal.

We had excluded kernels of this kind earlier, because the simplest one gives the wrong constant term in
(P). The right way to prove (P) for this kernel is to integrate the equal-radius inequality along a
path on which the interpolation radius moves from $p$ to $q$ at twice the speed of the integration
variable. Then the constant term is exactly the average of the two diagonal constants, and (P) needs no
new estimate at all (Section 3). The geometric mean, and with it (Star) and `QC`, is not needed.

## 1. The diagonal: an interpolation certificate

For $w > 0$ and $0 \le m \le n-2$ define the kernels

$$
k_m(w) = \frac{\sinh((n-m)w) - (n-m)\sinh w}{\cosh nw - 1}
$$

and their tail integrals

$$
\Gamma_m(p) = \int_p^\infty k_m(w)\,dw \quad (m \ge 1), \qquad
\Gamma_0(p) = \int_p^\infty \frac{k_0(w)-1}{2}\,dw .
$$

These are the cosine coefficients of the polynomial of degree $n-2$ that interpolates the function

$$
\theta \mapsto -\log\left|1-e^{-p}e^{i\theta}\right|
$$

to second order at the nontrivial $n$-th roots of unity. That is where the formulas come from, but only
the following four facts are used.

**K1. Positivity.** Each $k_m$ is nonnegative, because $\sinh Nw \ge N \sinh w$.

**K2. Kernel inequality.** Define the cosine polynomial

$$
\Pi_w(\theta) = \frac{k_0(w)}{2} + \sum_{m=1}^{n-2} k_m(w)\cos m\theta .
$$

Then

$$
\frac{P_w(\theta)}{2} - \Pi_w(\theta) = \frac{\rho_n(w)}{2}\,\mathrm{Fej}_n(\theta)\,P_w(\theta) \ge 0,
\qquad
\rho_n(w) = \frac{\cosh w - 1}{\cosh nw - 1} .
$$

This is a finite trigonometric identity.

**K3. Total identity.**

$$
(n-1)\,\Gamma_0(p) - \sum_{m=1}^{n-2} \Gamma_m(p) = -\log F_n(e^{-p}) .
$$

It follows by evaluating K2 at the $n$-th roots of unity, where the Fejér kernel vanishes, summing, and
integrating in $w$.

**K4. Monotonicity.** The function $\chi_m$ defined above is nondecreasing, tends to zero at zero, and
is at most one. Explicitly, with $t = e^{-w}$ and $N = n-m$,

$$
\chi_m(w) = \frac{1 - t^{2N} - N t^{N-1}(1-t^2)}{(1-t^n)^2} .
$$

It is the probability that a sum of three independent geometric random variables is at most $N-2$,
where two have ratio $t$ and are conditioned to be less than $n$, and one has ratio $t^2$. The Lean
proof is a direct calculus argument. A consequence is the hazard bound $k_m \le m\,\Gamma_m$.

Integrating K2 over $w$ from $p$ to infinity gives the equal-radius inequality

$$
-\log\left|1-e^{-p}e^{i\theta}\right| \ge \Gamma_0(p) + \sum_{m=1}^{n-2} \Gamma_m(p)\cos m\theta ,
$$

which together with K3 proves the theorem when all diagonal entries are equal.

## 2. The off-diagonal kernel

For $0 \le p \le q$ and $1 \le m \le n-2$ define

$$
K_m(p,q) = \Gamma_m(q) + \frac12 \int_p^q k_m(x)\, e^{-m(q-x)/2}\,dx ,
$$

and extend symmetrically. On the diagonal this is $\Gamma_m(p)$.

**Lemma 1 (mixture representation).** For all $p, q \ge 0$,

$$
K_m(p,q) = \frac1m \int_0^\infty \chi_m'(\tau)\; e^{-m\max(p,\tau)/2}\; e^{-m\max(q,\tau)/2}\,d\tau .
$$

*Proof.* Take $p \le q$ and split the integral at $p$ and at $q$. The part below $p$ equals

$$
\chi_m(p)\, e^{-m(p+q)/2} .
$$

Integrate by parts on the other two parts. The boundary terms at $p$ and at $q$ cancel, and what
remains is

$$
\frac m2\, e^{-mq/2} \int_p^q \chi_m(\tau)\, e^{-m\tau/2}\,d\tau + m \int_q^\infty \chi_m(\tau)\, e^{-m\tau}\,d\tau ,
$$

which is $m$ times the definition of the kernel. ∎

By K4 the weight $\chi_m'$ is nonnegative. So the kernel is a nonnegative mixture of rank-one kernels,
each the product of the following function evaluated at $p$ and at $q$:

$$
\phi_\tau(p) = e^{-m\max(p,\tau)/2} .
$$

**Corollary 2 (positive semidefiniteness).** Let $p_1, \dots, p_r \ge 0$ and let $M$ be a Hermitian
positive semidefinite $r \times r$ matrix. Then

$$
\sum_{i,j} K_m(p_i,p_j)\,\mathrm{Re}\,M_{ij} \ge 0 .
$$

Indeed, for each $\tau$ the integrand is the weight times the quadratic form of $M$ at a real vector. In
Lean the integral is truncated at a finite upper limit, and the remainder is a nonnegative multiple of a
rank-one kernel by the hazard bound.

## 3. The pair inequality

**Proposition 3.** Let $0 \le p \le q$ and $\alpha = (p+q)/2$. For all $\theta$,

$$
-\log\left|1-e^{-\alpha}e^{i\theta}\right| \ge \frac{\Gamma_0(p)+\Gamma_0(q)}{2} + \sum_{m=1}^{n-2} K_m(p,q)\cos m\theta .
$$

*Proof.* The left side is an integral of Poisson kernels:

$$
-\log\left|1-e^{-\alpha}e^{i\theta}\right| = \int_\alpha^\infty \frac{P_w(\theta)-1}{2}\,dw .
$$

We bound the integrand from below for each $w$.

*For $w \ge q$.* Fact K2 gives directly

$$
\frac{P_w(\theta)}{2} \ge \Pi_w(\theta) .
$$

*For $\alpha \le w \le q$.* Put $x = 2w-q$, which lies between $p$ and $q$, and $s = w-x = q-w \ge 0$.
Convolution with the Poisson kernel $P_s$ preserves inequalities, multiplies the $m$-th cosine
coefficient by $e^{-ms}$, and maps $P_x$ to $P_w$. Applying it to K2 at the point $x$ gives

$$
\frac{P_w(\theta)}{2} \ge \frac{k_0(x)}{2} + \sum_{m=1}^{n-2} k_m(x)\, e^{-m(q-w)}\cos m\theta .
$$

Equivalently: the harmonic function whose boundary values are the nonnegative function in K2 is
nonnegative on the smaller circle of radius $e^{-s}$.

*Integration.* The range $w \ge q$ contributes

$$
\Gamma_0(q) + \sum_{m=1}^{n-2} \Gamma_m(q)\cos m\theta .
$$

On the range $\alpha \le w \le q$ substitute $x = 2w-q$, so that $dw = dx/2$. The constant term gives

$$
\frac12 \int_p^q \frac{k_0(x)-1}{2}\,dx = \frac{\Gamma_0(p)-\Gamma_0(q)}{2} ,
$$

and the coefficient of $\cos m\theta$ gives

$$
\frac12 \int_p^q k_m(x)\, e^{-m(q-x)/2}\,dx .
$$

Adding the two ranges yields the claim. The constant term is exactly the average of $\Gamma_0(p)$ and
$\Gamma_0(q)$. ∎

The substitution is what makes the constant come out right: the interpolation radius $x$ runs from $p$
to $q$ at twice the speed of $w$, so each of $p$ and $q$ is charged half of the constant.

In Lean, Proposition 3 is organised as monotonicity: the gap is nonincreasing in $p$ on the interval
from zero to $q$, because its derivative in $p$ is minus the smoothed form of K2, and it is nonnegative
at $p = q$.

## 4. Assembly

First suppose that every diagonal entry is positive and at most one. Write

$$
d_i = e^{-p_i}, \qquad \alpha_{ij} = \frac{p_i+p_j}{2}, \qquad a_{ij} = e^{-\alpha_{ij}}\, c_{ij} .
$$

Fix $i \ne j$ and consider, as a function of $c$ in the closed unit disc,

$$
-\log\left|1-e^{-\alpha_{ij}}c\right| - \frac{\Gamma_0(p_i)+\Gamma_0(p_j)}{2} - \sum_{m=1}^{n-2} K_m(p_i,p_j)\,\mathrm{Re}\,c^m .
$$

It is harmonic and, by Proposition 3, nonnegative on the unit circle. By the minimum principle it is
nonnegative at $c = c_{ij}$. (If $a_{ij} = 1$ the left side of (R) is zero and there is nothing to
prove.) Summing over $i \ne j$:

$$
\sum_{i\ne j} -\log|1-a_{ij}| \ge (n-1)\sum_i \Gamma_0(p_i) + \sum_{m=1}^{n-2} \left[\, \sum_{i,j} K_m(p_i,p_j)\,\mathrm{Re}\,c_{ij}^{m} - \sum_i \Gamma_m(p_i) \right] .
$$

The entrywise power of $C$ is positive semidefinite by the Schur product theorem, so the double sum is
nonnegative by Corollary 2. Dropping it and using K3:

$$
\sum_{i\ne j} -\log|1-a_{ij}| \ge \sum_i \left[ (n-1)\,\Gamma_0(p_i) - \sum_{m=1}^{n-2} \Gamma_m(p_i) \right] = -\sum_i \log F_n(d_i) .
$$

This is (R).

**Arbitrary diagonal values.** For $s > 0$ put

$$
\gamma_0(s) = \Gamma_0(|\log s|) - \max(\log s,\,0), \qquad
\gamma_m(s) = \Gamma_m(|\log s|), \qquad
\kappa_m(s,t) = K_m(|\log s|,\,|\log t|) .
$$

The total identity still holds, because $F_n(s) = s^{n-1} F_n(1/s)$. The pair inequality (P) for all
positive $s$, $t$ follows from Proposition 3 and an elementary bound: for $K \ge 1$, $0 \le c \le 1$ and
$z$ on the unit circle,

$$
|1 - Kc\,z| \le K\,\left|1 - \frac{c}{K}\,z\right| .
$$

A row with zero diagonal entry is a zero row and contributes nothing. The cases $n \le 1$ are trivial.

## 5. Lean

The final statement is `MatrixIneq.mainTheorem : Statement.MainTheorem` in `MatrixIneq/Main.lean`.

- K1 is `kern_nonneg`, K2 is `kern_poisson_le`, K3 is `total_Gam`, K4 is `chi_mono`; the hazard bound is
  `kern_le_mul_Gam`.
- Lemma 1 is `tauK_repr` and Corollary 2 is `tauK_psd`.
- Proposition 3 is `tauStar`; its smoothing step is `kern_poisson_smooth_le`.
- The assembly is `reducedAt_of_kcertificate`, `tauCertificate` and `reducedAt_all`.

## 6. Remarks

- Equality holds for the matrix with entries $d\,\omega^{i-j}$, where $\omega$ is a primitive $n$-th root
  of unity. All inequalities above are equalities when the $p_i$ are equal and the $c_{ij}$ run through
  the $n$-th roots of unity.
- The kernel of Section 2 is not the geometric mean; it is smaller. The inequality (Star) with the
  geometric mean appears to be true as well, but we did not prove it. What is known about it is in the
  Lean library `Exploration/` and in `worklog/`.
- The proof has no threshold in $n$. The value 15 appears only for the convexity criterion applied to
  the geometric-mean route.
