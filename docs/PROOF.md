# The proof: idea, obstacle, resolution

**Theorem.** Let $A=(a_{ij})\in\mathbb C^{n\times n}$ be positive semidefinite. Then
$$\prod_{i,j=1}^{n}|1-a_{ij}|\ \le\ \prod_{i=1}^{n}|1-a_{ii}^{\,n}| .$$

This document explains the idea of the proof, where the first version of that idea got stuck, and how it
was completed. Sections 1–4 are the proof itself, as formalized in `MatrixIneq/`; routine verifications
(differentiation under the integral, integrability, finite algebra) are left to the Lean files.

Notation: $F_n(t)=1+t+\dots+t^{n-1}$; $\mathcal P_w(\theta)=\dfrac{\sinh w}{\cosh w-\cos\theta}=1+2\sum_{m\ge1}e^{-mw}\cos m\theta$
is the Poisson kernel at radius $e^{-w}$; $\mathrm{Fej}_n(\theta)=\dfrac{1-\cos n\theta}{1-\cos\theta}=\bigl|\sum_{j<n}e^{ij\theta}\bigr|^2$.

## The idea

The diagonal entries $d_i=a_{ii}$ are real and nonnegative, and $|1-d^n|=|1-d|\,F_n(d)$, so the theorem is
$$\prod_{i\ne j}|1-a_{ij}|\ \le\ \prod_iF_n(d_i).\tag{R}$$
Write $a_{ij}=\sqrt{d_id_j}\,c_{ij}$; then $C=(c_{ij})$ is positive semidefinite with unit diagonal and
$|c_{ij}|\le1$. Equality holds in (R) when all $d_i$ are equal and the $c_{ij}$ are the powers of an $n$-th
root of unity, which is the configuration of a regular $n$-gon. This is the situation of
linear-programming bounds for point configurations (Delsarte, Yudin, Cohn–Kumar), with one difference:
the points lie on circles of different radii. So we look for a pair inequality
$$-\log\bigl|1-\sqrt{st}\,c\bigr|\ \ge\ \tfrac12\bigl(\gamma_0(s)+\gamma_0(t)\bigr)+\sum_{m=1}^{n-2}\kappa_m(s,t)\,\mathrm{Re}\,c^m\qquad(|c|\le1)\tag{P}$$
in which every $\kappa_m$ is a positive semidefinite kernel in the two radii. Summing (P) over $i\ne j$,
the matrices $[\kappa_m(d_i,d_j)]$ and $C^{\circ m}$ are both positive semidefinite, so by the Schur
product theorem the cross terms can be dropped, leaving only the diagonal values $\kappa_m(s,s)$ and
$\gamma_0(s)$. If these satisfy $(n-1)\gamma_0(s)-\sum_m\kappa_m(s,s)=-\log F_n(s)$, then (R) follows.

On the diagonal $s=t$ there is essentially no choice. Tightness at the regular $n$-gon forces the
polynomial on the right of (P) to touch $-\log|1-s\,e^{i\theta}|$ at the nontrivial $n$-th roots of unity,
and the polynomial of degree $n-2$ doing that is the Hermite interpolant. Its coefficients
$\Gamma_m$ and the positivity of the interpolation error are in §1; they prove the theorem for constant
diagonal.

## Where it got stuck

What remains is to extend $\Gamma_m$ off the diagonal to a positive semidefinite kernel for which (P)
holds. The first choice is the rank-one kernel $\kappa_m(s,t)=\sqrt{\Gamma_m(s)\Gamma_m(t)}$. It is
positive semidefinite for free and the constant term works automatically, so everything rests on (P),
which becomes a two-parameter family of trigonometric inequalities:
$$-\log\bigl|1-e^{-(p+q)/2}e^{i\theta}\bigr|\ \ge\ \tfrac12\bigl(\Gamma_0(p)+\Gamma_0(q)\bigr)+\sum_{m=1}^{n-2}\sqrt{\Gamma_m(p)\Gamma_m(q)}\,\cos m\theta .\tag{Star}$$
Numerically (Star) holds for every $n$ tested, but we did not find a proof. What we learned:

- The difference between the two sides is a cosine polynomial plus a Poisson tail. Its coefficient
  sequence is convex for $n\le15$, so the classical Fejér criterion proves (Star) there, and it stops
  being convex at $n=16$: the coefficients are a convex polynomial part minus a geometric part with a
  kink at index $0$. This agrees with the remark in the source that the inequality was known for $n\le15$.
- The gap is monotone in the smaller of the two parameters, so (Star) follows from a one-sided
  inequality (`HIn`), which has slack everywhere except on the diagonal.
- Multiplying that one-sided inequality by $\cosh\alpha-\cos\theta$, i.e. dividing by the Poisson kernel,
  removes the geometric part exactly and turns the statement into the convexity of an explicit sequence,
  with no angle variable (`QC`). Equivalently, a certain profile must be a positive mixture of shifted
  ideal profiles. Numerically this holds for all $n\le80$ tested.
- The obstruction is the square root. `QC` is a statement about ratios of hazard rates of the densities
  $k_m$; in one limiting regime it reduces to $5\zeta(5)\ge3\zeta(3)^2$. It is true for quantitative, not
  structural, reasons, and we did not prove it.

The reductions `QC n → HIn n → Star n → MainTheorem` are formalized in `Exploration/`; `QC n` remains open.

## What resolved it

The last reduction has a probabilistic reading. With $t=e^{-w}$, the normalized kernel
$\chi_m(w)=e^{mw}k_m(w)$ is a distribution function in $w$ (§1, K4). If $\tau$ is a random variable with
this distribution, then
$$m\,\Gamma_m(p)=\mathbb E\,e^{-m\max(p,\tau)} .$$
Seen this way, the diagonal coefficient is a mixture over $\tau$ of the functions $e^{-m\max(p,\tau)}$,
and there are two ways to split it into a kernel in $(p,q)$: take the square root outside the expectation
(the geometric mean, which led to (Star)), or inside:
$$m\,K_m(p,q)=\mathbb E\,e^{-m\max(p,\tau)/2}\,e^{-m\max(q,\tau)/2}.$$
The second is a mixture of rank-one kernels, hence positive semidefinite, and it has the same diagonal.
We had excluded kernels of this "minimum" type earlier because the simplest one gives the wrong constant
term in (P). The correct way to prove (P) for $K_m$ is to integrate the equal-radius inequality along a
path on which the interpolation radius moves from $p$ to $q$ at twice the speed of the integration
variable; then the constant term is exactly $\tfrac12(\Gamma_0(p)+\Gamma_0(q))$ and (P) needs no new
estimate at all (§3). The geometric mean, and with it (Star) and `QC`, is not needed.

## 1. The diagonal: an interpolation certificate

For $w>0$ and $0\le m\le n-2$ put
$$k_m(w)=\frac{\sinh((n-m)w)-(n-m)\sinh w}{\cosh nw-1},\qquad
\Gamma_m(p)=\int_p^\infty k_m(w)\,dw\ \ (m\ge1),\qquad
\Gamma_0(p)=\int_p^\infty\frac{k_0(w)-1}{2}\,dw .$$
($\Gamma_0+\sum_m\Gamma_m\cos m\theta$ is the cosine polynomial of degree $n-2$ that interpolates
$-\log|1-e^{-p}e^{i\theta}|$ to second order at the nontrivial $n$-th roots of unity; this is where the
formulas come from, but only the following four facts are used.)

**(K1) Positivity.** $k_m\ge0$, because $\sinh Nw\ge N\sinh w$.

**(K2) Kernel inequality.** Let $\Pi_w(\theta)=\tfrac12k_0(w)+\sum_{m=1}^{n-2}k_m(w)\cos m\theta$. Then
$$\tfrac12\mathcal P_w(\theta)-\Pi_w(\theta)=\tfrac12\,\rho_n(w)\,\mathrm{Fej}_n(\theta)\,\mathcal P_w(\theta)\ \ge0,\qquad\rho_n(w)=\frac{\cosh w-1}{\cosh nw-1}.$$
This is a finite trigonometric identity (the second difference of $m\mapsto k_m$ twisted by $\cosh w$ is
$2\rho_n\sinh w\,(n-m)$).

**(K3) Total identity.** $(n-1)\Gamma_0(p)-\sum_{m=1}^{n-2}\Gamma_m(p)=-\log F_n(e^{-p})$. (Evaluate (K2) at the
$n$-th roots of unity, where $\mathrm{Fej}_n$ vanishes, sum, and integrate in $w$.)

**(K4) Monotonicity.** $\chi_m(w):=e^{mw}k_m(w)$ is nondecreasing in $w$, with $\chi_m(0^+)=0$ and
$\chi_m\le1$. In fact, with $t=e^{-w}$ and $N=n-m$,
$$\chi_m(w)=\frac{1-t^{2N}-Nt^{N-1}(1-t^2)}{(1-t^n)^2}=\mathbb P\bigl(\tilde G_1+\tilde G_2+G_3\le N-2\bigr),$$
where $\tilde G_1,\tilde G_2$ are geometric with ratio $t$ conditioned on being $<n$ and $G_3$ is geometric
with ratio $t^2$; the Lean proof is a direct calculus argument. A consequence is the hazard bound
$k_m\le m\,\Gamma_m$.

Integrating (K2) over $w\in[p,\infty)$ gives the equal-radius inequality
$-\log|1-e^{-p}e^{i\theta}|\ge\Gamma_0(p)+\sum_m\Gamma_m(p)\cos m\theta$, which with (K3) already proves the
theorem when all diagonal entries are equal.

## 2. The off-diagonal kernel

For $0\le p\le q$ define
$$K_m(p,q)=\Gamma_m(q)+\frac12\int_p^qk_m(x)\,e^{-m(q-x)/2}\,dx\qquad(1\le m\le n-2),$$
and $K_m(q,p)=K_m(p,q)$. Clearly $K_m(p,p)=\Gamma_m(p)$.

**Lemma 1 (mixture representation).** For $p,q\ge0$,
$$K_m(p,q)=\frac1m\int_0^\infty\chi_m'(\tau)\;e^{-m\max(p,\tau)/2}\,e^{-m\max(q,\tau)/2}\,d\tau .$$

*Proof.* Take $p\le q$ and split the integral at $p$ and $q$. On $[0,p]$ it gives $\chi_m(p)e^{-m(p+q)/2}$.
Integrating by parts on $[p,q]$ and on $[q,\infty)$, the boundary terms $\chi_m(p)e^{-m(p+q)/2}$ and
$\chi_m(q)e^{-mq}$ cancel, and what remains is
$\tfrac m2e^{-mq/2}\int_p^q\chi_m(\tau)e^{-m\tau/2}d\tau+m\int_q^\infty\chi_m(\tau)e^{-m\tau}d\tau
=m\bigl[\tfrac12\int_p^qk_m(\tau)e^{-m(q-\tau)/2}d\tau+\Gamma_m(q)\bigr]$. $\square$

By (K4), $\chi_m'\ge0$. So $K_m$ is a nonnegative mixture of the rank-one kernels
$\phi_\tau(p)\phi_\tau(q)$, $\phi_\tau(p)=e^{-m\max(p,\tau)/2}$:

**Corollary 2 (positive semidefiniteness).** For $p_1,\dots,p_r\ge0$ and any Hermitian positive
semidefinite $M\in\mathbb C^{r\times r}$, $\ \sum_{i,j}K_m(p_i,p_j)\mathrm{Re}\,M_{ij}\ge0$.

(The integrand is $\chi_m'(\tau)\,\phi^{\mathsf T}M\phi\ge0$ with the real vector $\phi=(\phi_\tau(p_i))_i$.
In Lean the integral is truncated at a finite upper limit; the remainder is a nonnegative multiple of a
rank-one kernel by the hazard bound.)

In probabilistic terms: $\chi_m$ is the distribution function of a random level $\tau$, and
$m\,K_m(p,q)=\mathbb E\,e^{-m(\max(p,\tau)+\max(q,\tau))/2}$, while $m\,\Gamma_m(p)=\mathbb E\,e^{-m\max(p,\tau)}$.

## 3. The pair inequality

**Proposition 3.** For $0\le p\le q$, $\alpha=\frac{p+q}2$ and all $\theta$,
$$-\log\bigl|1-e^{-\alpha}e^{i\theta}\bigr|\ \ge\ \tfrac12\bigl(\Gamma_0(p)+\Gamma_0(q)\bigr)+\sum_{m=1}^{n-2}K_m(p,q)\cos m\theta .$$

*Proof.* The left side is $\int_\alpha^\infty\tfrac12(\mathcal P_w(\theta)-1)\,dw$. We bound the integrand
from below for each $w$.

- For $w\ge q$, (K2) gives $\tfrac12\mathcal P_w\ge\Pi_w$.
- For $\alpha\le w\le q$, put $x=2w-q\in[p,q]$ and $s=w-x=q-w\ge0$. Convolution with the Poisson kernel
  $\mathcal P_s$ preserves inequalities and multiplies the $m$-th cosine coefficient by $e^{-ms}$; since
  $\mathcal P_s*\mathcal P_x=\mathcal P_{x+s}=\mathcal P_w$, applying it to (K2) at $x$ gives
  $$\tfrac12\mathcal P_w(\theta)\ \ge\ \tfrac12k_0(x)+\sum_{m=1}^{n-2}k_m(x)\,e^{-m(q-w)}\cos m\theta .$$
  (Equivalently: the harmonic function whose boundary values are $\tfrac12\mathcal P_x-\Pi_x\ge0$ is
  nonnegative on the smaller circle of radius $e^{-s}$.)

Integrate. The part $w\ge q$ contributes $\Gamma_0(q)+\sum_m\Gamma_m(q)\cos m\theta$. In the part
$\alpha\le w\le q$ substitute $x=2w-q$, $dw=\tfrac12dx$:
$$\frac12\int_p^q\Bigl[\frac{k_0(x)-1}{2}+\sum_mk_m(x)e^{-m(q-x)/2}\cos m\theta\Bigr]dx
=\tfrac12\bigl(\Gamma_0(p)-\Gamma_0(q)\bigr)+\sum_m\Bigl[\tfrac12\!\int_p^q\!k_m(x)e^{-m(q-x)/2}dx\Bigr]\cos m\theta .$$
Adding the two parts gives the claim; the constant term is exactly $\tfrac12(\Gamma_0(p)+\Gamma_0(q))$. $\square$

The path $x=2w-q$ is what makes the constant come out right: the "interpolation radius" $x$ runs from $p$
to $q$ at twice the speed of $w$, so each of $p$ and $q$ is charged half of $\Gamma_0$. The gap in
Proposition 3 is explicitly
$$\tfrac12\mathrm{Fej}_n(\theta)\int_q^\infty\rho_n\mathcal P_w(\theta)\,dw+\tfrac14\int_p^q\bigl(\mathcal P_{(q-x)/2}*\rho_n(x)\mathrm{Fej}_n\mathcal P_x\bigr)(\theta)\,dx\ \ge0 .$$

(The Lean proof of Proposition 3 is organised as monotonicity in $p$: the gap is nonincreasing in
$p\in[0,q]$, its $p$-derivative being minus the smoothed form of (K2), and it is nonnegative at $p=q$.)

## 4. Assembly

First suppose $0<d_i\le1$ for all $i$ and write $d_i=e^{-p_i}$, $\alpha_{ij}=\frac{p_i+p_j}2$,
$a_{ij}=e^{-\alpha_{ij}}c_{ij}$. For fixed $i\ne j$ the function
$$c\ \mapsto\ -\log|1-e^{-\alpha_{ij}}c|-\tfrac12\bigl(\Gamma_0(p_i)+\Gamma_0(p_j)\bigr)-\sum_mK_m(p_i,p_j)\mathrm{Re}\,c^m$$
is harmonic near the closed unit disc (if $a_{ij}=1$ there is nothing to prove) and nonnegative on the unit
circle by Proposition 3, hence nonnegative at $c=c_{ij}$. Summing over $i\ne j$:
$$\sum_{i\ne j}-\log|1-a_{ij}|\ \ge\ (n-1)\sum_i\Gamma_0(p_i)+\sum_{m=1}^{n-2}\Bigl[\sum_{i,j}K_m(p_i,p_j)\mathrm{Re}\,c_{ij}^{\,m}-\sum_i\Gamma_m(p_i)\Bigr].$$
The entrywise power $C^{\circ m}$ is positive semidefinite (Schur product theorem), so the double sum is
nonnegative by Corollary 2. With (K3),
$$\sum_{i\ne j}-\log|1-a_{ij}|\ \ge\ \sum_i\Bigl[(n-1)\Gamma_0(p_i)-\sum_m\Gamma_m(p_i)\Bigr]=-\sum_i\log F_n(d_i),$$
which is (R).

**Arbitrary diagonal values.** For $s>0$ put $\gamma_0(s)=\Gamma_0(|\log s|)-\max(\log s,0)$,
$\gamma_m(s)=\Gamma_m(|\log s|)$, $\kappa_m(s,t)=K_m(|\log s|,|\log t|)$; then
$(n-1)\gamma_0(s)-\sum_m\gamma_m(s)=-\log F_n(s)$ still holds because $F_n(s)=s^{n-1}F_n(1/s)$. The pair
inequality (P) for $s,t>0$ follows from Proposition 3 and the elementary bound
$|1-Kc\,z|\le K\,|1-(c/K)z|$ for $K\ge1$, $0\le c\le1$, $|z|=1$. Rows with $d_i=0$ are zero rows and
contribute nothing; if some $a_{ij}=1$ the left side of (R) is $0$. The cases $n\le1$ are trivial and
$n=2$ is $|a_{12}|^2\le d_1d_2$.

## 5. Lean

The final statement is `MatrixIneq.mainTheorem : Statement.MainTheorem` in `MatrixIneq/Main.lean`.
(K1) is `kern_nonneg`; (K2) is `kern_poisson_le`; (K3) is `total_Gam`; (K4) is `chi_mono`, with the hazard
bound `kern_le_mul_Gam`. Lemma 1 is `tauK_repr`, Corollary 2 is `tauK_psd`, Proposition 3 is `tauStar`
(its smoothing step is `kern_poisson_smooth_le`). The assembly is `reducedAt_of_kcertificate`,
`tauCertificate` and `reducedAt_all`.

## 6. Remarks

- Equality holds for $a_{ij}=d\,\omega^{i-j}$, $\omega=e^{2\pi i/n}$: all inequalities above are equalities
  when the $p_i$ are equal and the $c_{ij}$ run through the $n$-th roots of unity.
- The kernel $K_m$ is not the geometric mean $\sqrt{\Gamma_m(p)\Gamma_m(q)}$ (it is smaller). The inequality
  with the geometric mean in place of $K_m$ appears to be true as well, but we did not prove it; see
  `worklog/` and the Lean library `Exploration/` for what is known about it.
- For $n\le15$ the classical Fejér convexity criterion suffices for several of the intermediate
  statements we tried, and it fails from $n=16$ on; this matches the remark in the source that the
  inequality was known for $n\le15$. The proof above has no such threshold.
