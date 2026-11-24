# An entrywise product inequality for positive semidefinite matrices

## Problem

Let $A = (a_{ij}) \in \mathbb{C}^{n \times n}$ be a positive semidefinite matrix. Prove that

$$\prod_{i,j=1}^{n} \lvert 1 - a_{ij} \rvert \;\le\; \prod_{i=1}^{n} \lvert 1 - a_{ii}^{\,n} \rvert .$$

Conventions:

- Positive semidefinite means Hermitian ($a_{ji} = \overline{a_{ij}}$) with $x^* A x \ge 0$ for every
  $x \in \mathbb{C}^n$.
- The left product runs over all $n^2$ ordered pairs $(i, j)$, the diagonal ones included.
- On the right, $a_{ii}^{\,n}$ is the $n$-th power of the diagonal entry, where $n$ is the size of the matrix.
- $\lvert \cdot \rvert$ is the complex modulus.

The formal statement is `Statement.MainTheorem` in [`Statement.lean`](../Statement.lean).

**Status: proved.** `MatrixIneq.mainTheorem : Statement.MainTheorem` (Lean 4, no `sorry`, standard axioms only).
The written proof is in [`PROOF.md`](PROOF.md).

## Source

A post on Baidu Tieba, 数学吧, by user Haaruhi, titled
"求助喵（一道数分高代，astra几个小时做不出来！？". Screenshot: [`og-desc.png`](og-desc.png).

Original text:

> 这是一名群u想到的一个经典（？）结论的推广
>
> 在埋头做题之前，建议阅读下下面的内容：
>
> 1. 这个题目并不简单，很多人用各种ai（包括但不限于astra）蹬了几小时也没做出来，如果时间不充裕的话不建议投入太多时间。
> 2. 一些已知的结论：这个不等式在实矩阵、秩一矩阵或是阶小于等于15的时候都成立，可以直接告诉ai避免重复造轮子。
>
> 祝你好运！
>
> 设 $A = (a_{ij}) \in \mathbb{C}^{n\times n}$ 为半正定矩阵，证明
> $\prod_{i,j=1}^{n} |1 - a_{ij}| \le \prod_{i=1}^{n} |1 - a_{ii}^n|$.

Translation:

> This is a generalization, thought up by a member of a chat group, of a classical (?) result.
>
> Before diving in, please read the following:
>
> 1. This problem is not easy. Many people have spent hours on it with various AIs (including but not limited
>    to astra) without solving it. If you are short on time, investing a lot of it here is not recommended.
> 2. Some known results: the inequality holds for real matrices, for rank-one matrices, and for order at most
>    15. You can tell the AI this directly to avoid reinventing the wheel.
>
> Good luck!

The post does not say which classical result is being generalized.

## Known facts

### Stated in the post

The post gives these without proofs or references, and they have not been re-proved here.

1. **Real case.** The inequality holds when $A$ is real (real symmetric positive semidefinite).
2. **Rank-one case.** The inequality holds when $\operatorname{rank} A = 1$, i.e. $a_{ij} = x_i \overline{x_j}$
   for some $x \in \mathbb{C}^n$.
3. **Small order.** The inequality holds for all $n \le 15$.
4. **Difficulty.** Many attempts with AI tools, hours long, have failed.

### Added by the project owner

5. **This is a solved problem.** A proof was said to exist; the problem is difficult, not open. The goal here
   was to find and formalize a proof, not to decide whether the statement is true.
6. **Unconfirmed hint.** The proof reportedly uses modern mathematical tools. This is hearsay. The proof
   found here uses the Schur product theorem, the Poisson kernel, the minimum principle for harmonic
   functions and a linear-programming certificate with radius-dependent coefficients; we do not know
   whether it coincides with the proof the post alludes to.

### Checked while writing the statement

These are small observations made here, not from the post.

- **The diagonal is real.** For positive semidefinite $A$ every $a_{ii}$ is real and nonnegative, so the right
  side is $\prod_i \lvert 1 - a_{ii}^{\,n} \rvert$ with $a_{ii} \ge 0$. If some $a_{ii} = 1$ both sides are $0$.
- **Trivial sizes.** For $n = 1$ the two sides are equal. For $n = 0$ both are empty products, $1 \le 1$.
- **The bound is tight.** Let $\omega = e^{2\pi i / n}$, $r \ge 0$, and $a_{ij} = r^2 \omega^{\,i-j}$ (rank one,
  $x_i = r\omega^i$). Each row of $A$ runs through $r^2\omega^k$ for all $k$, and
  $\prod_{k=0}^{n-1} (1 - r^2\omega^k) = 1 - r^{2n}$, so both sides equal $\lvert 1 - r^{2n} \rvert^{\,n}$.
  The exponent $n$ on the right is therefore exactly what the rank-one case forces.
- **Positive semidefiniteness is needed.** For the Hermitian matrix
  $\begin{pmatrix} 0 & 3 \\ 3 & 0 \end{pmatrix}$ the left side is $4$ and the right side is $1$.
- **Numerical test.** 280,000 random complex positive semidefinite matrices with $1 \le n \le 7$, of random
  rank and scale, gave no violation. Dropping the power on the right
  ($\prod_i \lvert 1 - a_{ii} \rvert$) fails often, which confirms the reading of the formula in the screenshot.

## Formal statement

```lean
open scoped ComplexOrder

def Statement.MainTheorem : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖
```

| Problem | Lean |
| --- | --- |
| $A = (a_{ij}) \in \mathbb{C}^{n\times n}$ | `A : Matrix (Fin n) (Fin n) ℂ`, entry `A i j` |
| $A$ positive semidefinite | `A.PosSemidef` (Mathlib's `Matrix.PosSemidef`) |
| $\lvert z \rvert$ | `‖z‖` |
| $\prod_{i,j=1}^{n}$ | `∏ i, ∏ j` over `Fin n` |
| $a_{ii}^{\,n}$ | `A i i ^ n` |

The statement allows $n = 0$, which the problem presumably does not intend; that case is trivially true, so
nothing is gained or lost.

The project uses Lean `v4.36.0` and Mathlib `v4.36.0`. Build with `lake build`.
