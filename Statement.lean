import Mathlib

/-!
# An entrywise product inequality for positive semidefinite matrices

Let `A = (a_ij) ∈ ℂ^{n×n}` be positive semidefinite. Then

  `∏_{i,j=1}^{n} |1 - a_ij|  ≤  ∏_{i=1}^{n} |1 - a_ii ^ n|`.

This file contains the statement only, using Mathlib only. See `docs/PROBLEM.md` for the source and the
known facts.

Reading guide, for checking the statement against the problem:

* `Matrix (Fin n) (Fin n) ℂ` is `ℂ^{n×n}`, and `A i j` is the entry `a_ij`.
* `A.PosSemidef` is Mathlib's `Matrix.PosSemidef`: `A` is Hermitian and `x* A x ≥ 0` for every
  `x ∈ ℂⁿ`. The order on `ℂ` is the one of `ComplexOrder` (`z ≤ w` iff `z.re ≤ w.re` and
  `z.im = w.im`), so `0 ≤ z` says that `z` is real and nonnegative.
* `‖z‖` for `z : ℂ` is the modulus `|z|`, a real number; both sides of the inequality are real.
* `∏ i, ∏ j, _` runs over all `n²` ordered pairs `(i, j)`, the diagonal ones included.
* `A i i ^ n` is the `n`-th power (`n : ℕ`, the size of the matrix) of the diagonal entry `a_ii`.
* `n = 0` is allowed and says `1 ≤ 1`.
-/

open scoped ComplexOrder

namespace Statement

/-- **Main theorem.** For every positive semidefinite `A = (a_ij) ∈ ℂ^{n×n}`,
`∏_{i,j} |1 - a_ij| ≤ ∏_i |1 - a_ii ^ n|`. -/
def MainTheorem : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖

end Statement
