import Statement

/-!
# Step 1: reduction to the off-diagonal form

Since `|1 - a ^ n| = |1 - a| * (1 + a + ⋯ + a ^ (n-1))` for real `a ≥ 0`, the diagonal factors cancel and the
main theorem follows from the reduced form `ReducedAt n`:

  `∏_{i ≠ j} |1 - a_ij| ≤ ∏_i (1 + a_ii + ⋯ + a_ii ^ (n-1))`

(`main_of_reducedAt`, `mainTheorem_of_reduced`).
-/

open scoped ComplexOrder
open Finset

namespace MatrixIneq

/-- **Reduced form for size `n`.** For positive semidefinite `A`,
`∏_{i ≠ j} |1 - a_ij| ≤ ∏_i (1 + a_ii + ⋯ + a_ii ^ (n-1))`. -/
def ReducedAt (n : ℕ) : Prop :=
  ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef →
    ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ ≤ ∏ i, ∑ k ∈ range n, (A i i).re ^ k

/-- **Reduced form**, for all sizes. -/
def Reduced : Prop := ∀ n, ReducedAt n

/-- For real `r ≥ 0`: `|1 - r ^ n| = |1 - r| * (1 + r + ⋯ + r ^ (n-1))`. -/
theorem norm_one_sub_pow (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ‖1 - (r : ℂ) ^ n‖ = ‖1 - (r : ℂ)‖ * ∑ k ∈ range n, r ^ k := by
  have h : (1 - (r : ℂ) ^ n) = (1 - (r : ℂ)) * ((∑ k ∈ range n, r ^ k : ℝ) : ℂ) := by
    push_cast
    exact (mul_neg_geom_sum (r : ℂ) n).symm
  rw [h, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sum_nonneg fun k _ => pow_nonneg hr k)]

/-- The diagonal of a positive semidefinite complex matrix is real and nonnegative. -/
theorem diag_eq_re {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (i : Fin n) :
    0 ≤ (A i i).re ∧ A i i = ((A i i).re : ℂ) := by
  have h := hA.diag_nonneg (i := i)
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp h
  exact ⟨h1, Complex.ext rfl (by simpa using h2.symm)⟩

/-- For each size `n`, the main inequality follows from the reduced form for that `n`. -/
theorem main_of_reducedAt {n : ℕ} (h : ReducedAt n) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖ := by
  have hL : ∏ i, ∏ j, ‖1 - A i j‖ = (∏ i, ‖1 - A i i‖) * ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => (mul_prod_erase univ (fun j => ‖1 - A i j‖) (mem_univ i)).symm
  have hR : ∏ i, ‖1 - A i i ^ n‖ = (∏ i, ‖1 - A i i‖) * ∏ i, ∑ k ∈ range n, (A i i).re ^ k := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    obtain ⟨h0, he⟩ := diag_eq_re hA i
    rw [he, norm_one_sub_pow _ h0, Complex.ofReal_re]
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (h A hA) (prod_nonneg fun i _ => norm_nonneg _)

/-- The main theorem follows from the reduced form. -/
theorem mainTheorem_of_reduced (h : Reduced) : Statement.MainTheorem :=
  fun n A hA => main_of_reducedAt (h n) A hA

end MatrixIneq
