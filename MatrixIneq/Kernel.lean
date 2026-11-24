import MatrixIneq.Harmonic

/-!
# The kernels `k_m`

  `kern n m w = (sinh ((n - m) w) - (n - m) sinh w) / (cosh (n w) - 1)`,   `0 ≤ m ≤ n - 2`.

The certificate coefficients are tail integrals of these kernels (`MatrixIneq/Coefficients.lean`).
This file proves `kern_nonneg` (from `N sinh w ≤ sinh (N w)`).
-/

namespace MatrixIneq

open Real

/-- `sinh (N w) ≥ N sinh w` for `w ≥ 0`. -/
theorem nat_mul_sinh_le_sinh_nat_mul (N : ℕ) {w : ℝ} (hw : 0 ≤ w) : N * sinh w ≤ sinh (N * w) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs : 0 ≤ sinh w := sinh_nonneg_iff.mpr hw
    have hNs : 0 ≤ sinh (N * w) := sinh_nonneg_iff.mpr (by positivity)
    have h1 : (1 : ℝ) ≤ cosh w := one_le_cosh w
    have h2 : (1 : ℝ) ≤ cosh (N * w) := one_le_cosh _
    have e : sinh ((N + 1 : ℕ) * w) = sinh (N * w) * cosh w + cosh (N * w) * sinh w := by
      rw [← sinh_add]; push_cast; ring_nf
    rw [e]; push_cast
    nlinarith

/-- The kernel of the `m`-th coefficient of the Fejér certificate for size `n`. -/
noncomputable def kern (n m : ℕ) (w : ℝ) : ℝ :=
  (sinh ((n - m : ℕ) * w) - (n - m : ℕ) * sinh w) / (cosh (n * w) - 1)

theorem kern_nonneg (n m : ℕ) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ kern n m w := by
  unfold kern
  exact div_nonneg (sub_nonneg.mpr (nat_mul_sinh_le_sinh_nat_mul _ hw)) (sub_nonneg.mpr (one_le_cosh _))

/-- The kernel vanishes for `m = n - 1`, so the certificate has degree at most `n - 2`. -/
theorem kern_pred (n : ℕ) (hn : 1 ≤ n) (w : ℝ) : kern n (n - 1) w = 0 := by
  unfold kern
  have : n - (n - 1) = 1 := by omega
  simp [this]

end MatrixIneq
