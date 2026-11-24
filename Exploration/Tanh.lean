import MatrixIneq.Reduced

/-!
# Subadditivity of `tanh`

This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open Real

namespace MatrixIneq

/-! ### `tanh` is subadditive on `[0, ∞)` -/

theorem tanh_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : tanh (a + b) ≤ tanh a + tanh b := by
  have hsa : 0 ≤ sinh a := sinh_nonneg_iff.mpr ha
  have hsb : 0 ≤ sinh b := sinh_nonneg_iff.mpr hb
  have hs : 0 ≤ sinh (a + b) := sinh_nonneg_iff.mpr (add_nonneg ha hb)
  have hca := cosh_pos a
  have hcb := cosh_pos b
  have hc : cosh a * cosh b ≤ cosh (a + b) := by
    rw [cosh_add]; nlinarith [mul_nonneg hsa hsb]
  rw [tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh, tanh_eq_sinh_div_cosh]
  calc sinh (a + b) / cosh (a + b) ≤ sinh (a + b) / (cosh a * cosh b) :=
        div_le_div_of_nonneg_left hs (mul_pos hca hcb) hc
    _ = sinh a / cosh a + sinh b / cosh b := by
        rw [sinh_add]; field_simp

/-- `tanh (N x) ≤ N tanh x` for `x ≥ 0`. -/
theorem nat_mul_tanh_ge (N : ℕ) {x : ℝ} (hx : 0 ≤ x) : tanh (N * x) ≤ N * tanh x := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : ((N + 1 : ℕ) : ℝ) * x = N * x + x := by push_cast; ring
    rw [e]
    have h := tanh_add_le (a := N * x) (b := x) (by positivity) hx
    push_cast
    linarith


end MatrixIneq
