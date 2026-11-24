import MatrixIneq.Small

/-!
# The reduced form for `n = 2`
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

/-- `n = 2`: `|1 - b|² ≤ (1 + √(ac))² ≤ (1 + a)(1 + c)`. -/
theorem reducedAt_two : ReducedAt 2 := by
  intro A hA
  obtain ⟨ha, -⟩ := diag_eq_re hA 0
  obtain ⟨hc, -⟩ := diag_eq_re hA 1
  have hb := norm_sq_le hA 0 1
  have h10 : ‖1 - A 1 0‖ = ‖1 - A 0 1‖ := by
    rw [apply_conj hA 0 1, ← norm_star (1 - A 0 1), star_sub, star_one]
  have hL : ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ = ‖1 - A 0 1‖ ^ 2 := by
    have e0 : (univ : Finset (Fin 2)).erase 0 = {1} := by decide
    have e1 : (univ : Finset (Fin 2)).erase 1 = {0} := by decide
    rw [Fin.prod_univ_two, e0, e1, prod_singleton, prod_singleton, h10, sq]
  have hR : ∏ i : Fin 2, ∑ k ∈ range 2, (A i i).re ^ k = (1 + (A 0 0).re) * (1 + (A 1 1).re) := by
    simp [Fin.prod_univ_two, sum_range_succ]
  rw [hL, hR]
  have h1 : ‖1 - A 0 1‖ ≤ 1 + ‖A 0 1‖ := by
    simpa using norm_sub_le (1 : ℂ) (A 0 1)
  have hn := norm_nonneg (A 0 1)
  have h2 : 2 * ‖A 0 1‖ ≤ (A 0 0).re + (A 1 1).re := by
    nlinarith [sq_nonneg ((A 0 0).re - (A 1 1).re)]
  calc ‖1 - A 0 1‖ ^ 2 ≤ (1 + ‖A 0 1‖) ^ 2 := by gcongr
    _ ≤ (1 + (A 0 0).re) * (1 + (A 1 1).re) := by nlinarith


end MatrixIneq
