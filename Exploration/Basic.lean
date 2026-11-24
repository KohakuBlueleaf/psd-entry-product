import MatrixIneq.Basic

/-!
# Further facts on positive semidefinite matrices

Sum of entries of entrywise powers; enlarging the diagonal.
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- `∑_{i,j} a_ij ^ k ≥ 0`. -/
theorem sum_pow_nonneg_one (hA : A.PosSemidef) (k : ℕ) : 0 ≤ ∑ i, ∑ j, A i j ^ k := by
  simpa using sum_pow_nonneg hA k fun _ => 1

/-- Enlarging the diagonal keeps positive semidefiniteness. -/
theorem posSemidef_add_diagonal (hA : A.PosSemidef) {d : Fin n → ℂ} (hd : 0 ≤ d) :
    (A + diagonal d).PosSemidef :=
  hA.add (PosSemidef.diagonal hd)

theorem add_diagonal_apply_ne (d : Fin n → ℂ) {i j : Fin n} (h : i ≠ j) :
    (A + diagonal d) i j = A i j := by
  simp [diagonal_apply_ne _ h]


end MatrixIneq
