import MatrixIneq.Reduced

/-!
# Basic facts about positive semidefinite complex matrices

* `apply_conj`, `norm_sq_le`: `a_ji = conj a_ij` and `|a_ij|² ≤ a_ii a_jj`.
* `posSemidef_map_pow`, `sum_pow_nonneg`: entrywise powers are positive semidefinite (Schur product theorem),
  hence `∑_{i,j} conj(w_i) a_ij ^ k w_j ≥ 0`. This is the positivity input of the certificate method.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

theorem apply_conj (hA : A.PosSemidef) (i j : Fin n) : A j i = star (A i j) :=
  (hA.1.apply j i).symm

/-- `|a_ij|² ≤ a_ii a_jj`. -/
theorem norm_sq_le (hA : A.PosSemidef) (i j : Fin n) :
    ‖A i j‖ ^ 2 ≤ (A i i).re * (A j j).re := by
  have hB := (hA.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at hB
  simp only [submatrix_apply, cons_val_zero, cons_val_one] at hB
  rw [apply_conj hA i j] at hB
  have h := (Complex.nonneg_iff.mp hB).1
  obtain ⟨-, hi⟩ := diag_eq_re hA i
  obtain ⟨-, hj⟩ := diag_eq_re hA j
  rw [hi, hj] at h
  have hn : (A i j * star (A i j)).re = ‖A i j‖ ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [Complex.sub_re, hn, ← Complex.ofReal_mul, Complex.ofReal_re] at h
  linarith

/-- **Schur.** Entrywise powers of a positive semidefinite matrix are positive semidefinite. -/
theorem posSemidef_map_pow (hA : A.PosSemidef) (k : ℕ) : (A.map (· ^ k)).PosSemidef := by
  induction k with
  | zero =>
    have h : A.map (· ^ 0) = vecMulVec (fun _ => (1 : ℂ)) (star fun _ => (1 : ℂ)) := by
      ext i j; simp [vecMulVec_apply]
    rw [h]; exact posSemidef_vecMulVec_self_star _
  | succ k ih =>
    have h : A.map (· ^ (k + 1)) = A.map (· ^ k) ⊙ A := by
      ext i j; simp [pow_succ]
    rw [h]; exact ih.hadamard hA

/-- `∑_{i,j} conj(w_i) a_ij ^ k w_j ≥ 0`. -/
theorem sum_pow_nonneg (hA : A.PosSemidef) (k : ℕ) (w : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, star (w i) * A i j ^ k * w j := by
  have h := (posSemidef_map_pow hA k).dotProduct_mulVec_nonneg w
  simpa [dotProduct, mulVec, mul_sum, mul_assoc] using h


end MatrixIneq
