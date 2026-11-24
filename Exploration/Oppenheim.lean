import Exploration.Basic

/-!
# Oppenheim's inequality

For positive semidefinite `A`, `B`:  `det A * ∏ i, B i i ≤ det (A ⊙ B)`.

This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

theorem eq_re_of_nonneg {z : ℂ} (h : 0 ≤ z) : 0 ≤ z.re ∧ z = (z.re : ℂ) := by
  obtain ⟨h1, h2⟩ := Complex.nonneg_iff.mp h
  exact ⟨h1, Complex.ext rfl (by simpa using h2.symm)⟩

/-- Cauchy–Schwarz for a positive semidefinite form. -/
theorem cauchy_schwarz {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (y x : Fin n → ℂ) :
    ‖star y ⬝ᵥ (A *ᵥ x)‖ ^ 2 ≤ (star y ⬝ᵥ (A *ᵥ y)).re * (star x ⬝ᵥ (A *ᵥ x)).re := by
  let B : Matrix (Fin n) (Fin 2) ℂ := of fun i k => ![y i, x i] k
  have hG : (Bᴴ * A * B).PosSemidef := hA.conjTranspose_mul_mul_same B
  have key : ∀ k l : Fin 2, (Bᴴ * A * B) k l = star (fun i => B i k) ⬝ᵥ (A *ᵥ fun i => B i l) := by
    intro k l
    rw [Matrix.mul_assoc]
    simp [Matrix.mul_apply, dotProduct, mulVec]
  have h := norm_sq_le hG 0 1
  rw [key 0 1, key 0 0, key 1 1] at h
  simpa [B] using h

/-- For positive definite `A`, with `q = (A⁻¹)₀₀`:  `|x₀|² ≤ q · x*Ax`. -/
theorem norm_sq_apply_zero_le {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.PosDef)
    (x : Fin (n + 1) → ℂ) :
    ‖x 0‖ ^ 2 ≤ (A⁻¹ 0 0).re * (star x ⬝ᵥ (A *ᵥ x)).re := by
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
  set y : Fin (n + 1) → ℂ := A⁻¹ *ᵥ Pi.single 0 1 with hy
  have hAy : A *ᵥ y = Pi.single 0 1 := by
    rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have h1 : star y ⬝ᵥ (A *ᵥ x) = x 0 := by
    rw [dotProduct_mulVec, ← hA.isHermitian.eq, ← star_mulVec, hAy]
    simp
  have h2 : star y ⬝ᵥ (A *ᵥ y) = star (A⁻¹ 0 0) := by
    rw [hAy]; simp [hy, dotProduct, Pi.single_apply]
  have h := cauchy_schwarz hA.posSemidef y x
  rw [h1, h2] at h
  simpa using h

section succ

variable {n : ℕ}

/-- The matrix unit `E₀₀`. -/
def E (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.single 0 0 1

theorem E_apply (i j : Fin (n + 1)) : E n i j = if i = 0 ∧ j = 0 then 1 else 0 := by
  simp [E, single_apply, eq_comm]

theorem inv_apply_zero_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    A⁻¹ 0 0 = A.det⁻¹ * (A.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_succ_eq_det_submatrix]
  simp [Ring.inverse_eq_inv']

/-- `det (N - s E₀₀) = det N - s det N'`, where `N'` deletes row and column `0`. -/
theorem det_sub_single (N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    (N - s • E n).det = N.det - s * (N.submatrix Fin.succ Fin.succ).det := by
  have hsub : ∀ j : Fin (n + 1), (N - s • E n).submatrix Fin.succ j.succAbove
      = N.submatrix Fin.succ j.succAbove := by
    intro j; ext a b
    simp [E_apply, Fin.succ_ne_zero]
  rw [det_succ_row_zero, det_succ_row_zero N]
  simp only [hsub]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hz : ∀ j : Fin n, (N - s • E n : Matrix _ _ ℂ) 0 j.succ = N 0 j.succ := by
    intro j
    simp [E_apply, Fin.succ_ne_zero]
  have h0 : (N - s • E n : Matrix _ _ ℂ) 0 0 = N 0 0 - s := by
    simp [E_apply]
  simp only [hz, h0]
  simp
  ring

/-- For positive definite `A` and `t = 1 / (A⁻¹)₀₀`, the matrix `A - t E₀₀` is positive semidefinite. -/
theorem posSemidef_sub_single {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hA : A.PosDef) :
    (A - (((A⁻¹ 0 0).re⁻¹ : ℝ) : ℂ) • E n).PosSemidef := by
  have hq : 0 < (A⁻¹ 0 0).re := (Complex.pos_iff.mp (hA.inv.diag_pos (i := 0))).1
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun x => ?_⟩
  · ext i j
    have := hA.isHermitian.apply i j
    simp only [conjTranspose_apply, Matrix.sub_apply, Matrix.smul_apply, E_apply, smul_eq_mul, star_sub, this]
    by_cases h : i = 0 ∧ j = 0
    · simp [h]
    · have h' : ¬(j = 0 ∧ i = 0) := fun h' => h h'.symm
      simp [h, h']
  · have hE : (E n) *ᵥ x = Pi.single 0 (x 0) := by
      ext i; by_cases hi : i = 0 <;> simp [mulVec, dotProduct, E_apply, hi]
    obtain ⟨hr, he⟩ := eq_re_of_nonneg (hA.posSemidef.dotProduct_mulVec_nonneg x)
    have hb := norm_sq_apply_zero_le hA x
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, hE, he]
    have hx : star x ⬝ᵥ ((((A⁻¹ 0 0).re⁻¹ : ℝ) : ℂ) • Pi.single 0 (x 0))
        = (((A⁻¹ 0 0).re⁻¹ * ‖x 0‖ ^ 2 : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Pi.star_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [mul_left_comm, Complex.star_def, Complex.conj_mul']
      push_cast; ring
    rw [hx, ← Complex.ofReal_sub, Complex.zero_le_real, sub_nonneg, inv_mul_le_iff₀ hq]
    exact hb

end succ

/-- **Oppenheim's inequality.** `det A * ∏ i, B i i ≤ det (A ⊙ B)` for positive semidefinite `A`, `B`. -/
theorem oppenheim : ∀ {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}, A.PosSemidef → B.PosSemidef →
    A.det * ∏ i, B i i ≤ (A ⊙ B).det := by
  intro n
  induction n with
  | zero => intro A B _ _; simp
  | succ n ih =>
    intro A B hA hB
    by_cases hdet : A.det = 0
    · rw [hdet, zero_mul]; exact (hA.hadamard hB).det_nonneg
    have hPD : A.PosDef := hA.posDef_iff_det_ne_zero.mpr hdet
    set A' := A.submatrix Fin.succ Fin.succ with hA'
    set B' := B.submatrix Fin.succ Fin.succ with hB'
    have hA'PD : A'.PosDef := hPD.submatrix (Fin.succ_injective n)
    have hih := ih hA'PD.posSemidef (hB.submatrix Fin.succ)
    obtain ⟨hq0, hqe⟩ := eq_re_of_nonneg (hPD.inv.diag_pos (i := 0)).le
    set q := (A⁻¹ 0 0).re with hqdef
    have hq : 0 < q := (Complex.pos_iff.mp (hPD.inv.diag_pos (i := 0))).1
    -- `t * det A' = det A`
    have ht : ((q⁻¹ : ℝ) : ℂ) * A'.det = A.det := by
      have h1 : (q : ℂ) = A.det⁻¹ * A'.det := by rw [← hqe, inv_apply_zero_zero]
      have hqne : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
      rw [Complex.ofReal_inv, h1]
      have hA'ne : A'.det ≠ 0 := hA'PD.det_pos.ne'
      field_simp
    have hM := (posSemidef_sub_single hPD).hadamard hB
    have hMeq : (A - ((q⁻¹ : ℝ) : ℂ) • E n) ⊙ B
        = A ⊙ B - (((q⁻¹ : ℝ) : ℂ) * B 0 0) • E n := by
      ext i j
      simp only [hadamard_apply, Matrix.sub_apply, Matrix.smul_apply, E_apply, smul_eq_mul]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h; ring
      · ring
    have hdetM := hM.det_nonneg
    rw [hMeq, det_sub_single] at hdetM
    have hsubm : (A ⊙ B).submatrix Fin.succ Fin.succ = A' ⊙ B' := rfl
    rw [hsubm, sub_nonneg] at hdetM
    have hc : (0 : ℂ) ≤ ((q⁻¹ : ℝ) : ℂ) * B 0 0 :=
      mul_nonneg (Complex.zero_le_real.mpr (inv_nonneg.mpr hq.le)) hB.diag_nonneg
    calc A.det * ∏ i, B i i
        = (((q⁻¹ : ℝ) : ℂ) * B 0 0) * (A'.det * ∏ i, B' i i) := by
          rw [Fin.prod_univ_succ, ← ht]; simp only [hB', submatrix_apply]; ring
      _ ≤ (((q⁻¹ : ℝ) : ℂ) * B 0 0) * (A' ⊙ B').det := mul_le_mul_of_nonneg_left hih hc
      _ ≤ (A ⊙ B).det := hdetM

end MatrixIneq
