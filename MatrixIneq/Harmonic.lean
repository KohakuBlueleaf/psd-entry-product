import MatrixIneq.Basic

/-!
# Harmonic sums, the maximum principle, and normalised entries

Shared tools of the certificate method.

* `harm κ b D z = κ + ∑_{m=1}^{D} b m · Re (z ^ m)`.
* `disc_of_circle`: an inequality `|1 - τ z| ≤ exp (- harm z)` on the unit circle holds on the closed unit disc
  (maximum modulus principle).
* `nz A i j = a_ij / √(a_ii a_jj)`, with `eq_sqrt_mul_nz`, `norm_nz_le`.
* `sum_sqrt_mul_nz_pow_nonneg`: Schur positivity in normalised form,
  `0 ≤ ∑_{i,j} φ_i φ_j Re (nz A i j ^ m)` for real weights `φ` vanishing where `a_ii = 0`.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

/-- `κ + ∑_{m=1}^{D} b m · Re (z ^ m)`. -/
noncomputable def harm (κ : ℝ) (b : ℕ → ℝ) (D : ℕ) (z : ℂ) : ℝ :=
  κ + ∑ m ∈ Icc 1 D, b m * (z ^ m).re

/-- Maximum modulus: an inequality `|1 - τ z| ≤ exp (- harm z)` on the unit circle holds on the closed disc. -/
theorem disc_of_circle (τ κ : ℝ) (b : ℕ → ℝ) (D : ℕ)
    (h : ∀ z : ℂ, ‖z‖ = 1 → ‖1 - (τ : ℂ) * z‖ ≤ Real.exp (-(harm κ b D z)))
    (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖1 - (τ : ℂ) * z‖ ≤ Real.exp (-(harm κ b D z)) := by
  set Q : ℂ → ℂ := fun w => (κ : ℂ) + ∑ m ∈ Icc 1 D, (b m : ℂ) * w ^ m with hQ
  have hQre : ∀ w, (Q w).re = harm κ b D w := by
    intro w
    simp only [hQ, harm, Complex.add_re, Complex.ofReal_re, Complex.re_sum, Complex.re_ofReal_mul]
  set f : ℂ → ℂ := fun w => (1 - (τ : ℂ) * w) * Complex.exp (Q w) with hf
  have hnorm : ∀ w, ‖f w‖ = ‖1 - (τ : ℂ) * w‖ * Real.exp (harm κ b D w) := by
    intro w
    simp only [hf, norm_mul, Complex.norm_exp, hQre]
  have hdiff : Differentiable ℂ f := by
    simp only [hf, hQ]
    fun_prop
  have key : ‖f z‖ ≤ 1 := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1)
      Metric.isBounded_ball hdiff.diffContOnCl ?_ ?_
    · intro w hw
      rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
      rw [hnorm]
      calc ‖1 - (τ : ℂ) * w‖ * Real.exp (harm κ b D w)
          ≤ Real.exp (-(harm κ b D w)) * Real.exp (harm κ b D w) :=
            mul_le_mul_of_nonneg_right (h w hw) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    · rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall_zero_iff]; exact hz
  rw [hnorm] at key
  calc ‖1 - (τ : ℂ) * z‖
      = ‖1 - (τ : ℂ) * z‖ * Real.exp (harm κ b D z) * Real.exp (-(harm κ b D z)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ 1 * Real.exp (-(harm κ b D z)) := mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = _ := one_mul _

section main

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- The normalised entry `a_ij / √(d_i d_j)` (zero when `d_i d_j = 0`). -/
noncomputable def nz (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ℂ :=
  if (A i i).re * (A j j).re = 0 then 0 else A i j / (Real.sqrt ((A i i).re * (A j j).re) : ℂ)

theorem norm_le_sqrt (hA : A.PosSemidef) (i j : Fin n) :
    ‖A i j‖ ≤ Real.sqrt ((A i i).re * (A j j).re) :=
  Real.le_sqrt_of_sq_le (norm_sq_le hA i j)

theorem eq_sqrt_mul_nz (hA : A.PosSemidef) (i j : Fin n) :
    A i j = (Real.sqrt ((A i i).re * (A j j).re) : ℂ) * nz A i j := by
  unfold nz
  split_ifs with h
  · have := norm_le_sqrt hA i j
    rw [h, Real.sqrt_zero] at this
    simp [norm_le_zero_iff.mp this]
  · have hpos : (Real.sqrt ((A i i).re * (A j j).re) : ℂ) ≠ 0 := by
      have h0 : 0 ≤ (A i i).re * (A j j).re := mul_nonneg (diag_eq_re hA i).1 (diag_eq_re hA j).1
      exact_mod_cast (Real.sqrt_pos.mpr (lt_of_le_of_ne h0 (Ne.symm h))).ne'
    field_simp

theorem norm_nz_le (hA : A.PosSemidef) (i j : Fin n) : ‖nz A i j‖ ≤ 1 := by
  unfold nz
  split_ifs with h
  · simp
  · have h0 : 0 ≤ (A i i).re * (A j j).re := mul_nonneg (diag_eq_re hA i).1 (diag_eq_re hA j).1
    have hpos : 0 < Real.sqrt ((A i i).re * (A j j).re) := Real.sqrt_pos.mpr (lt_of_le_of_ne h0 (Ne.symm h))
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_le_one hpos]
    exact norm_le_sqrt hA i j

/-- Schur positivity in normalised form:
`∑_{i,j} √(φ_i φ_j) Re (z_ij ^ m) ≥ 0` for `φ ≥ 0`, `m ≥ 1`, `z = nz A`. -/
theorem sum_sqrt_mul_nz_pow_nonneg (hA : A.PosSemidef) {m : ℕ} (hm : 1 ≤ m) (φ : Fin n → ℝ) (hφ : ∀ i, 0 ≤ φ i) :
    0 ≤ ∑ i, ∑ j, Real.sqrt (φ i * φ j) * ((nz A i j) ^ m).re := by
  set d : Fin n → ℝ := fun i => (A i i).re with hd
  have hd0 : ∀ i, 0 ≤ d i := fun i => (diag_eq_re hA i).1
  set w : Fin n → ℂ := fun i => if d i = 0 then 0 else ((Real.sqrt (φ i) / Real.sqrt (d i) ^ m : ℝ) : ℂ) with hw
  have h := (Complex.nonneg_iff.mp (sum_pow_nonneg hA m w)).1
  rw [Complex.re_sum] at h
  simp only [Complex.re_sum] at h
  refine le_of_le_of_eq h ?_
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hij : d i * d j = 0
  · have hz : nz A i j = 0 := by
      simp only [nz]; exact ite_eq_left_iff.mpr (fun h => absurd hij h)
    have hw0 : w i = 0 ∨ w j = 0 := by
      rcases mul_eq_zero.mp hij with h1 | h1
      · left; simp [hw, h1]
      · right; simp [hw, h1]
    rw [hz, zero_pow (by omega : m ≠ 0)]
    rcases hw0 with h1 | h1 <;> simp [h1]
  · have hi : d i ≠ 0 := fun h1 => hij (by rw [h1, zero_mul])
    have hj : d j ≠ 0 := fun h1 => hij (by rw [h1, mul_zero])
    have hsi : 0 < Real.sqrt (d i) := Real.sqrt_pos.mpr (lt_of_le_of_ne (hd0 i) (Ne.symm hi))
    have hsj : 0 < Real.sqrt (d j) := Real.sqrt_pos.mpr (lt_of_le_of_ne (hd0 j) (Ne.symm hj))
    have ha : A i j = ((Real.sqrt (d i) * Real.sqrt (d j) : ℝ) : ℂ) * nz A i j := by
      rw [← Real.sqrt_mul (hd0 i)]; exact eq_sqrt_mul_nz hA i j
    have hwi : w i = ((Real.sqrt (φ i) / Real.sqrt (d i) ^ m : ℝ) : ℂ) := by simp [hw, hi]
    have hwj : w j = ((Real.sqrt (φ j) / Real.sqrt (d j) ^ m : ℝ) : ℂ) := by simp [hw, hj]
    rw [hwi, hwj, ha, Complex.star_def, Complex.conj_ofReal, mul_pow, ← Complex.ofReal_pow,
      Real.sqrt_mul (hφ i)]
    have e : ((Real.sqrt (φ i) / Real.sqrt (d i) ^ m : ℝ) : ℂ)
          * (((Real.sqrt (d i) * Real.sqrt (d j)) ^ m : ℝ) * nz A i j ^ m)
          * ((Real.sqrt (φ j) / Real.sqrt (d j) ^ m : ℝ) : ℂ)
        = ((Real.sqrt (φ i) * Real.sqrt (φ j) : ℝ) : ℂ) * nz A i j ^ m := by
      have h1 : (Real.sqrt (d i) : ℂ) ≠ 0 := by exact_mod_cast hsi.ne'
      have h2 : (Real.sqrt (d j) : ℂ) ≠ 0 := by exact_mod_cast hsj.ne'
      push_cast
      field_simp
      ring
    rw [e, Complex.re_ofReal_mul]

end main

end MatrixIneq
