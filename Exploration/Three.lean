import Exploration.Two
import Exploration.Basic

/-!
# The reduced form for `n = 3`

Elementary proof.  Write `d_i = a_ii`, `F(d) = 1 + d + d²`, `r_i = √F(d_i)`, `x_ij = Re a_ij`.

1. `|1 - a_ij|² ≤ 1 + d_i d_j - 2 x_ij =: y_ij`, because `|a_ij|² ≤ d_i d_j`.
2. `(1 + s t) √(F s F t) ≤ F s F t - (s F t + t F s)/2` for `s, t ≥ 0` (`key3`), hence
   `y_ij / (r_i r_j) ≤ 1 - d_i/(2 r_i²) - d_j/(2 r_j²) - 2 x_ij/(r_i r_j)`.
3. Summing over the three pairs: `∑ y_ij/(r_i r_j) ≤ 3 - ∑_{i,j} a_ij/(r_i r_j) ≤ 3` by positive semidefiniteness.
4. AM-GM: `∏ y_ij/(r_i r_j) ≤ 1`, i.e. `∏_{i<j} y_ij ≤ ∏_i F(d_i)`.

This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

/-- `F(d) = 1 + d + d²`. -/
noncomputable def F3 (d : ℝ) : ℝ := 1 + d + d ^ 2

theorem F3_pos {d : ℝ} (hd : 0 ≤ d) : 0 < F3 d := by unfold F3; positivity

/-- The key scalar inequality for `n = 3`. -/
theorem key3 (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (1 + s * t) * Real.sqrt (F3 s * F3 t) ≤ F3 s * F3 t - (s * F3 t + t * F3 s) / 2 := by
  have hR : 0 ≤ F3 s * F3 t - (s * F3 t + t * F3 s) / 2 := by
    have : F3 s * F3 t - (s * F3 t + t * F3 s) / 2
        = (2 * s ^ 2 * t ^ 2 + s ^ 2 * t + 2 * s ^ 2 + s * t ^ 2 + s + 2 * t ^ 2 + t + 2) / 2 := by
      unfold F3; ring
    rw [this]; positivity
  have hsq : ((1 + s * t)) ^ 2 * (F3 s * F3 t) ≤ (F3 s * F3 t - (s * F3 t + t * F3 s) / 2) ^ 2 := by
    have : (F3 s * F3 t - (s * F3 t + t * F3 s) / 2) ^ 2 - (1 + s * t) ^ 2 * (F3 s * F3 t)
        = (s - t) ^ 2 * (5 * s ^ 2 * t ^ 2 + 4 * s ^ 2 * t + 4 * s ^ 2 + 4 * s * t ^ 2 + 2 * s * t + 4 * s
            + 4 * t ^ 2 + 4 * t + 5) / 4 := by
      unfold F3; ring
    have h2 : 0 ≤ (s - t) ^ 2 * (5 * s ^ 2 * t ^ 2 + 4 * s ^ 2 * t + 4 * s ^ 2 + 4 * s * t ^ 2 + 2 * s * t + 4 * s
            + 4 * t ^ 2 + 4 * t + 5) / 4 := by positivity
    linarith
  have h1 : 0 ≤ 1 + s * t := by positivity
  calc (1 + s * t) * Real.sqrt (F3 s * F3 t)
      = Real.sqrt ((1 + s * t) ^ 2 * (F3 s * F3 t)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1]
    _ ≤ Real.sqrt ((F3 s * F3 t - (s * F3 t + t * F3 s) / 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = F3 s * F3 t - (s * F3 t + t * F3 s) / 2 := Real.sqrt_sq hR

/-- AM-GM for three nonnegative reals with sum at most `3`. -/
theorem prod_le_one_of_sum_le_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ 3) : a * b * c ≤ 1 := by
  have h1 : 27 * (a * b * c) ≤ (a + b + c) ^ 3 := by
    nlinarith [mul_nonneg ha (sq_nonneg (b - c)), mul_nonneg hb (sq_nonneg (c - a)),
      mul_nonneg hc (sq_nonneg (a - b)), mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (a - b)),
      mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (b - c)),
      mul_nonneg (add_nonneg (add_nonneg ha hb) hc) (sq_nonneg (c - a))]
  have h2 : (a + b + c) ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by positivity) h 3
  linarith

/-- Per-pair bound: `|1 - a_ij|² ≤ r_i r_j (1 - d_i/(2 r_i²) - d_j/(2 r_j²)) - 2 Re a_ij`. -/
theorem pair_bound {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosSemidef) (i j : Fin n) :
    ‖1 - A i j‖ ^ 2 ≤ Real.sqrt (F3 (A i i).re) * Real.sqrt (F3 (A j j).re)
      - ((A i i).re * Real.sqrt (F3 (A j j).re) / Real.sqrt (F3 (A i i).re)
        + (A j j).re * Real.sqrt (F3 (A i i).re) / Real.sqrt (F3 (A j j).re)) / 2 - 2 * (A i j).re := by
  obtain ⟨hs, -⟩ := diag_eq_re hA i
  obtain ⟨ht, -⟩ := diag_eq_re hA j
  set s := (A i i).re
  set t := (A j j).re
  have hFs := F3_pos hs
  have hFt := F3_pos ht
  have hrs : 0 < Real.sqrt (F3 s) := Real.sqrt_pos.mpr hFs
  have hrt : 0 < Real.sqrt (F3 t) := Real.sqrt_pos.mpr hFt
  have h1 : ‖1 - A i j‖ ^ 2 = 1 - 2 * (A i j).re + ‖A i j‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp; ring
  have h2 := norm_sq_le hA i j
  have hk := key3 s t hs ht
  rw [Real.sqrt_mul hFs.le] at hk
  have hss : Real.sqrt (F3 s) * Real.sqrt (F3 s) = F3 s := Real.mul_self_sqrt hFs.le
  have htt : Real.sqrt (F3 t) * Real.sqrt (F3 t) = F3 t := Real.mul_self_sqrt hFt.le
  -- divide `hk` by `r_s r_t`
  have hdiv : 1 + s * t ≤ Real.sqrt (F3 s) * Real.sqrt (F3 t)
      - (s * Real.sqrt (F3 t) / Real.sqrt (F3 s) + t * Real.sqrt (F3 s) / Real.sqrt (F3 t)) / 2 := by
    have hpos : 0 < Real.sqrt (F3 s) * Real.sqrt (F3 t) := mul_pos hrs hrt
    rw [← mul_le_mul_iff_of_pos_right hpos]
    have e : (Real.sqrt (F3 s) * Real.sqrt (F3 t)
        - (s * Real.sqrt (F3 t) / Real.sqrt (F3 s) + t * Real.sqrt (F3 s) / Real.sqrt (F3 t)) / 2)
          * (Real.sqrt (F3 s) * Real.sqrt (F3 t)) = F3 s * F3 t - (s * F3 t + t * F3 s) / 2 := by
      field_simp
      nlinarith [hss, htt]
    rw [e]; exact hk
  linarith

/-- `n = 3`. -/
theorem reducedAt_three : ReducedAt 3 := by
  intro A hA
  have hd : ∀ i, 0 ≤ (A i i).re := fun i => (diag_eq_re hA i).1
  have hF : ∀ i, 0 < F3 (A i i).re := fun i => F3_pos (hd i)
  set r : Fin 3 → ℝ := fun i => Real.sqrt (F3 (A i i).re) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.sqrt_pos.mpr (hF i)
  have hrr : ∀ i, r i * r i = F3 (A i i).re := fun i => Real.mul_self_sqrt (hF i).le
  -- symmetric norms
  have hsym : ∀ i j, ‖1 - A j i‖ = ‖1 - A i j‖ := by
    intro i j
    rw [apply_conj hA i j, ← norm_star (1 - A i j), star_sub, star_one]
  -- positivity of the quadratic form with weights `1 / r_i`
  have hQ := sum_pow_nonneg hA 1 (fun i => ((1 / r i : ℝ) : ℂ))
  have hQre := (Complex.nonneg_iff.mp hQ).1
  have hre : ∀ i j, (A j i).re = (A i j).re := by
    intro i j; rw [apply_conj hA i j]; simp
  simp only [Fin.sum_univ_three, pow_one, Complex.star_def, Complex.conj_ofReal, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul] at hQre
  rw [hre 0 1, hre 0 2, hre 1 2] at hQre
  -- the three pair bounds
  have b01 := pair_bound hA 0 1
  have b02 := pair_bound hA 0 2
  have b12 := pair_bound hA 1 2
  set u01 := ‖1 - A 0 1‖ ^ 2 / (r 0 * r 1) with hu01
  set u02 := ‖1 - A 0 2‖ ^ 2 / (r 0 * r 2) with hu02
  set u12 := ‖1 - A 1 2‖ ^ 2 / (r 1 * r 2) with hu12
  have hu01n : 0 ≤ u01 := div_nonneg (sq_nonneg _) (mul_pos (hrpos 0) (hrpos 1)).le
  have hu02n : 0 ≤ u02 := div_nonneg (sq_nonneg _) (mul_pos (hrpos 0) (hrpos 2)).le
  have hu12n : 0 ≤ u12 := div_nonneg (sq_nonneg _) (mul_pos (hrpos 1) (hrpos 2)).le
  have key : ∀ i j : Fin 3, ‖1 - A i j‖ ^ 2 / (r i * r j) ≤
      1 - ((A i i).re / (r i * r i) + (A j j).re / (r j * r j)) / 2 - 2 * (A i j).re / (r i * r j) := by
    intro i j
    have hp := mul_pos (hrpos i) (hrpos j)
    rw [div_le_iff₀ hp]
    have b := pair_bound hA i j
    have e : (1 - ((A i i).re / (r i * r i) + (A j j).re / (r j * r j)) / 2 - 2 * (A i j).re / (r i * r j))
        * (r i * r j) = r i * r j - ((A i i).re * r j / r i + (A j j).re * r i / r j) / 2 - 2 * (A i j).re := by
      have := (hrpos i).ne'; have := (hrpos j).ne'
      field_simp
    rw [e]; exact b
  have hsum : u01 + u02 + u12 ≤ 3 := by
    have k01 := key 0 1; have k02 := key 0 2; have k12 := key 1 2
    have e : (1 / r 0 * (A 0 0).re * (1 / r 0) + 1 / r 0 * (A 0 1).re * (1 / r 1) + 1 / r 0 * (A 0 2).re * (1 / r 2)
        + (1 / r 1 * (A 0 1).re * (1 / r 0) + 1 / r 1 * (A 1 1).re * (1 / r 1) + 1 / r 1 * (A 1 2).re * (1 / r 2))
        + (1 / r 2 * (A 0 2).re * (1 / r 0) + 1 / r 2 * (A 1 2).re * (1 / r 1) + 1 / r 2 * (A 2 2).re * (1 / r 2)))
        = (A 0 0).re / (r 0 * r 0) + (A 1 1).re / (r 1 * r 1) + (A 2 2).re / (r 2 * r 2)
          + 2 * (A 0 1).re / (r 0 * r 1) + 2 * (A 0 2).re / (r 0 * r 2) + 2 * (A 1 2).re / (r 1 * r 2) := by
      have := (hrpos 0).ne'; have := (hrpos 1).ne'; have := (hrpos 2).ne'
      field_simp; ring
    rw [e] at hQre
    linarith
  have hprod := prod_le_one_of_sum_le_three hu01n hu02n hu12n hsum
  -- assemble
  have hL : ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖
      = ‖1 - A 0 1‖ ^ 2 * ‖1 - A 0 2‖ ^ 2 * ‖1 - A 1 2‖ ^ 2 := by
    have e0 : (univ : Finset (Fin 3)).erase 0 = {1, 2} := by decide
    have e1 : (univ : Finset (Fin 3)).erase 1 = {0, 2} := by decide
    have e2 : (univ : Finset (Fin 3)).erase 2 = {0, 1} := by decide
    rw [Fin.prod_univ_three, e0, e1, e2]
    simp only [prod_insert (show (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) by decide),
      prod_insert (show (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) by decide),
      prod_insert (show (0 : Fin 3) ∉ ({1} : Finset (Fin 3)) by decide), prod_singleton]
    rw [hsym 0 1, hsym 0 2, hsym 1 2]; ring
  have hR : ∏ i : Fin 3, ∑ k ∈ range 3, (A i i).re ^ k = F3 (A 0 0).re * F3 (A 1 1).re * F3 (A 2 2).re := by
    simp [Fin.prod_univ_three, sum_range_succ, F3]
  rw [hL, hR]
  have e : ‖1 - A 0 1‖ ^ 2 * ‖1 - A 0 2‖ ^ 2 * ‖1 - A 1 2‖ ^ 2
      = (u01 * u02 * u12) * ((r 0 * r 0) * (r 1 * r 1) * (r 2 * r 2)) := by
    have := (hrpos 0).ne'; have := (hrpos 1).ne'; have := (hrpos 2).ne'
    simp only [hu01, hu02, hu12]
    field_simp
  rw [e, hrr 0, hrr 1, hrr 2]
  have hFF : 0 ≤ F3 (A 0 0).re * F3 (A 1 1).re * F3 (A 2 2).re :=
    (mul_pos (mul_pos (hF 0) (hF 1)) (hF 2)).le
  calc u01 * u02 * u12 * (F3 (A 0 0).re * F3 (A 1 1).re * F3 (A 2 2).re)
      ≤ 1 * (F3 (A 0 0).re * F3 (A 1 1).re * F3 (A 2 2).re) := mul_le_mul_of_nonneg_right hprod hFF
    _ = _ := one_mul _

end MatrixIneq

namespace MatrixIneq

/-- **The main theorem for `n ≤ 3`.** -/
theorem mainTheorem_le_three {n : ℕ} (hn : n ≤ 3) (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖ := by
  interval_cases n
  · exact main_of_reducedAt reducedAt_zero A hA
  · exact main_of_reducedAt reducedAt_one A hA
  · exact main_of_reducedAt reducedAt_two A hA
  · exact main_of_reducedAt reducedAt_three A hA

end MatrixIneq
