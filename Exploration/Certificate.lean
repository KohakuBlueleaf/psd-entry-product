import MatrixIneq.Harmonic

/-!
# Certificates with rank-one (geometric-mean) cross coefficients

`Certificate n` and `reducedAt_of_certificate`: the first form of the certificate method, with cross
coefficient `√(c_m(s) c_m(t))`. The final proof uses the more general `KCertificate` of `MatrixIneq/Main.lean`.
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

/-- A certificate for size `n`. -/
structure Certificate (n : ℕ) where
  /-- the degree -/
  D : ℕ
  /-- the coefficient functions -/
  c : ℕ → ℝ → ℝ
  nonneg : ∀ m, 1 ≤ m → ∀ s, 0 ≤ s → 0 ≤ c m s
  total : ∀ s, 0 ≤ s →
    -Real.log (∑ k ∈ range n, s ^ k) ≤ ((n : ℝ) - 1) * c 0 s - ∑ m ∈ Icc 1 D, c m s
  circle : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ z : ℂ, ‖z‖ = 1 →
    ‖1 - (Real.sqrt (s * t) : ℂ) * z‖ ≤
      Real.exp (-(harm ((c 0 s + c 0 t) / 2) (fun m => Real.sqrt (c m s * c m t)) D z))

section main

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- **A certificate implies the reduced form.** -/
theorem reducedAt_of_certificate (C : Certificate n) : ReducedAt n := by
  intro A hA
  set d : Fin n → ℝ := fun i => (A i i).re with hd
  have hd0 : ∀ i, 0 ≤ d i := fun i => (diag_eq_re hA i).1
  set κ : Fin n → Fin n → ℝ := fun i j => (C.c 0 (d i) + C.c 0 (d j)) / 2 with hκ
  set b : Fin n → Fin n → ℕ → ℝ := fun i j m => Real.sqrt (C.c m (d i) * C.c m (d j)) with hb
  -- pair bound on the closed disc
  have hpair : ∀ i j, ‖1 - A i j‖ ≤ Real.exp (-(harm (κ i j) (b i j) C.D (nz A i j))) := by
    intro i j
    have := disc_of_circle (Real.sqrt (d i * d j)) (κ i j) (b i j) C.D
      (C.circle (d i) (d j) (hd0 i) (hd0 j)) (nz A i j) (norm_nz_le hA i j)
    rwa [← eq_sqrt_mul_nz hA i j] at this
  -- product of the pair bounds
  have hprod : ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖
      ≤ Real.exp (-(∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => norm_nonneg _) fun i _ => ?_
    rw [← sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hpair i j
  -- lower bound for the exponent
  have hS : ∑ i, (((n : ℝ) - 1) * C.c 0 (d i) - ∑ m ∈ Icc 1 C.D, C.c m (d i))
      ≤ ∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j) := by
    have hsplit : ∀ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j)
        = ∑ j, harm (κ i j) (b i j) C.D (nz A i j) - harm (κ i i) (b i i) C.D (nz A i i) := by
      intro i; rw [sum_erase_eq_sub (mem_univ i)]
    simp only [hsplit, sum_sub_distrib]
    -- the full double sum
    have hfull : ∑ i, ∑ j, harm (κ i j) (b i j) C.D (nz A i j)
        = (n : ℝ) * ∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re := by
      simp only [harm, sum_add_distrib]
      congr 1
      · simp only [hκ, add_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← sum_div, ← mul_sum]
        ring
      · rw [show (∑ m ∈ Icc 1 C.D, ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re)
            = ∑ i, ∑ m ∈ Icc 1 C.D, ∑ j, b i j m * ((nz A i j) ^ m).re from sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    have hdiag : ∑ i, harm (κ i i) (b i i) C.D (nz A i i)
        ≤ ∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, C.c m (d i) := by
      simp only [harm, sum_add_distrib]
      refine add_le_add (le_of_eq ?_) ?_
      · exact sum_congr rfl fun i _ => by simp [hκ]
      · rw [sum_comm]
        refine sum_le_sum fun m hm => sum_le_sum fun i _ => ?_
        have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
        have hc := C.nonneg m hm1 (d i) (hd0 i)
        have hbii : b i i m = C.c m (d i) := by simp [hb, Real.sqrt_mul_self hc]
        rw [hbii]
        have : ((nz A i i) ^ m).re ≤ 1 :=
          (Complex.re_le_norm _).trans (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_nz_le hA i i))
        nlinarith
    have hschur : ∀ m ∈ Icc 1 C.D, 0 ≤ ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re := by
      intro m hm
      exact sum_sqrt_mul_nz_pow_nonneg hA (mem_Icc.mp hm).1 (fun i => C.c m (d i))
        (fun i => C.nonneg m (mem_Icc.mp hm).1 (d i) (hd0 i))
    have hschur' := sum_nonneg hschur
    rw [hfull]
    have e : ∑ i, (((n : ℝ) - 1) * C.c 0 (d i)) - ∑ i, ∑ m ∈ Icc 1 C.D, C.c m (d i)
        = (n : ℝ) * ∑ i, C.c 0 (d i) - (∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, C.c m (d i)) := by
      rw [← mul_sum, sum_comm]; ring
    rw [e]
    linarith
  -- the total identity
  have hT : -(∑ i, Real.log (∑ k ∈ range n, d i ^ k))
      ≤ ∑ i, (((n : ℝ) - 1) * C.c 0 (d i) - ∑ m ∈ Icc 1 C.D, C.c m (d i)) := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun i _ => C.total (d i) (hd0 i)
  have hFpos : ∀ i, 0 < ∑ k ∈ range n, d i ^ k := by
    intro i
    by_cases hn : n = 0
    · exact (Fin.elim0 (hn ▸ i))
    · have : (1 : ℝ) ≤ ∑ k ∈ range n, d i ^ k := by
        calc (1 : ℝ) = d i ^ 0 := by simp
          _ ≤ ∑ k ∈ range n, d i ^ k :=
            single_le_sum (f := fun k => d i ^ k) (fun k _ => pow_nonneg (hd0 i) k)
              (mem_range.mpr (Nat.pos_of_ne_zero hn))
      linarith
  calc ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖
      ≤ Real.exp (-(∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j))) := hprod
    _ ≤ Real.exp (∑ i, Real.log (∑ k ∈ range n, d i ^ k)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = ∏ i, ∑ k ∈ range n, d i ^ k := by
        rw [Real.exp_sum]; exact prod_congr rfl fun i _ => Real.exp_log (hFpos i)


end main

/-- If every size has a certificate, the main theorem holds. -/
theorem mainTheorem_of_certificates (C : ∀ n, Certificate n) : Statement.MainTheorem :=
  mainTheorem_of_reduced fun n => reducedAt_of_certificate (C n)

end MatrixIneq
