import MatrixIneq.Coefficients
import Exploration.Certificate
import Exploration.Two

/-!
# The geometric-mean pair inequality `Star n`

`Star n` is the pair inequality with cross coefficients `√(Γ_m(p) Γ_m(q))`; it implies the main theorem
(`mainTheorem_of_star`) but is not proved here in general.
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-! ### The two-parameter inequality and the certificate -/

/-- The two-parameter inequality at a fixed pair `(p, q)`:
`-log |1 - e^{-(p+q)/2} z| ≥ (Γ_0(p) + Γ_0(q))/2 + ∑_{m=1}^{n-2} √(Γ_m(p) Γ_m(q)) · Re (z^m)` for `|z| = 1`. -/
def StarAt (n : ℕ) (p q : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 →
    ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * z‖ ≤
      Real.exp (-(harm ((Gam0 n p + Gam0 n q) / 2) (fun m => Real.sqrt (Gam n m p * Gam n m q)) (n - 2) z))

/-- **The remaining inequality.** `StarAt n p q` for all `p, q ≥ 0`. -/
def Star (n : ℕ) : Prop :=
  ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → ∀ z : ℂ, ‖z‖ = 1 →
    ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * z‖ ≤
      Real.exp (-(harm ((Gam0 n p + Gam0 n q) / 2) (fun m => Real.sqrt (Gam n m p * Gam n m q)) (n - 2) z))

theorem Star.starAt {n : ℕ} (h : Star n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : StarAt n p q :=
  fun z hz => h p q hp hq z hz

theorem coef_circle {n : ℕ} (s t : ℝ) (h : StarAt n |log s| |log t|) (hs : 0 ≤ s) (ht : 0 ≤ t) (z : ℂ)
    (hz : ‖z‖ = 1) :
    ‖1 - (Real.sqrt (s * t) : ℂ) * z‖ ≤
      Real.exp (-(harm ((coef n 0 s + coef n 0 t) / 2) (fun m => Real.sqrt (coef n m s * coef n m t)) (n - 2) z)) := by
  have hzero : ∀ u v : ℝ, u = 0 →
      ‖1 - (Real.sqrt (u * v) : ℂ) * z‖ ≤
        Real.exp (-(harm ((coef n 0 u + coef n 0 v) / 2) (fun m => Real.sqrt (coef n m u * coef n m v)) (n - 2) z)) := by
    intro u v hu
    subst hu
    have hc : ∀ m, coef n m 0 = 0 := fun m => by simp [coef]
    simp only [harm, hc, zero_mul, Real.sqrt_zero, sum_const_zero, add_zero, zero_add, Complex.ofReal_zero,
      sub_zero, norm_one]
    have := coef_zero_nonpos n v
    exact Real.one_le_exp (by linarith)
  rcases hs.eq_or_lt with h0 | hs0
  · exact hzero s t h0.symm
  rcases ht.eq_or_lt with h0 | ht0
  · have := hzero t s h0.symm
    simpa [mul_comm, add_comm] using this
  -- both positive
  set a := log s with ha
  set b := log t with hb
  set A : ℝ := (max a 0 + max b 0) / 2 with hA
  have hA0 : 0 ≤ A := by
    have := le_max_right a 0; have := le_max_right b 0; positivity
  have hsqrt : Real.sqrt (s * t) = exp ((a + b) / 2) := by
    rw [exp_half, exp_add, exp_log hs0, exp_log ht0]
  have hab : (a + b) / 2 - A ≤ 0 := by
    have := le_max_left a 0; have := le_max_left b 0
    rw [hA]; linarith
  have habs : (a + b) / 2 - A - A = -(|a| + |b|) / 2 := by
    rw [hA]
    rcases le_total a 0 with h1 | h1 <;> rcases le_total b 0 with h2 | h2 <;>
      simp only [abs_of_nonpos, abs_of_nonneg, max_eq_left, max_eq_right, h1, h2] <;> ring
  have hKc : exp A * exp ((a + b) / 2 - A) = exp ((a + b) / 2) := by
    rw [← exp_add]; congr 1; ring
  have hcK : exp ((a + b) / 2 - A) / exp A = exp (-(|a| + |b|) / 2) := by
    rw [← exp_sub, habs]
  have hstep := norm_one_sub_mul_le (K := exp A) (c := exp ((a + b) / 2 - A)) (Real.one_le_exp hA0)
    (exp_pos _).le (exp_le_one_iff.mpr hab) hz
  rw [hKc, hcK] at hstep
  have hstar := h z hz
  have hs' : s ≠ 0 := hs0.ne'
  have ht' : t ≠ 0 := ht0.ne'
  have hharm : harm ((coef n 0 s + coef n 0 t) / 2) (fun m => Real.sqrt (coef n m s * coef n m t)) (n - 2) z
      = harm ((Gam0 n |a| + Gam0 n |b|) / 2) (fun m => Real.sqrt (Gam n m |a| * Gam n m |b|)) (n - 2) z - A := by
    unfold harm
    have e1 : ∑ m ∈ Finset.Icc 1 (n - 2), Real.sqrt (coef n m s * coef n m t) * (z ^ m).re
        = ∑ m ∈ Finset.Icc 1 (n - 2), Real.sqrt (Gam n m |a| * Gam n m |b|) * (z ^ m).re := by
      refine sum_congr rfl fun m hm => ?_
      have : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
      simp [coef, hs', ht', this, ha, hb]
    rw [e1]
    simp only [coef, hs', ht', ↓reduceIte, ← ha, ← hb, hA]
    ring
  rw [hsqrt, hharm]
  calc ‖1 - (exp ((a + b) / 2) : ℂ) * z‖
      ≤ exp A * ‖1 - (exp (-(|a| + |b|) / 2) : ℂ) * z‖ := hstep
    _ ≤ exp A * Real.exp (-(harm ((Gam0 n |a| + Gam0 n |b|) / 2)
          (fun m => Real.sqrt (Gam n m |a| * Gam n m |b|)) (n - 2) z)) :=
        mul_le_mul_of_nonneg_left hstar (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

/-- **`Star n` gives a certificate.** -/
noncomputable def certificate_of_star {n : ℕ} (hn : 1 ≤ n) (h : Star n) : Certificate n where
  D := n - 2
  c := coef n
  nonneg := fun _ hm s _ => coef_nonneg n hm s
  total := fun _ hs => coef_total hn hs
  circle := fun s t hs ht z hz => coef_circle s t (h.starAt (abs_nonneg _) (abs_nonneg _)) hs ht z hz

/-- If the two-parameter inequality `Star n` holds for every `n ≥ 3`, the main theorem follows. -/
theorem mainTheorem_of_star (h : ∀ n, 3 ≤ n → Star n) : Statement.MainTheorem := by
  refine mainTheorem_of_reduced fun n => ?_
  by_cases hn : 3 ≤ n
  · exact reducedAt_of_certificate (certificate_of_star (by omega) (h n hn))
  · have : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact reducedAt_zero
    · exact reducedAt_one
    · exact reducedAt_two


end MatrixIneq
