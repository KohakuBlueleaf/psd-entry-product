import Exploration.HIn

/-!
# `HIn` follows from a θ-free convexity statement `QC`

Multiply `H_in = ½ P_α - Π` by `2 (cosh α - cos θ) > 0` (`P_α = sinh α / (cosh α - cos θ)`):

  `sinh α - 2 (cosh α - cos θ) Π(θ) = a_0 / 2 + ∑_{m=1}^{n-1} a_m cos mθ`,

where `Π = u_0/2 + ∑ u_m cos mθ`, `u_m = k_m(p) √(Γ_m(q)/Γ_m(p))`, and `a_m = u_{m-1} + u_{m+1} - 2 cosh α · u_m`
is the `α`-twisted second difference (which annihilates the Poisson part `e^{-mα}`).
If the sequence `a` is convex (`QC n`), Fejér's criterion gives nonnegativity, hence `HIn n`.

This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open Real Finset

namespace MatrixIneq

/-- On the unit circle, `Re z^{m+2} + Re z^m = 2 Re z · Re z^{m+1}`. -/
theorem re_pow_rec {z : ℂ} (hz : ‖z‖ = 1) (m : ℕ) :
    (z ^ (m + 2)).re + (z ^ m).re = 2 * z.re * (z ^ (m + 1)).re := by
  have h1 : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp
  have h3 : ((2 * z.re : ℝ) : ℂ) = z + (starRingEnd ℂ) z := (Complex.add_conj z).symm
  have h2 : z ^ (m + 2) + z ^ m = z ^ (m + 1) * ((2 * z.re : ℝ) : ℂ) := by
    rw [h3]
    calc z ^ (m + 2) + z ^ m = z ^ (m + 2) + z ^ m * (z * (starRingEnd ℂ) z) := by rw [h1, mul_one]
      _ = _ := by ring
  have := congrArg Complex.re h2
  rw [Complex.add_re, Complex.re_mul_ofReal] at this
  linarith

/-- Summation by parts twice (exact finite identity, arbitrary sequence). -/
theorem fejer_identity (a : ℕ → ℝ) {z : ℂ} (hz : ‖z‖ = 1) (M : ℕ) :
    2 * (1 - z.re) * (a 0 / 2 + ∑ m ∈ Icc 1 M, a m * (z ^ m).re)
      = ∑ j ∈ range M, (a j - 2 * a (j + 1) + a (j + 2)) * (1 - (z ^ (j + 1)).re)
        + a M * (1 - (z ^ (M + 1)).re) - a (M + 1) * (1 - (z ^ M).re) := by
  induction M with
  | zero => simp; ring
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    have h := re_pow_rec hz M
    linear_combination ih + a (M + 1) * h

theorem nonneg_of_convex_eventually_zero {a : ℕ → ℝ} {M : ℕ} (h0 : ∀ m, M ≤ m → a m = 0)
    (hc : ∀ j, 0 ≤ a j - 2 * a (j + 1) + a (j + 2)) : ∀ j, 0 ≤ a j := by
  have hd : ∀ k j, a (j + k) - a (j + k + 1) ≤ a j - a (j + 1) := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih =>
      intro j
      have h1 := ih (j + 1)
      have h2 := hc j
      have e : j + (k + 1) = j + 1 + k := by ring
      rw [e]
      have e2 : j + 1 + 1 = j + 2 := rfl
      rw [e2] at h1
      linarith
  have hdec : ∀ j, a (j + 1) ≤ a j := by
    intro j
    have := hd M j
    rw [h0 (j + M) (by omega), h0 (j + M + 1) (by omega)] at this
    linarith
  have hk : ∀ k j, a (j + k) ≤ a j := by
    intro k
    induction k with
    | zero => intro j; simp
    | succ k ih => intro j; exact (hdec (j + k)).trans (ih j)
  intro j
  have := hk M j
  rwa [h0 _ (by omega)] at this

/-- **Fejér's criterion.** A convex, eventually zero sequence has a nonnegative cosine sum. -/
theorem fejer_criterion {a : ℕ → ℝ} {M : ℕ} (h0 : ∀ m, M ≤ m → a m = 0)
    (hc : ∀ j, 0 ≤ a j - 2 * a (j + 1) + a (j + 2)) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ a 0 / 2 + ∑ m ∈ Icc 1 M, a m * (z ^ m).re := by
  have hpos := nonneg_of_convex_eventually_zero h0 hc
  have hre : ∀ m : ℕ, (z ^ m).re ≤ 1 := fun m => by
    have := Complex.re_le_norm (z ^ m)
    rwa [norm_pow, hz, one_pow] at this
  have h1 : z.re ≤ 1 := by simpa using hre 1
  rcases h1.lt_or_eq with hlt | heq
  · have hid := fejer_identity a hz M
    rw [h0 M le_rfl, h0 (M + 1) (by omega)] at hid
    have hR : 0 ≤ ∑ j ∈ range M, (a j - 2 * a (j + 1) + a (j + 2)) * (1 - (z ^ (j + 1)).re) :=
      sum_nonneg fun j _ => mul_nonneg (hc j) (sub_nonneg.mpr (hre _))
    have : 0 ≤ 2 * (1 - z.re) * (a 0 / 2 + ∑ m ∈ Icc 1 M, a m * (z ^ m).re) := by
      rw [hid]; linarith
    exact nonneg_of_mul_nonneg_right this (by linarith)
  · have hn : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
    have him : z.im = 0 := by
      have : z.im * z.im = 0 := by rw [heq] at hn; linarith
      exact mul_self_eq_zero.mp this
    have hz1 : z = 1 := Complex.ext (by simpa using heq) (by simpa using him)
    subst hz1
    simp only [one_pow, Complex.one_re, mul_one]
    exact add_nonneg (by linarith [hpos 0]) (sum_nonneg fun m _ => hpos m)

/-- The twisted-second-difference identity (exact, arbitrary sequence `u`). -/
theorem twist_identity (u : ℕ → ℝ) (s C : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (K : ℕ) :
    (s - u 0 * C + u 1) + ∑ m ∈ Icc 1 K, (u (m - 1) + u (m + 1) - 2 * C * u m) * (z ^ m).re
      = s - 2 * (C - z.re) * (u 0 / 2 + ∑ m ∈ Icc 1 K, u m * (z ^ m).re)
        + (u (K + 1) * (z ^ K).re - u K * (z ^ (K + 1)).re) := by
  induction K with
  | zero => simp; ring
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have h := re_pow_rec hz K
    simp only [Nat.add_sub_cancel]
    linear_combination ih + u (K + 1) * h

/-- `u_m = k_m(p) √(Γ_m(q)/Γ_m(p))` for `1 ≤ m ≤ n-2`, `u_0 = k_0(p)`, `u_m = 0` for `m ≥ n-1`. -/
noncomputable def uCoef (n : ℕ) (p q : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then kern n 0 p
  else if m ≤ n - 2 then kern n m p * Real.sqrt (Gam n m q / Gam n m p) else 0

/-- Twisted coefficients: `a_0 = 2 (sinh α − u_0 cosh α + u_1)`, `a_m = u_{m−1} + u_{m+1} − 2 cosh α · u_m`
(`m ≥ 1`), `α = (p+q)/2`. -/
noncomputable def aCoef (n : ℕ) (p q : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 2 * (Real.sinh ((p + q) / 2) - uCoef n p q 0 * Real.cosh ((p + q) / 2) + uCoef n p q 1)
  else uCoef n p q (m - 1) + uCoef n p q (m + 1) - 2 * Real.cosh ((p + q) / 2) * uCoef n p q m

/-- **θ-free convexity statement**: the twisted coefficient sequence is convex. -/
def QC (n : ℕ) : Prop :=
  ∀ p q : ℝ, 0 < p → p < q → ∀ j : ℕ, 0 ≤ aCoef n p q j - 2 * aCoef n p q (j + 1) + aCoef n p q (j + 2)

theorem uCoef_eq_zero {n : ℕ} (hn : 3 ≤ n) (p q : ℝ) {m : ℕ} (hm : n - 1 ≤ m) : uCoef n p q m = 0 := by
  unfold uCoef
  simp only [if_neg (show ¬ m = 0 by omega), if_neg (show ¬ m ≤ n - 2 by omega)]

theorem aCoef_eq_zero {n : ℕ} (hn : 3 ≤ n) (p q : ℝ) {m : ℕ} (hm : n ≤ m) : aCoef n p q m = 0 := by
  unfold aCoef
  rw [if_neg (by omega), uCoef_eq_zero hn p q (by omega), uCoef_eq_zero hn p q (by omega),
    uCoef_eq_zero hn p q (by omega)]
  ring

theorem hIn_of_qc {n : ℕ} (hn : 3 ≤ n) (h : QC n) : HIn n := by
  intro p q hp hpq z hz
  set α : ℝ := (p + q) / 2 with hα
  have hαpos : 0 < α := by rw [hα]; linarith
  set u := uCoef n p q with hu
  -- the left side of `HIn` in terms of `u`, with the sum extended to `n`
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hS : kern (k + 2) 0 p / 2 + ∑ m ∈ Icc 1 (k + 2 - 2),
        kern (k + 2) m p * Real.sqrt (Gam (k + 2) m q / Gam (k + 2) m p) * (z ^ m).re
      = u 0 / 2 + ∑ m ∈ Icc 1 (k + 2), u m * (z ^ m).re := by
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      hu, uCoef_eq_zero hn p q (show k + 2 - 1 ≤ k + 1 + 1 by omega),
      uCoef_eq_zero hn p q (show k + 2 - 1 ≤ k + 1 by omega)]
    have h0 : uCoef (k + 2) p q 0 = kern (k + 2) 0 p := by simp [uCoef]
    rw [h0, zero_mul, zero_mul, add_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_Icc] at hm
    unfold uCoef
    rw [if_neg (by omega), if_pos (by omega)]
  rw [hS]
  -- Fejér's criterion for the twisted coefficients
  have hF := fejer_criterion (a := aCoef (k + 2) p q) (M := k + 2)
    (fun m hm => aCoef_eq_zero hn p q hm) (h p q hp hpq) hz
  have hT := twist_identity u (Real.sinh α) (Real.cosh α) hz (k + 2)
  rw [hu, uCoef_eq_zero hn p q (show k + 2 - 1 ≤ k + 2 + 1 by omega),
    uCoef_eq_zero hn p q (show k + 2 - 1 ≤ k + 2 by omega)] at hT
  have hA : aCoef (k + 2) p q 0 / 2 + ∑ m ∈ Icc 1 (k + 2), aCoef (k + 2) p q m * (z ^ m).re
      = (Real.sinh α - uCoef (k + 2) p q 0 * Real.cosh α + uCoef (k + 2) p q 1)
        + ∑ m ∈ Icc 1 (k + 2), (uCoef (k + 2) p q (m - 1) + uCoef (k + 2) p q (m + 1)
            - 2 * Real.cosh α * uCoef (k + 2) p q m) * (z ^ m).re := by
    congr 1
    · simp [aCoef, hα]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_Icc] at hm
      unfold aCoef
      rw [if_neg (by omega)]
  rw [hA, hT] at hF
  set S := u 0 / 2 + ∑ m ∈ Icc 1 (k + 2), u m * (z ^ m).re with hSdef
  have hF' : 2 * (Real.cosh α - z.re) * S ≤ Real.sinh α := by
    linarith
  -- rewrite in terms of `E = e^{-α}`
  set E : ℝ := Real.exp (-(p + q) / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E < 1 := by
    rw [hE, ← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have hEα : Real.exp (-α) = E := by rw [hE, hα]; congr 1; ring
  have hEα' : Real.exp α = E⁻¹ := by rw [← hEα, Real.exp_neg, inv_inv]
  have hE2 : Real.exp (-(p + q)) = E ^ 2 := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hc1 : z.re ≤ 1 := by
    have := Complex.re_le_norm z
    rwa [hz] at this
  have hnorm : ‖1 - (E : ℂ) * z‖ ^ 2 = 1 - 2 * E * z.re + E ^ 2 := by
    have hn : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_sub]
    nlinarith [hn]
  have hden : 0 < 1 - 2 * E * z.re + E ^ 2 := by nlinarith [sq_nonneg (1 - E), mul_pos hEpos hEpos]
  rw [hE2, hnorm, le_div_iff₀ (by linarith)]
  rw [Real.sinh_eq, Real.cosh_eq, hEα, hEα'] at hF'
  have hinv : E * E⁻¹ = 1 := mul_inv_cancel₀ hEpos.ne'
  have := mul_le_mul_of_nonneg_left hF' (by linarith : (0 : ℝ) ≤ 2 * E)
  nlinarith [this, hinv]

theorem mainTheorem_of_qc (h : ∀ n, 3 ≤ n → QC n) : Statement.MainTheorem :=
  mainTheorem_of_hIn fun n hn => hIn_of_qc hn (h n hn)

end MatrixIneq
