import MatrixIneq.Coefficients

/-!
# Monotonicity of `χ_m` and the bound `k_m ≤ m Γ_m`

* `chi_mono`, `hasDerivAt_chi`: `χ_m(w) = e^{m w} k_m(w)` is nondecreasing on `w > 0`. Its derivative is the
  mixing weight that makes the τ-kernel positive semidefinite.
* `integrableOn_kern`: the kernels are integrable on `(p, ∞)`.
* `kern_le_mul_Gam`: `k_m(x) ≤ m Γ_m(x)` for `1 ≤ m ≤ n - 2`, `x ≥ 0`.
-/

open Real MeasureTheory Set Filter Finset

namespace MatrixIneq

/-! ### The key inequality, in exponential form -/

/-- `(1 + cosh w)(e^{N w} - 1) ≤ N sinh w (e^{N w} + 1)`; equivalent to `tanh (N w / 2) ≤ N tanh (w / 2)`. -/
theorem key_exp (N : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    (1 + cosh w) * (exp (N * w) - 1) ≤ N * sinh w * (exp (N * w) + 1) := by
  have hs : 0 ≤ sinh w := sinh_nonneg_iff.mpr hw
  have he1 : 1 ≤ exp w := one_le_exp hw
  have hcs : cosh w + sinh w = exp w := cosh_add_sinh w
  have hsq : cosh w ^ 2 = sinh w ^ 2 + 1 := cosh_sq w
  have id1 : (1 + cosh w) * (exp w - 1) = sinh w * (exp w + 1) := by
    rw [← hcs]; linear_combination hsq
  induction N with
  | zero => simp
  | succ N ih =>
    have hE : exp (((N + 1 : ℕ) : ℝ) * w) = exp (N * w) * exp w := by
      rw [← exp_add]; congr 1; push_cast; ring
    have hbern : 1 + (N : ℝ) * (exp w - 1) ≤ exp (N * w) := by
      rw [exp_nat_mul]
      have := one_add_mul_le_pow (a := exp w - 1) (by linarith) N
      simpa using this
    rw [hE]; push_cast
    set E := exp (N * w) with hEdef
    set e := exp w with hedef
    set s := sinh w
    set c := cosh w
    have hA : 0 ≤ (N : ℝ) * s * (E + 1) - (1 + c) * (E - 1) := by linarith
    have hE1 : 1 ≤ E := by rw [hEdef]; exact one_le_exp (by positivity)
    have hB : 0 ≤ e * (E - 1) - (N : ℝ) * (e - 1) := by
      have : 0 ≤ (e - 1) * (E - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ e) hA
    have h2 := mul_nonneg hs hB
    nlinarith [h1, h2, id1]

/-- For `N ≤ n` and `w ≥ 0`: `n (e^{N w} - 1) ≤ N (e^{n w} - 1)`  (`y ↦ (e^y - 1)/y` is nondecreasing). -/
theorem exp_sub_one_scaling {n N : ℕ} (hN : N ≤ n) (w : ℝ) :
    (n : ℝ) * (exp (N * w) - 1) ≤ N * (exp (n * w) - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : N = 0 := by omega
    subst this; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast hpos
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hN
  have ha : (0 : ℝ) ≤ N / n := by positivity
  have hb : (0 : ℝ) ≤ 1 - N / n := by
    rw [sub_nonneg, div_le_one hn]; exact hNn
  have h := convexOn_exp.2 (mem_univ ((n : ℝ) * w)) (mem_univ (0 : ℝ)) ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, exp_zero, mul_one] at h
  have e : (N : ℝ) / n * (n * w) = N * w := by field_simp
  rw [e] at h
  have h2 := mul_le_mul_of_nonneg_left h hn.le
  have e2 : (n : ℝ) * ((N : ℝ) / n * exp (n * w) + (1 - N / n)) = N * exp (n * w) + (n - N) := by
    field_simp
  rw [e2] at h2
  linarith

/-- The numerator of the derivative of `χ` is nonnegative. Here `u = sinh (N w) - N sinh w`,
`u' = N (cosh (N w) - cosh w)`, `v = cosh (n w) - 1`, `v' = n sinh (n w)`, and `m = n - N`. -/
theorem chi_deriv_num_nonneg {n N : ℕ} (hN : N ≤ n) {w : ℝ} (hw : 0 < w) :
    0 ≤ ((n : ℝ) - N) * (sinh (N * w) - N * sinh w) * (cosh (n * w) - 1)
        + N * (cosh (N * w) - cosh w) * (cosh (n * w) - 1)
        - (sinh (N * w) - N * sinh w) * (n * sinh (n * w)) := by
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · subst h0; simp
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set EN := exp (N * w) with hEN
  set En := exp (n * w) with hEn
  have hENpos : 0 < EN := exp_pos _
  have hEnpos : 0 < En := exp_pos _
  have hEN1 : 1 < EN := by
    rw [hEN]; exact one_lt_exp_iff.mpr (by positivity)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hNr (by exact_mod_cast hN)
  have hEn1 : 1 < En := by
    rw [hEn]; exact one_lt_exp_iff.mpr (by positivity)
  have hsN : sinh (N * w) = (EN - EN⁻¹) / 2 := by rw [sinh_eq, exp_neg]
  have hcN : cosh (N * w) = (EN + EN⁻¹) / 2 := by rw [cosh_eq, exp_neg]
  have hsn : sinh (n * w) = (En - En⁻¹) / 2 := by rw [sinh_eq, exp_neg]
  have hcn : cosh (n * w) = (En + En⁻¹) / 2 := by rw [cosh_eq, exp_neg]
  set s := sinh w
  set c := cosh w
  set u := sinh (N * w) - N * s with hu
  set v := cosh (n * w) - 1 with hv
  have hu0 : 0 ≤ u := sub_nonneg.mpr (nat_mul_sinh_le_sinh_nat_mul N hw.le)
  have hv0 : 0 ≤ v := sub_nonneg.mpr (one_le_cosh _)
  -- `D = u' - N u`
  set D := (N : ℝ) * (cosh (N * w) - c) - N * u with hD
  have hK := key_exp N hw.le
  -- `2 N u ≤ D (EN - 1)`
  have hD1 : 2 * (N : ℝ) * u ≤ D * (EN - 1) := by
    have e : D * (EN - 1) - 2 * (N : ℝ) * u
        = N * ((N : ℝ) * s * (EN + 1) - (1 + c) * (EN - 1)) := by
      rw [hD, hu, hsN, hcN]; field_simp; ring
    have : 0 ≤ (N : ℝ) * ((N : ℝ) * s * (EN + 1) - (1 + c) * (EN - 1)) :=
      mul_nonneg hNr.le (by linarith)
    linarith
  have hDnn : 0 ≤ D := by
    have h : 0 ≤ D * (EN - 1) := le_trans (by positivity) hD1
    by_contra hneg
    have : D * (EN - 1) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) (by linarith)
    linarith
  have hscale := exp_sub_one_scaling hN w
  -- `2 n u ≤ D (En - 1)`
  have hD2 : 2 * (n : ℝ) * u ≤ D * (En - 1) := by
    have h1 : D * ((n : ℝ) * (EN - 1)) ≤ D * (N * (En - 1)) := mul_le_mul_of_nonneg_left hscale hDnn
    have h2 : (n : ℝ) * (2 * N * u) ≤ n * (D * (EN - 1)) := mul_le_mul_of_nonneg_left hD1 hnpos.le
    have h3 : (N : ℝ) * (2 * n * u) ≤ N * (D * (En - 1)) := by nlinarith
    exact le_of_mul_le_mul_left h3 hNr
  -- `sinh (n w) (En - 1) = v (En + 1)`
  have hS : sinh (n * w) * (En - 1) = v * (En + 1) := by
    rw [hv, hsn, hcn]; field_simp; ring
  set G := ((n : ℝ) - N) * u * v + N * (cosh (N * w) - c) * v - u * (n * sinh (n * w)) with hG
  have hGeq : (En - 1) * G = v * (D * (En - 1) - 2 * n * u) := by
    rw [hG, hD]; linear_combination (-(n : ℝ) * u) * hS
  have hpos : 0 ≤ v * (D * (En - 1) - 2 * n * u) := mul_nonneg hv0 (by linarith)
  have : (En - 1) * 0 ≤ (En - 1) * G := by rw [mul_zero, hGeq]; exact hpos
  exact le_of_mul_le_mul_left this (by linarith)

/-! ### Monotonicity of `χ` -/

/-- `χ_m(w) = e^{m w} k_m(w)` has a nonnegative derivative at every `w > 0`. -/
theorem hasDerivAt_chi {n m : ℕ} (hm : m ≤ n) {w : ℝ} (hw : 0 < w) :
    ∃ d : ℝ, HasDerivAt (fun w => exp (m * w) * kern n m w) d w ∧ 0 ≤ d := by
  set N := n - m with hNdef
  have hNn : N ≤ n := Nat.sub_le n m
  have hmN : (m : ℝ) = (n : ℝ) - N := by
    have : m + N = n := by omega
    have h : ((m + N : ℕ) : ℝ) = n := by exact_mod_cast this
    push_cast at h; linarith
  have hn0 : (n : ℝ) * w ≠ 0 ∨ n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · right; exact h
    · left; have : (0 : ℝ) < n := by exact_mod_cast h
      positivity
  rcases Nat.eq_zero_or_pos n with h0 | hnpos
  · -- `n = 0`: the kernel is identically zero
    subst h0
    have hm0 : m = 0 := by omega
    subst hm0
    refine ⟨0, ?_, le_rfl⟩
    have : (fun w : ℝ => exp (((0 : ℕ) : ℝ) * w) * kern 0 0 w) = fun _ => (0 : ℝ) := by
      funext w; simp [kern]
    rw [this]; exact hasDerivAt_const w 0
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hvpos : 0 < cosh (n * w) - 1 := by
    have : 1 < cosh (n * w) := one_lt_cosh.mpr (by positivity)
    linarith
  have hexp : HasDerivAt (fun w : ℝ => exp (m * w)) (exp (m * w) * (m * 1)) w :=
    ((hasDerivAt_id w).const_mul (m : ℝ)).exp
  have hu : HasDerivAt (fun w : ℝ => sinh (N * w) - N * sinh w)
      (cosh (N * w) * (N * 1) - N * cosh w) w :=
    (((hasDerivAt_id w).const_mul (N : ℝ)).sinh).sub ((hasDerivAt_sinh w).const_mul (N : ℝ))
  have hv : HasDerivAt (fun w : ℝ => cosh (n * w) - 1) (sinh (n * w) * (n * 1)) w := by
    simpa using (((hasDerivAt_id w).const_mul (n : ℝ)).cosh).sub_const 1
  have hdiv := hu.div hv hvpos.ne'
  have hmul := hexp.mul hdiv
  have hfun : (fun w : ℝ => exp (m * w) * kern n m w)
      = (fun w : ℝ => exp (m * w)) * ((fun w : ℝ => sinh (N * w) - N * sinh w) / fun w : ℝ => cosh (n * w) - 1) := by
    funext w; simp [kern, hNdef]
  rw [← hfun] at hmul
  refine ⟨_, hmul, ?_⟩
  have hnum := chi_deriv_num_nonneg hNn hw
  have hE : 0 < exp (m * w) := exp_pos _
  have key : exp (m * w) * (m * 1) * ((sinh (N * w) - N * sinh w) / (cosh (n * w) - 1))
      + exp (m * w) * (((cosh (N * w) * (N * 1) - N * cosh w) * (cosh (n * w) - 1)
          - (sinh (N * w) - N * sinh w) * (sinh (n * w) * (n * 1))) / (cosh (n * w) - 1) ^ 2)
      = exp (m * w) / (cosh (n * w) - 1) ^ 2 *
        (((n : ℝ) - N) * (sinh (N * w) - N * sinh w) * (cosh (n * w) - 1)
          + N * (cosh (N * w) - cosh w) * (cosh (n * w) - 1)
          - (sinh (N * w) - N * sinh w) * (n * sinh (n * w))) := by
    rw [hmN]; field_simp; ring
  simp only [Pi.div_apply]
  rw [key]
  exact mul_nonneg (div_nonneg hE.le (by positivity)) hnum

/-- `χ_m(w) = e^{m w} k_m(w)` is nondecreasing on `w > 0`. -/
theorem chi_mono {n m : ℕ} (hm : m ≤ n) :
    MonotoneOn (fun w => exp (m * w) * kern n m w) (Ioi 0) := by
  have hd : ∀ w ∈ Ioi (0 : ℝ), ∃ d : ℝ, HasDerivAt (fun w => exp (m * w) * kern n m w) d w ∧ 0 ≤ d :=
    fun w hw => hasDerivAt_chi hm hw
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro w hw
    obtain ⟨d, h, -⟩ := hd w hw
    exact h.continuousAt.continuousWithinAt
  · rw [interior_Ioi]
    intro w hw
    obtain ⟨d, h, -⟩ := hd w hw
    exact h.differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro w hw
    obtain ⟨d, h, h0⟩ := hd w hw
    rw [h.deriv]; exact h0

/-! ### The hazard-rate bound -/

/-- The kernels `k_m`, `1 ≤ m ≤ n - 2`, are integrable on `(p, ∞)` for `p ≥ 0`. -/
theorem integrableOn_kern {n m : ℕ} (hn : 1 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn (kern n m) (Ioi p) := by
  set A : ℝ → ℝ := fun w => ((n : ℝ) - 1) * ((kern n 0 w - 1) / 2) with hA
  set B : ℝ → ℝ := fun w => ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w with hB
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : ∀ w ∈ Ioi p, 0 ≤ w := fun w hw => hp.trans (le_of_lt hw)
  have hAle : ∀ w ∈ Ioi p, A w ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos hn1 (by have := kern_zero_le_one n (hpos w hw); linarith)
  have hBge : ∀ w ∈ Ioi p, 0 ≤ B w := fun w hw =>
    Finset.sum_nonneg fun m _ => kern_nonneg n m (hpos w hw)
  have hderiv : ∀ w ∈ Ioi p, HasDerivAt (logF n) (A w - B w) w := by
    intro w hw
    have hw0 : 0 < w := lt_of_le_of_lt hp hw
    have := hasDerivAt_logF hn hw0
    rwa [← kern_identity hn hw0] at this
  have hneg : ∀ w ∈ Ioi p, A w - B w ≤ 0 := fun w hw => by linarith [hAle w hw, hBge w hw]
  have hcont : ContinuousWithinAt (logF n) (Ici p) p := (continuous_logF hn).continuousWithinAt
  have hint : IntegrableOn (fun w => A w - B w) (Ioi p) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hneg (tendsto_logF hn)
  have hdom : IntegrableOn (fun w => -(A w - B w)) (Ioi p) := hint.neg
  refine Integrable.mono' hdom (measurable_kern n m).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg n m (hpos w hw))]
  have h1 : kern n m w ≤ B w :=
    Finset.single_le_sum (f := fun m => kern n m w) (fun m _ => kern_nonneg n m (hpos w hw)) hm
  linarith [hAle w hw]

/-- **Hazard-rate bound**: `k_m(x) ≤ m Γ_m(x)` for `1 ≤ m ≤ n - 2` and `x ≥ 0`. -/
theorem kern_le_mul_Gam {n m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ n - 2) {x : ℝ} (hx : 0 ≤ x) :
    kern n m x ≤ m * Gam n m x := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · subst h0
    have hk : kern n m 0 = 0 := by simp [kern]
    rw [hk]
    exact mul_nonneg hmr.le (Gam_nonneg n m le_rfl)
  have hn : 1 ≤ n := by omega
  have hmn : m ≤ n := by omega
  have hI := integrableOn_kern hn (Finset.mem_Icc.mpr ⟨hm1, hm2⟩) hx
  have hmono := chi_mono (n := n) (m := m) hmn
  have ha : -(m : ℝ) < 0 := by linarith
  set C := kern n m x * exp (m * x) with hC
  have hgI : IntegrableOn (fun w : ℝ => C * exp (-(m : ℝ) * w)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi ha x).const_mul C
  have hle : ∫ w in Ioi x, C * exp (-(m : ℝ) * w) ≤ ∫ w in Ioi x, kern n m w := by
    refine setIntegral_mono_on hgI hI measurableSet_Ioi fun w hw => ?_
    have hw0 : (0 : ℝ) < w := lt_trans hxpos hw
    have h := hmono (mem_Ioi.mpr hxpos) (mem_Ioi.mpr hw0) (le_of_lt hw)
    simp only at h
    have e : exp (-(m : ℝ) * w) * exp (m * w) = 1 := by rw [← exp_add]; simp
    calc C * exp (-(m : ℝ) * w) = exp (-(m : ℝ) * w) * (exp (m * x) * kern n m x) := by rw [hC]; ring
      _ ≤ exp (-(m : ℝ) * w) * (exp (m * w) * kern n m w) :=
          mul_le_mul_of_nonneg_left h (exp_pos _).le
      _ = kern n m w := by rw [← mul_assoc, e, one_mul]
  have hval : ∫ w in Ioi x, C * exp (-(m : ℝ) * w) = kern n m x / m := by
    rw [integral_const_mul, integral_exp_mul_Ioi ha x, hC]
    have e : exp (m * x) * exp (-(m : ℝ) * x) = 1 := by rw [← exp_add]; simp
    rw [neg_div_neg_eq, ← mul_div_assoc, mul_assoc, e, mul_one]
  rw [hval] at hle
  have : kern n m x / m ≤ Gam n m x := hle
  rw [div_le_iff₀ hmr] at this
  linarith

end MatrixIneq
