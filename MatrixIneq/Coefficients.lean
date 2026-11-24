import MatrixIneq.Kernel

/-!
# Step 2: the certificate coefficients and the total identity

For `p ≥ 0` let

* `Gam n m p = ∫_{w > p} kern n m w`  (`1 ≤ m ≤ n - 2`),
* `Gam0 n p = ∫_{w > p} (kern n 0 w - 1) / 2`.

Results:

* `kern_identity`: the kernels add up to the logarithmic derivative of `1 + s + ⋯ + s^(n-1)` at `s = e^{-w}`;
* `total_Gam`: `(n-1) Γ_0(p) - ∑_{m=1}^{n-2} Γ_m(p) = - log (∑_{k<n} e^{-kp})`;
* `coef n m s`: the coefficient functions for every diagonal value `s ≥ 0` (through `|log s|`), with
  `coef_nonneg`, `coef_zero_nonpos`, `coef_total`;
* `norm_one_sub_mul_le`: the rescaling inequality used to pass from diagonal values in `(0, 1]` to all `s ≥ 0`.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-! ### The kernel sum identity -/

theorem sum_range_succ_cast (n : ℕ) : ∑ j ∈ range n, ((j + 1 : ℕ) : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

theorem sum_range_sinh (n : ℕ) (w : ℝ) (hw : 0 < w) :
    ∑ j ∈ range n, sinh ((j + 1 : ℕ) * w)
      = (exp w * (exp w ^ n - 1) / (exp w - 1) - (exp w)⁻¹ * ((exp w)⁻¹ ^ n - 1) / ((exp w)⁻¹ - 1)) / 2 := by
  have hx : exp w ≠ 1 := by
    have : (1 : ℝ) < exp w := one_lt_exp_iff.mpr hw
    exact this.ne'
  have hx' : (exp w)⁻¹ ≠ 1 := by
    intro h; exact hx (inv_eq_one.mp h)
  have e : ∀ j : ℕ, sinh ((j + 1 : ℕ) * w) = (exp w * exp w ^ j - (exp w)⁻¹ * (exp w)⁻¹ ^ j) / 2 := by
    intro j
    rw [sinh_eq, show -(((j + 1 : ℕ) : ℝ) * w) = ((j + 1 : ℕ) : ℝ) * (-w) by ring,
      exp_nat_mul, exp_nat_mul, exp_neg, pow_succ', pow_succ']
  simp only [e]
  rw [← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum, geom_sum_eq hx, geom_sum_eq hx']
  ring

theorem sum_range_kern (n : ℕ) (w : ℝ) :
    ∑ m ∈ range n, kern n m w
      = (∑ j ∈ range n, sinh ((j + 1 : ℕ) * w) - (n * (n + 1) / 2 : ℝ) * sinh w) / (cosh (n * w) - 1) := by
  set g : ℕ → ℝ := fun j => (sinh ((j + 1 : ℕ) * w) - ((j + 1 : ℕ) : ℝ) * sinh w) / (cosh (n * w) - 1) with hg
  have h1 : ∑ m ∈ range n, kern n m w = ∑ m ∈ range n, g (n - 1 - m) := by
    refine sum_congr rfl fun m hm => ?_
    have hm' : m < n := mem_range.mp hm
    have : n - m = n - 1 - m + 1 := by omega
    simp only [hg, kern, this]
  rw [h1, sum_range_reflect g n]
  simp only [hg]
  rw [← sum_div, sum_sub_distrib, ← sum_mul, sum_range_succ_cast]

theorem sum_Icc_kern {n : ℕ} (hn : 1 ≤ n) (w : ℝ) :
    ∑ m ∈ Icc 1 (n - 2), kern n m w = ∑ m ∈ range n, kern n m w - kern n 0 w := by
  have h0 : (0 : ℕ) ∈ range n := Finset.mem_range.mpr hn
  rw [← sum_erase_eq_sub h0]
  refine sum_subset ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [mem_erase, Finset.mem_range]
    omega
  · intro m hm hm'
    rw [mem_erase, Finset.mem_range] at hm
    rw [Finset.mem_Icc] at hm'
    have : m = n - 1 := by omega
    rw [this]; exact kern_pred n hn w

/-- The kernels add up to a logarithmic derivative. -/
theorem kern_identity {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw : 0 < w) :
    ((n : ℝ) - 1) * ((kern n 0 w - 1) / 2) - ∑ m ∈ Icc 1 (n - 2), kern n m w
      = n / (exp (n * w) - 1) - 1 / (exp w - 1) := by
  rw [sum_Icc_kern hn, sum_range_kern, sum_range_sinh n w hw]
  have hk0 : kern n 0 w = (sinh (n * w) - n * sinh w) / (cosh (n * w) - 1) := by simp [kern]
  rw [hk0]
  set x := exp w with hx
  have hxn : exp (n * w) = x ^ n := exp_nat_mul w n
  set y := x ^ n with hy
  have hx1 : 1 < x := one_lt_exp_iff.mpr hw
  have hy1 : 1 < y := one_lt_pow₀ hx1 (by omega)
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc : cosh (n * w) - 1 = (y - 1) ^ 2 / (2 * y) := by
    rw [cosh_eq, exp_neg, hxn]; field_simp; ring
  have hs : sinh w = (x ^ 2 - 1) / (2 * x) := by
    rw [sinh_eq, exp_neg, ← hx]; field_simp
  have hsn : sinh (n * w) = (y ^ 2 - 1) / (2 * y) := by
    rw [sinh_eq, exp_neg, hxn]; field_simp
  have hinv : x⁻¹ ^ n = y⁻¹ := by rw [inv_pow]
  rw [hc, hs, hsn, hxn, hinv]
  have h1 : x - 1 ≠ 0 := by linarith
  have h2 : y - 1 ≠ 0 := by linarith
  have h3 : x⁻¹ - 1 ≠ 0 := by
    have : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx1
    linarith
  have hxne : x ≠ 0 := hx0.ne'
  have hyne : y ≠ 0 := hy0.ne'
  have h4 : (1 : ℝ) - x ≠ 0 := by linarith
  have e3 : x⁻¹ * (y⁻¹ - 1) / (x⁻¹ - 1) = (y - 1) / (y * (x - 1)) := by
    rw [show x⁻¹ - 1 = (1 - x) / x by field_simp, show y⁻¹ - 1 = (1 - y) / y by field_simp]
    rw [div_eq_div_iff (div_ne_zero h4 hxne) (mul_ne_zero hyne h1)]
    field_simp
    ring
  rw [e3]
  field_simp
  ring

/-! ### The function `log F_n (e^{-w})` -/

/-- `logF n w = log (∑_{k<n} e^{-k w})`. -/
noncomputable def logF (n : ℕ) (w : ℝ) : ℝ := log (∑ k ∈ range n, exp (-(k * w)))

theorem sumF_pos {n : ℕ} (hn : 1 ≤ n) (w : ℝ) : 0 < ∑ k ∈ range n, exp (-(k * w)) :=
  sum_pos (fun k _ => exp_pos _) (nonempty_range_iff.mpr (by omega))

theorem continuous_logF {n : ℕ} (hn : 1 ≤ n) : Continuous (logF n) := by
  unfold logF
  exact Continuous.log (by fun_prop) fun w => (sumF_pos hn w).ne'

theorem sumF_eq {n : ℕ} {w : ℝ} (hw : 0 < w) :
    ∑ k ∈ range n, exp (-(k * w)) = (1 - exp (-(n * w))) / (1 - exp (-w)) := by
  have hx : exp (-w) ≠ 1 := by
    have : exp (-w) < 1 := exp_lt_one_iff.mpr (by linarith)
    exact this.ne
  have e : ∀ k : ℕ, exp (-(k * w)) = exp (-w) ^ k := by
    intro k; rw [← exp_nat_mul]; congr 1; ring
  simp only [e]
  rw [geom_sum_eq hx, ← e n]
  rw [div_eq_div_iff (sub_ne_zero.mpr hx) (sub_ne_zero.mpr (Ne.symm hx))]
  ring

theorem hasDerivAt_logF {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw : 0 < w) :
    HasDerivAt (logF n) (n / (exp (n * w) - 1) - 1 / (exp w - 1)) w := by
  have h1 : ∀ c : ℝ, 0 < c → ∀ v : ℝ, 0 < v → 0 < 1 - exp (-(c * v)) := by
    intro c hc v hv
    have : exp (-(c * v)) < 1 := exp_lt_one_iff.mpr (by nlinarith [mul_pos hc hv])
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ c : ℝ, 0 < c →
      HasDerivAt (fun v : ℝ => log (1 - exp (-(c * v)))) (c / (exp (c * w) - 1)) w := by
    intro c hc
    have hinner : HasDerivAt (fun v : ℝ => 1 - exp (-(c * v))) (c * exp (-(c * w))) w := by
      have h0 : HasDerivAt (fun v : ℝ => -(c * v)) (-c) w := by
        have h := hasDerivAt_mul_const (-c) (x := w)
        have e : (fun v : ℝ => -(c * v)) = fun v : ℝ => v * -c := by funext v; ring
        rw [e]; exact h
      have := h0.exp.const_sub 1
      convert this using 1
      ring
    have := hinner.log (h1 c hc w hw).ne'
    convert this using 1
    have hE : exp (c * w) ≠ 0 := (exp_pos _).ne'
    have hE1 : exp (c * w) - 1 ≠ 0 := by
      have : 1 < exp (c * w) := one_lt_exp_iff.mpr (mul_pos hc hw)
      linarith
    rw [exp_neg]
    field_simp
  have hG := (hd n hn0).sub (hd 1 one_pos)
  simp only [one_mul] at hG
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hw] with v hv
  have hv' : 0 < v := hv
  simp only [logF, Pi.sub_apply]
  rw [sumF_eq hv', log_div (h1 n hn0 v hv').ne' (by simpa using (h1 1 one_pos v hv').ne')]

theorem tendsto_logF {n : ℕ} (hn : 1 ≤ n) : Tendsto (logF n) atTop (𝓝 0) := by
  have hsum : Tendsto (fun w : ℝ => ∑ k ∈ range n, exp (-(k * w))) atTop
      (𝓝 (∑ k ∈ range n, if k = 0 then (1 : ℝ) else 0)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false]
      have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hk0)
  have h1 : (∑ k ∈ range n, if k = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_ite_eq' (range n) 0 (fun _ => (1 : ℝ))]
    simp [Finset.mem_range]; omega
  rw [h1] at hsum
  have := (continuousAt_log (one_ne_zero)).tendsto.comp hsum
  rw [log_one] at this
  exact this

/-! ### The coefficients as tail integrals -/

/-- `Γ_m(p) = ∫_{w > p} kern n m w`. -/
noncomputable def Gam (n m : ℕ) (p : ℝ) : ℝ := ∫ w in Ioi p, kern n m w

/-- `Γ_0(p) = ∫_{w > p} (kern n 0 w - 1) / 2`. -/
noncomputable def Gam0 (n : ℕ) (p : ℝ) : ℝ := ∫ w in Ioi p, (kern n 0 w - 1) / 2

theorem Gam_nonneg (n m : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ Gam n m p :=
  setIntegral_nonneg measurableSet_Ioi fun w hw => kern_nonneg n m (hp.trans (le_of_lt hw))

theorem one_sub_exp_le (n : ℕ) {w : ℝ} (hw : 0 ≤ w) : 1 - exp (-(n * w)) ≤ n * sinh w := by
  have hb : 1 - exp (-w) ≤ sinh w := by
    rw [sinh_eq]
    have h1 := add_one_le_exp w
    have h2 := add_one_le_exp (-w)
    linarith
  have hb0 : 0 ≤ 1 - exp (-w) := by
    have : exp (-w) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    linarith
  induction n with
  | zero => simp
  | succ n ih =>
    have ha : exp (-(n * w)) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have ha0 : 0 < exp (-(n * w)) := exp_pos _
    have e : exp (-(((n + 1 : ℕ) : ℝ) * w)) = exp (-(n * w)) * exp (-w) := by
      rw [← exp_add]; congr 1; push_cast; ring
    rw [e]; push_cast
    nlinarith

theorem kern_zero_le_one (n : ℕ) {w : ℝ} (hw : 0 ≤ w) : kern n 0 w ≤ 1 := by
  have hk : kern n 0 w = (sinh (n * w) - n * sinh w) / (cosh (n * w) - 1) := by simp [kern]
  rw [hk]
  by_cases h : cosh (n * w) - 1 = 0
  · rw [h, div_zero]; exact zero_le_one
  · have hpos : 0 < cosh (n * w) - 1 := lt_of_le_of_ne (sub_nonneg.mpr (one_le_cosh _)) (Ne.symm h)
    rw [div_le_one hpos]
    have h1 := one_sub_exp_le n hw
    have h2 := cosh_sub_sinh (n * w)
    linarith

theorem Gam0_nonpos (n : ℕ) {p : ℝ} (hp : 0 ≤ p) : Gam0 n p ≤ 0 :=
  setIntegral_nonpos measurableSet_Ioi fun w hw => by
    have := kern_zero_le_one n (hp.trans (le_of_lt hw))
    linarith

theorem measurable_kern (n m : ℕ) : Measurable (kern n m) := by
  unfold kern
  fun_prop

/-- **The total identity**: `(n-1) Γ_0(p) - ∑_{m=1}^{n-2} Γ_m(p) = - log (∑_{k<n} e^{-kp})`. -/
theorem total_Gam {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    ((n : ℝ) - 1) * Gam0 n p - ∑ m ∈ Icc 1 (n - 2), Gam n m p = -logF n p := by
  set A : ℝ → ℝ := fun w => ((n : ℝ) - 1) * ((kern n 0 w - 1) / 2) with hA
  set B : ℝ → ℝ := fun w => ∑ m ∈ Icc 1 (n - 2), kern n m w with hB
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : ∀ w ∈ Ioi p, 0 ≤ w := fun w hw => hp.trans (le_of_lt hw)
  have hAle : ∀ w ∈ Ioi p, A w ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos hn1 (by have := kern_zero_le_one n (hpos w hw); linarith)
  have hBge : ∀ w ∈ Ioi p, 0 ≤ B w := fun w hw => sum_nonneg fun m _ => kern_nonneg n m (hpos w hw)
  have hderiv : ∀ w ∈ Ioi p, HasDerivAt (logF n) (A w - B w) w := by
    intro w hw
    have hw0 : 0 < w := lt_of_le_of_lt hp hw
    have := hasDerivAt_logF hn hw0
    rwa [← kern_identity hn hw0] at this
  have hneg : ∀ w ∈ Ioi p, A w - B w ≤ 0 := fun w hw => by linarith [hAle w hw, hBge w hw]
  have hcont : ContinuousWithinAt (logF n) (Ici p) p := (continuous_logF hn).continuousWithinAt
  have hint : IntegrableOn (fun w => A w - B w) (Ioi p) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hneg (tendsto_logF hn)
  have heq : ∫ w in Ioi p, (A w - B w) = 0 - logF n p :=
    integral_Ioi_of_hasDerivAt_of_nonpos hcont hderiv hneg (tendsto_logF hn)
  have hdom : IntegrableOn (fun w => -(A w - B w)) (Ioi p) := hint.neg
  have hAint : IntegrableOn A (Ioi p) := by
    refine Integrable.mono' hdom ?_ ?_
    · exact ((measurable_const.mul (((measurable_kern n 0).sub measurable_const).div_const 2))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_of_nonpos (hAle w hw)]
      linarith [hBge w hw]
  have hkint : ∀ m ∈ Finset.Icc 1 (n - 2), IntegrableOn (kern n m) (Ioi p) := by
    intro m hm
    refine Integrable.mono' hdom (measurable_kern n m).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg n m (hpos w hw))]
    have h1 : kern n m w ≤ B w :=
      single_le_sum (f := fun m => kern n m w) (fun m _ => kern_nonneg n m (hpos w hw)) hm
    linarith [hAle w hw]
  have hBint : IntegrableOn B (Ioi p) := integrable_finsetSum _ hkint
  have e1 : ∫ w in Ioi p, (A w - B w) = (∫ w in Ioi p, A w) - ∫ w in Ioi p, B w :=
    integral_sub hAint hBint
  have e2 : ∫ w in Ioi p, A w = ((n : ℝ) - 1) * Gam0 n p := by
    simp only [hA, Gam0]; exact integral_const_mul _ _
  have e3 : ∫ w in Ioi p, B w = ∑ m ∈ Icc 1 (n - 2), Gam n m p := by
    simp only [hB, Gam]; exact MeasureTheory.integral_finsetSum _ hkint
  rw [e1, e2, e3] at heq
  linarith

/-- The coefficient functions of the Fejér certificate, for all `s ≥ 0`:
`s = e^{-p}` or `s = e^{p}` with `p = |log s|`; for `s > 1` the constant term is shifted by `-log s`. -/
noncomputable def coef (n m : ℕ) (s : ℝ) : ℝ :=
  if s = 0 then 0 else if m = 0 then Gam0 n |log s| - max (log s) 0 else Gam n m |log s|

theorem coef_nonneg (n : ℕ) {m : ℕ} (hm : 1 ≤ m) (s : ℝ) : 0 ≤ coef n m s := by
  unfold coef
  split_ifs with h1 h2
  · exact le_rfl
  · omega
  · exact Gam_nonneg n m (abs_nonneg _)

theorem coef_zero_nonpos (n : ℕ) (s : ℝ) : coef n 0 s ≤ 0 := by
  unfold coef
  by_cases h1 : s = 0
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    have := Gam0_nonpos n (abs_nonneg (log s))
    have := le_max_right (log s) 0
    linarith

theorem log_sum_pow_zero (n : ℕ) : log (∑ k ∈ range n, (0 : ℝ) ^ k) = 0 := by
  cases n with
  | zero => simp
  | succ n => rw [sum_range_succ']; simp

theorem sum_exp_reflect (n : ℕ) (a : ℝ) :
    ∑ k ∈ range n, exp (k * a) = exp ((n - 1 : ℝ) * a) * ∑ k ∈ range n, exp (-(k * a)) := by
  rw [mul_sum, ← sum_range_reflect (fun k : ℕ => exp (k * a)) n]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k < n := Finset.mem_range.mp hk
  rw [← exp_add]
  congr 1
  have : ((n - 1 - k : ℕ) : ℝ) = (n : ℝ) - 1 - k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  rw [this]; ring

theorem coef_total {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : 0 ≤ s) :
    -log (∑ k ∈ range n, s ^ k) ≤ ((n : ℝ) - 1) * coef n 0 s - ∑ m ∈ Finset.Icc 1 (n - 2), coef n m s := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have hc : ∀ m, coef n m 0 = 0 := fun m => by simp [coef]
    rw [log_sum_pow_zero]
    simp [hc]
  · have hs0 : s ≠ 0 := hpos.ne'
    have hc0 : coef n 0 s = Gam0 n |log s| - max (log s) 0 := by simp [coef, hs0]
    have hcm : ∀ m ∈ Finset.Icc 1 (n - 2), coef n m s = Gam n m |log s| := by
      intro m hm
      have : m ≠ 0 := by rw [Finset.mem_Icc] at hm; omega
      simp [coef, hs0, this]
    rw [hc0, sum_congr rfl hcm]
    have htot := total_Gam hn (abs_nonneg (log s))
    have hpow : ∀ k : ℕ, s ^ k = exp (k * log s) := by
      intro k; rw [exp_nat_mul, exp_log hpos]
    simp only [hpow]
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rcases le_total (log s) 0 with ha | ha
    · have e : ∑ k ∈ range n, exp (k * log s) = ∑ k ∈ range n, exp (-(k * |log s|)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [abs_of_nonpos ha]; congr 1; ring
      rw [e, max_eq_right ha]
      have : logF n |log s| = log (∑ k ∈ range n, exp (-(k * |log s|))) := rfl
      linarith
    · have e : ∑ k ∈ range n, exp (k * log s)
          = exp ((n - 1 : ℝ) * |log s|) * ∑ k ∈ range n, exp (-(k * |log s|)) := by
        rw [abs_of_nonneg ha]; exact sum_exp_reflect n (log s)
      rw [e, log_mul (exp_pos _).ne' (sumF_pos hn _).ne', log_exp, max_eq_left ha]
      have : logF n |log s| = log (∑ k ∈ range n, exp (-(k * |log s|))) := rfl
      rw [abs_of_nonneg ha] at *
      linarith

theorem normSq_one_sub (r : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - (r : ℂ) * z‖ ^ 2 = 1 - 2 * r * z.re + r ^ 2 := by
  have h1 : z.re * z.re + z.im * z.im = 1 := by
    have := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at this
    simpa using this
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp
  nlinarith

theorem norm_one_sub_mul_le {K c : ℝ} (hK : 1 ≤ K) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖1 - ((K * c : ℝ) : ℂ) * z‖ ≤ K * ‖1 - ((c / K : ℝ) : ℂ) * z‖ := by
  have hK0 : 0 < K := by linarith
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, normSq_one_sub _ hz, normSq_one_sub _ hz]
  have e : K ^ 2 * (1 - 2 * (c / K) * z.re + (c / K) ^ 2) = K ^ 2 - 2 * (K * c) * z.re + c ^ 2 := by
    field_simp
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sub_nonneg.mpr hc1), mul_nonneg hc0 (sub_nonneg.mpr hc1),
    mul_nonneg (sub_nonneg.mpr hK) hc0]


end MatrixIneq
