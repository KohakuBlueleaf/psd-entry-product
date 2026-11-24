import MatrixIneq.Tail

/-!
# Step 4: the τ-kernel, a positive semidefinite coefficient kernel with a provable pair inequality

For `0 ≤ p ≤ q` let `Ktau n m p q = Γ_m(q) + ½ ∫_p^q k_m(u) e^{-m(q-u)/2} du`.

* `tauStar`: the pair inequality
  `-log |1 - e^{-(p+q)/2} z| ≥ (Γ_0(p)+Γ_0(q))/2 + ∑_m Ktau n m p q · Re (z^m)` on `|z| = 1`,
  by monotonicity in `p` (the derivative is a Poisson-smoothed form of the diagonal kernel inequality).
* `tauK_psd`: the symmetric extension of `Ktau` is a nonnegative mixture of the rank-one kernels
  `e^{-m max(p,τ)/2} e^{-m max(q,τ)/2}`, with weight `χ_m'(τ) ≥ 0`.

A written version of the proof is in `docs/PROOF.md`.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-! ### Minimum principle for the real part -/

theorem re_nonneg_of_circle {F : ℂ → ℂ} (hF : ∀ z : ℂ, ‖z‖ ≤ 1 → DifferentiableAt ℂ F z)
    (h : ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (F z).re) (z : ℂ) (hz : ‖z‖ ≤ 1) : 0 ≤ (F z).re := by
  set g : ℂ → ℂ := fun w => Complex.exp (-(F w)) with hg
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall 0 1 := closure_ball (0 : ℂ) one_ne_zero
  have hd : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    intro w hw
    rw [hcl, mem_closedBall_zero_iff] at hw
    exact ((hF w hw).neg.cexp).differentiableWithinAt
  have key : ‖g z‖ ≤ 1 := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.ball (0 : ℂ) 1)
      Metric.isBounded_ball hd ?_ ?_
    · intro w hw
      rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere_zero_iff_norm] at hw
      simp only [hg, Complex.norm_exp, Complex.neg_re]
      exact Real.exp_le_one_iff.mpr (by linarith [h w hw])
    · rw [hcl, mem_closedBall_zero_iff]; exact hz
  simp only [hg, Complex.norm_exp, Complex.neg_re] at key
  have := Real.exp_le_one_iff.mp key
  linarith

/-- `Re ((1 + e^{-w} e^{iθ}) / (1 - e^{-w} e^{iθ})) = sinh w / (cosh w - cos θ)`. -/
theorem re_mobius {w : ℝ} (hw : 0 < w) (θ : ℝ) :
    ((1 + (Real.exp (-w) : ℂ) * Complex.exp (θ * Complex.I))
      / (1 - (Real.exp (-w) : ℂ) * Complex.exp (θ * Complex.I))).re = sinh w / (cosh w - cos θ) := by
  set t := Real.exp (-w) with ht
  have ht0 : 0 < t := exp_pos _
  have hre : ((t : ℂ) * Complex.exp (θ * Complex.I)).re = t * cos θ := by
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : ((t : ℂ) * Complex.exp (θ * Complex.I)).im = t * sin θ := by
    rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hcw : 1 < cosh w := Real.one_lt_cosh.mpr hw.ne'
  have hD : 0 < cosh w - cos θ := by linarith [Real.cos_le_one θ]
  have hq : (1 - t * cos θ) * (1 - t * cos θ) + (-(t * sin θ)) * (-(t * sin θ)) = 2 * t * (cosh w - cos θ) := by
    have := qf_eq (cos θ) w
    unfold qf at this
    rw [← ht] at this
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im,
    hre, him, zero_add, zero_sub]
  rw [hq, ← add_div]
  have hs : sinh w = (1 - t ^ 2) / (2 * t) := by
    rw [sinh_eq, ht, exp_neg]
    have : exp w ≠ 0 := (exp_pos w).ne'
    field_simp
  rw [hs]
  have h2 : (1 + t * cos θ) * (1 - t * cos θ) + t * sin θ * -(t * sin θ) = 1 - t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h2]
  field_simp

/-- **Poisson-smoothed kernel inequality.** For `x > 0`, `s ≥ 0`:
`(k_0(x) - 1)/2 + ∑_m k_m(x) e^{-m s} cos mθ ≤ (P_{x+s}(θ) - 1)/2`. -/
theorem kern_poisson_smooth_le {n : ℕ} (hn : 1 ≤ n) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s) (θ : ℝ) :
    (kern n 0 x - 1) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), kern n m x * exp (-(m * s)) * cos (m * θ)
      ≤ (sinh (x + s) / (cosh (x + s) - cos θ) - 1) / 2 := by
  set r := Real.exp (-x) with hr
  have hr0 : 0 < r := exp_pos _
  have hr1 : r < 1 := exp_lt_one_iff.mpr (by linarith)
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun ζ => (1 + (r : ℂ) * ζ) / (1 - (r : ℂ) * ζ) / 2 - (kern n 0 x : ℂ) / 2
      - ∑ m ∈ Finset.Icc 1 (n - 2), (kern n m x : ℂ) * ζ ^ m := ⟨_, rfl⟩
  have hne : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → (1 - (r : ℂ) * ζ) ≠ 0 := by
    intro ζ hζ h0
    have h1 : (r : ℂ) * ζ = 1 := by linear_combination -h0
    have h2 : ‖(r : ℂ) * ζ‖ = 1 := by rw [h1]; simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le] at h2
    nlinarith [norm_nonneg ζ]
  have hdiff : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → DifferentiableAt ℂ F ζ := by
    intro ζ hζ
    have ha : DifferentiableAt ℂ (fun ζ : ℂ => 1 + (r : ℂ) * ζ) ζ := by fun_prop
    have hb : DifferentiableAt ℂ (fun ζ : ℂ => 1 - (r : ℂ) * ζ) ζ := by fun_prop
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => (1 + (r : ℂ) * ζ) / (1 - (r : ℂ) * ζ)) ζ :=
      ha.div hb (hne ζ hζ)
    have h3 : DifferentiableAt ℂ (fun ζ : ℂ => ∑ m ∈ Finset.Icc 1 (n - 2), (kern n m x : ℂ) * ζ ^ m) ζ := by
      fun_prop
    rw [hFdef]
    exact ((h1.div_const 2).sub (differentiableAt_const ((kern n 0 x : ℂ) / 2))).sub h3
  have hFre : ∀ (ρ φ : ℝ), 0 < x + ρ → exp (-ρ) ≤ 1 →
      (F ((Real.exp (-ρ) : ℂ) * Complex.exp (φ * Complex.I))).re
        = sinh (x + ρ) / (cosh (x + ρ) - cos φ) / 2 - kern n 0 x / 2
          - ∑ m ∈ Finset.Icc 1 (n - 2), kern n m x * exp (-(m * ρ)) * cos (m * φ) := by
    intro ρ φ hxρ _
    have hmob := re_mobius hxρ φ
    have e1 : (r : ℂ) * ((Real.exp (-ρ) : ℂ) * Complex.exp (φ * Complex.I))
        = (Real.exp (-(x + ρ)) : ℂ) * Complex.exp (φ * Complex.I) := by
      rw [← mul_assoc, ← Complex.ofReal_mul, hr, ← Real.exp_add]; congr 3; ring
    rw [hFdef]
    simp only [e1, Complex.sub_re, Complex.re_sum]
    have e2 : ((1 + (Real.exp (-(x + ρ)) : ℂ) * Complex.exp (φ * Complex.I))
        / (1 - (Real.exp (-(x + ρ)) : ℂ) * Complex.exp (φ * Complex.I)) / 2).re
        = sinh (x + ρ) / (cosh (x + ρ) - cos φ) / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, hmob]
    have e3 : ((kern n 0 x : ℂ) / 2).re = kern n 0 x / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.div_ofReal_re, Complex.ofReal_re]
    rw [e2, e3]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.re_ofReal_mul, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul, re_pow_exp,
      ← Real.exp_nat_mul]
    have : (m : ℝ) * -ρ = -(m * ρ) := by ring
    rw [this]; ring
  have hcirc : ∀ ζ : ℂ, ‖ζ‖ = 1 → 0 ≤ (F ζ).re := by
    intro ζ hζ
    obtain ⟨φ, rfl⟩ := (Complex.norm_eq_one_iff ζ).mp hζ
    have h := hFre 0 φ (by linarith) (by simp)
    simp only [neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul, add_zero, mul_zero, mul_one] at h
    rw [h]
    have := kern_poisson_le hn hx φ
    linarith
  have hin : ‖(Real.exp (-s) : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (exp_pos _).le]
    exact exp_le_one_iff.mpr (by linarith)
  have hmain := re_nonneg_of_circle hdiff hcirc _ hin
  rw [hFre s θ (by linarith) (exp_le_one_iff.mpr (by linarith))] at hmain
  linarith

/-! ### The kernel `Ktau` and the pair inequality -/

/-- The integrand `k_m(u) e^{-m (q - u)/2}`. -/
noncomputable def hK (n m : ℕ) (q u : ℝ) : ℝ := kern n m u * exp (-(m * (q - u) / 2))

/-- `Ktau n m x q = Γ_m(q) + ½ ∫_x^q k_m(u) e^{-m(q-u)/2} du` (used for `x ≤ q`). -/
noncomputable def Ktau (n m : ℕ) (x q : ℝ) : ℝ := Gam n m q + 1 / 2 * ∫ u in x..q, hK n m q u

theorem Ktau_self (n m : ℕ) (q : ℝ) : Ktau n m q q = Gam n m q := by simp [Ktau]

theorem kern_intervalIntegrable {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) : IntervalIntegrable (kern n m) volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    (((integrableOn_kern_parts hn (le_refl (0 : ℝ))).2 m hm).mono_set
      (fun _ hu => lt_of_le_of_lt ha hu.1))

theorem hK_intervalIntegrable {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) (q : ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (hK n m q) volume a b := by
  unfold hK
  exact (kern_intervalIntegrable hn hm ha hab).mul_continuousOn (by fun_prop)

theorem Ktau_continuousOn {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (fun x => Ktau n m x q) (Icc 0 q) := by
  have hint : IntervalIntegrable (hK n m q) volume 0 q := hK_intervalIntegrable hn hm q le_rfl hq
  have h := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) left_mem_uIcc
  rw [uIcc_of_le hq] at h
  have e : ∀ x ∈ Icc 0 q, Ktau n m x q
      = Gam n m q + 1 / 2 * ((∫ u in (0 : ℝ)..q, hK n m q u) - ∫ u in (0 : ℝ)..x, hK n m q u) := by
    intro x hx
    unfold Ktau
    rw [intervalIntegral.integral_interval_sub_left hint (hK_intervalIntegrable hn hm q le_rfl hx.1)]
  exact (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub h))).congr e

theorem Ktau_hasDerivAt {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {x q : ℝ} (hx : 0 < x)
    (hxq : x ≤ q) : HasDerivAt (fun x => Ktau n m x q) (1 / 2 * -(hK n m q x)) x := by
  have hint : IntervalIntegrable (hK n m q) volume x q := hK_intervalIntegrable hn hm q hx.le hxq
  have hmeas : Measurable (hK n m q) := by
    unfold hK; exact (measurable_kern n m).mul (by fun_prop)
  have hc : ContinuousAt (hK n m q) x := by
    unfold hK; exact (continuousAt_kern (by omega) m hx).mul (by fun_prop)
  have h := intervalIntegral.integral_hasDerivAt_left hint
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter hc
  exact (h.const_mul (1 / 2 : ℝ)).const_add (Gam n m q)

/-- The gap of the pair inequality at `z = e^{iθ}`, as a function of the smaller parameter `x`. -/
noncomputable def gapT (n : ℕ) (θ q x : ℝ) : ℝ :=
  -(1 / 2 * log (qf (cos θ) ((x + q) / 2))) -
    ((Gam0 n x + Gam0 n q) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), Ktau n m x q * cos (m * θ))

theorem gapT_continuousOn {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousOn (gapT n θ q) (Icc 0 q) := by
  obtain ⟨h0, -⟩ := integrableOn_kern_parts hn (le_refl (0 : ℝ))
  have hqf : Continuous (qf (cos θ)) := by unfold qf; fun_prop
  have hlog : ContinuousOn (fun x : ℝ => log (qf (cos θ) ((x + q) / 2))) (Icc 0 q) := by
    refine ContinuousOn.log (hqf.comp (by fun_prop)).continuousOn fun x hx => ?_
    exact (qf_pos (cos_le_one θ) (by linarith [hx.1] : 0 < (x + q) / 2)).ne'
  have hG0 : ContinuousOn (Gam0 n) (Icc 0 q) := tail_continuousOn h0 hq.le
  exact ContinuousOn.sub (ContinuousOn.neg (continuousOn_const.mul hlog))
    (ContinuousOn.add ((hG0.add continuousOn_const).div_const 2)
      (continuousOn_finsetSum _ fun m hm => (Ktau_continuousOn hn hm hq.le).mul continuousOn_const))

theorem gapT_deriv_nonpos {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) {q x : ℝ} (hx : 0 < x) (hxq : x < q) :
    ∃ E, HasDerivAt (gapT n θ q) E x ∧ E ≤ 0 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h0, -⟩ := integrableOn_kern_parts hn (le_refl (0 : ℝ))
  have hα : 0 < (x + q) / 2 := by linarith
  have hQ : 0 < qf (cos θ) ((x + q) / 2) := qf_pos (cos_le_one θ) hα
  have hin : HasDerivAt (fun x : ℝ => (x + q) / 2) (1 / 2) x := by
    simpa using ((hasDerivAt_id x).add_const q).div_const 2
  have hlog : HasDerivAt (fun x : ℝ => 1 / 2 * log (qf (cos θ) ((x + q) / 2)))
      ((exp (-((x + q) / 2)) * cos θ - exp (-((x + q) / 2)) ^ 2) / qf (cos θ) ((x + q) / 2) * (1 / 2)) x :=
    HasDerivAt.comp (h₂ := fun w : ℝ => 1 / 2 * log (qf (cos θ) w)) (h := fun x : ℝ => (x + q) / 2) x
      (hasDerivAt_half_log_qf (w := (x + q) / 2) hQ) hin
  have hG0 : HasDerivAt (Gam0 n) (-((kern n 0 x - 1) / 2)) x :=
    tail_hasDerivAt h0 (((measurable_kern n 0).sub measurable_const).div_const 2) hx
      (((continuousAt_kern hn1 0 hx).sub continuousAt_const).div_const 2)
  have hsum : HasDerivAt (fun x => ∑ m ∈ Finset.Icc 1 (n - 2), Ktau n m x q * cos (m * θ))
      (∑ m ∈ Finset.Icc 1 (n - 2), 1 / 2 * -(hK n m q x) * cos (m * θ)) x :=
    HasDerivAt.fun_sum fun m hm => (Ktau_hasDerivAt hn hm hx hxq.le).mul_const _
  refine ⟨_, hlog.neg.sub (((hG0.add_const (Gam0 n q)).div_const 2).add hsum), ?_⟩
  have hsm := kern_poisson_smooth_le hn1 hx (by linarith : (0 : ℝ) ≤ (q - x) / 2) θ
  have e0 : x + (q - x) / 2 = (x + q) / 2 := by ring
  rw [e0, poisson_eq hα (cos_le_one θ)] at hsm
  have hS : ∑ m ∈ Finset.Icc 1 (n - 2), 1 / 2 * -(hK n m q x) * cos (m * θ)
      = -(1 / 2) * ∑ m ∈ Finset.Icc 1 (n - 2), kern n m x * exp (-(m * ((q - x) / 2))) * cos (m * θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold hK
    have : (m : ℝ) * (q - x) / 2 = m * ((q - x) / 2) := by ring
    rw [this]; ring
  rw [hS]
  linarith

/-- **The pair inequality for the τ-kernel**, `0 ≤ p ≤ q`. -/
theorem tauStar {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * z‖ ≤
      Real.exp (-(harm ((Gam0 n p + Gam0 n q) / 2) (fun m => Ktau n m p q) (n - 2) z)) := by
  rcases hpq.eq_or_lt with rfl | hlt
  · have h := star_diag hn hp z hz
    have e1 : -(p + p) / 2 = -p := by ring
    have e2 : (Gam0 n p + Gam0 n p) / 2 = Gam0 n p := by ring
    have e3 : (fun m => Ktau n m p p) = fun m => Gam n m p := by
      funext m; exact Ktau_self n m p
    rw [e1, e2, e3]; exact h
  have hq : 0 < q := lt_of_le_of_lt hp hlt
  have hsq := normSq_one_sub (exp (-(p + q) / 2)) hz
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  rw [Complex.exp_ofReal_mul_I_re] at hsq
  have e1 : -(p + q) / 2 = -((p + q) / 2) := by ring
  have hqf : ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2
      = qf (cos θ) ((p + q) / 2) := by
    rw [hsq, e1]; unfold qf; ring
  have hanti : AntitoneOn (gapT n θ q) (Icc 0 q) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 q) (gapT_continuousOn hn θ hq) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨E, hE, -⟩ := gapT_deriv_nonpos hn θ hx.1 hx.2
      exact hE.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨E, hE, hE0⟩ := gapT_deriv_nonpos hn θ hx.1 hx.2
      rw [hE.deriv]; exact hE0
  have hdiag : 0 ≤ gapT n θ q q := by
    have h := harm_le hn hq.le θ (Or.inl hq.ne')
    unfold gapT
    simp only [Ktau_self]
    have e2 : (q + q) / 2 = q := by ring
    rw [e2]
    linarith
  have hgap : 0 ≤ gapT n θ q p := hdiag.trans (hanti ⟨hp, hpq⟩ ⟨hq.le, le_rfl⟩ hpq)
  have hharm : harm ((Gam0 n p + Gam0 n q) / 2) (fun m => Ktau n m p q) (n - 2)
        (Complex.exp (θ * Complex.I))
      = (Gam0 n p + Gam0 n q) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), Ktau n m p q * cos (m * θ) := by
    unfold harm; simp only [re_pow_exp]
  rw [hharm]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_pos _).le two_ne_zero).mp ?_
  rw [hqf, ← Real.exp_nat_mul]
  have hQ : 0 < qf (cos θ) ((p + q) / 2) := qf_pos (cos_le_one θ) (by linarith)
  unfold gapT at hgap
  calc qf (cos θ) ((p + q) / 2) = exp (log (qf (cos θ) ((p + q) / 2))) := (exp_log hQ).symm
    _ ≤ _ := exp_le_exp.mpr (by push_cast; linarith)

/-! ### `χ_m` and its regularity on `[0, ∞)` -/

/-- `χ_m(τ) = e^{m τ} k_m(τ)`. -/
noncomputable def chi (n m : ℕ) (τ : ℝ) : ℝ := exp (m * τ) * kern n m τ

theorem sinh_le_mul_cosh {y : ℝ} (hy : 0 ≤ y) : sinh y ≤ y * cosh y := by
  have hmono : MonotoneOn (fun y : ℝ => y * cosh y - sinh y) (Ici 0) := by
    have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * cosh y - sinh y) (1 * cosh x + x * sinh x - cosh x) x :=
      fun x => ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have := sinh_pos_iff.mpr hx
    have hx' : (0 : ℝ) < x := hx
    nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hy) hy
  simp only [zero_mul, sinh_zero, sub_zero] at this
  linarith

theorem kern_le_mul_self (n m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : kern n m τ ≤ (n - m : ℕ) * τ := by
  unfold kern
  set N : ℕ := n - m with hN
  have hNτ : (0 : ℝ) ≤ N * τ := by positivity
  by_cases h : cosh (n * τ) - 1 = 0
  · rw [h, div_zero]; exact hNτ
  · have hpos : 0 < cosh (n * τ) - 1 := lt_of_le_of_ne (sub_nonneg.mpr (one_le_cosh _)) (Ne.symm h)
    rw [div_le_iff₀ hpos]
    have h1 := sinh_le_mul_cosh hNτ
    have h2 : τ ≤ sinh τ := self_le_sinh_iff.mpr hτ
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n m
    have h3 : cosh (N * τ) ≤ cosh (n * τ) := by
      rw [cosh_le_cosh, abs_of_nonneg hNτ, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right hNn hτ
    have h4 : (N : ℝ) * τ * cosh (N * τ) ≤ N * τ * cosh (n * τ) := mul_le_mul_of_nonneg_left h3 hNτ
    have h5 : (N : ℝ) * τ ≤ N * sinh τ := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg N)
    nlinarith

theorem chi_zero (n m : ℕ) : chi n m 0 = 0 := by simp [chi, kern]

theorem chi_nonneg (n m : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) : 0 ≤ chi n m τ :=
  mul_nonneg (exp_pos _).le (kern_nonneg n m hτ)

theorem chi_continuousOn {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn (chi n m) (Icc a b) := by
  intro τ hτ
  rcases eq_or_lt_of_le (ha.trans hτ.1) with h0 | hpos
  · subst h0
    have hup : Tendsto (fun τ : ℝ => exp (m * τ) * ((n - m : ℕ) * τ)) (𝓝[Ici 0] 0) (𝓝 0) := by
      have hc : Continuous (fun τ : ℝ => exp (m * τ) * ((n - m : ℕ) * τ)) := by fun_prop
      have := hc.continuousAt.tendsto (x := 0)
      simp only [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h0' : Tendsto (chi n m) (𝓝[Ici 0] 0) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
      · exact eventually_nhdsWithin_of_forall fun τ hτ => chi_nonneg n m hτ
      · exact eventually_nhdsWithin_of_forall fun τ hτ =>
          mul_le_mul_of_nonneg_left (kern_le_mul_self n m hτ) (exp_pos _).le
    have hcw : ContinuousWithinAt (chi n m) (Ici 0) 0 := by
      unfold ContinuousWithinAt; rw [chi_zero]; exact h0'
    exact hcw.mono (fun x hx => mem_Ici.mpr (ha.trans hx.1))
  · have hE : Continuous (fun τ : ℝ => exp (m * τ)) := by fun_prop
    exact (hE.continuousAt.mul (continuousAt_kern hn m hpos)).continuousWithinAt

theorem chi_hasDerivAt {n m : ℕ} (hm : m ≤ n) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (chi n m) (deriv (chi n m) τ) τ ∧ 0 ≤ deriv (chi n m) τ := by
  obtain ⟨d, hd, hd0⟩ := hasDerivAt_chi (n := n) hm hτ
  have hd' : HasDerivAt (chi n m) d τ := hd
  rw [hd'.deriv]; exact ⟨hd', hd0⟩

theorem deriv_chi_intervalIntegrable {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (deriv (chi n m)) volume a b := by
  refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := chi n m) ?_ ?_ ?_
  · rw [uIcc_of_le hab]; exact chi_continuousOn hn m ha
  · intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact (chi_hasDerivAt hm (lt_of_le_of_lt ha hx.1)).1
  · intro x hx
    rw [min_eq_left hab, max_eq_right hab] at hx
    exact (chi_hasDerivAt hm (lt_of_le_of_lt ha hx.1)).2

/-- Integration by parts against an exponential. -/
theorem chi_byParts {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (lam : ℝ) :
    ∫ τ in a..b, deriv (chi n m) τ * exp (-(lam * τ))
      = chi n m b * exp (-(lam * b)) - chi n m a * exp (-(lam * a))
        + lam * ∫ τ in a..b, chi n m τ * exp (-(lam * τ)) := by
  have hE : Continuous (fun τ : ℝ => exp (-(lam * τ))) := by fun_prop
  have hcont := chi_continuousOn hn m (b := b) ha
  have hint1 := deriv_chi_intervalIntegrable hn hm ha hab
  have hint2 : IntervalIntegrable (fun τ => deriv (chi n m) τ * exp (-(lam * τ))) volume a b :=
    hint1.mul_continuousOn hE.continuousOn
  have hint3 : IntervalIntegrable (fun τ => chi n m τ * exp (-(lam * τ))) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcont.mul hE.continuousOn)
  have hder : ∀ x ∈ Ioo a b, HasDerivAt (fun τ => chi n m τ * exp (-(lam * τ)))
      (deriv (chi n m) x * exp (-(lam * x)) + -lam * (chi n m x * exp (-(lam * x)))) x := by
    intro x hx
    have h1 := (chi_hasDerivAt hm (lt_of_le_of_lt ha hx.1)).1
    have h2 : HasDerivAt (fun τ : ℝ => exp (-(lam * τ))) (exp (-(lam * x)) * -(lam * 1)) x :=
      ((hasDerivAt_id x).const_mul lam).neg.exp
    have h3 := h1.mul h2
    convert h3 using 1
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab (hcont.mul hE.continuousOn) hder
    (hint2.add (hint3.const_mul (-lam)))
  rw [intervalIntegral.integral_add hint2 (hint3.const_mul (-lam)), intervalIntegral.integral_const_mul] at hftc
  simp only [Pi.mul_apply] at hftc
  linarith

/-! ### The mixture representation and positive semidefiniteness -/

/-- `φ_τ(p) = e^{-m max(p, τ)/2}`. -/
noncomputable def phi (m : ℕ) (p τ : ℝ) : ℝ := exp (-(m * max p τ / 2))

theorem continuous_phi (m : ℕ) (p : ℝ) : Continuous (phi m p) := by
  unfold phi
  exact Real.continuous_exp.comp
    (((continuous_const.mul (continuous_const.max continuous_id)).div_const 2).neg)

/-- **Mixture representation** of the τ-kernel, for `0 ≤ p ≤ q ≤ P`. -/
theorem tauK_repr {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {p q P : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) (hqP : q ≤ P) :
    m * Ktau n m p q
      = (∫ τ in (0 : ℝ)..P, deriv (chi n m) τ * (phi m p τ * phi m q τ)) + (m * Gam n m P - kern n m P) := by
  have hn1 : 1 ≤ n := by omega
  have hmn : m ≤ n := by have := (Finset.mem_Icc.mp hm).2; omega
  have hq : 0 ≤ q := hp.trans hpq
  have hP : 0 ≤ P := hq.trans hqP
  have hcφ : Continuous (fun τ => phi m p τ * phi m q τ) := (continuous_phi m p).mul (continuous_phi m q)
  have hI : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      IntervalIntegrable (fun τ => deriv (chi n m) τ * (phi m p τ * phi m q τ)) volume a b :=
    fun ha hab => (deriv_chi_intervalIntegrable hn1 hmn ha hab).mul_continuousOn hcφ.continuousOn
  have hsplit : ∫ τ in (0 : ℝ)..P, deriv (chi n m) τ * (phi m p τ * phi m q τ)
      = (∫ τ in (0 : ℝ)..p, deriv (chi n m) τ * (phi m p τ * phi m q τ))
        + (∫ τ in p..q, deriv (chi n m) τ * (phi m p τ * phi m q τ))
        + ∫ τ in q..P, deriv (chi n m) τ * (phi m p τ * phi m q τ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hI le_rfl hp) (hI hp hpq),
      intervalIntegral.integral_add_adjacent_intervals (hI le_rfl hq) (hI hq hqP)]
  set Cp := exp (-(m * p / 2)) with hCp
  set Cq := exp (-(m * q / 2)) with hCq
  -- first piece
  have h1 : ∫ τ in (0 : ℝ)..p, deriv (chi n m) τ * (phi m p τ * phi m q τ) = Cp * Cq * chi n m p := by
    have e : ∀ τ ∈ uIcc (0 : ℝ) p, deriv (chi n m) τ * (phi m p τ * phi m q τ)
        = (Cp * Cq) * (deriv (chi n m) τ * exp (-((0 : ℝ) * τ))) := by
      intro τ hτ
      rw [uIcc_of_le hp] at hτ
      unfold phi
      rw [max_eq_left hτ.2, max_eq_left (hτ.2.trans hpq)]
      simp only [zero_mul, neg_zero, exp_zero, mul_one]
      ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
      chi_byParts hn1 hmn le_rfl hp 0]
    simp [chi_zero]
  -- second piece
  have h2 : ∫ τ in p..q, deriv (chi n m) τ * (phi m p τ * phi m q τ)
      = Cq * (chi n m q * Cq - chi n m p * Cp + (m / 2 : ℝ) * ∫ τ in p..q, chi n m τ * exp (-((m / 2 : ℝ) * τ))) := by
    have e : ∀ τ ∈ uIcc p q, deriv (chi n m) τ * (phi m p τ * phi m q τ)
        = Cq * (deriv (chi n m) τ * exp (-((m / 2 : ℝ) * τ))) := by
      intro τ hτ
      rw [uIcc_of_le hpq] at hτ
      unfold phi
      rw [max_eq_right hτ.1, max_eq_left hτ.2]
      have : (m : ℝ) * τ / 2 = m / 2 * τ := by ring
      rw [this]; ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul,
      chi_byParts hn1 hmn hp hpq (m / 2)]
    have e1 : exp (-((m / 2 : ℝ) * q)) = Cq := by rw [hCq]; congr 1; ring
    have e2 : exp (-((m / 2 : ℝ) * p)) = Cp := by rw [hCp]; congr 1; ring
    rw [e1, e2]
  -- third piece
  have hkI := (integrableOn_kern_parts hn hq).2 m hm
  have h3 : ∫ τ in q..P, deriv (chi n m) τ * (phi m p τ * phi m q τ)
      = kern n m P - chi n m q * (Cq * Cq) + m * (Gam n m q - Gam n m P) := by
    have e : ∀ τ ∈ uIcc q P, deriv (chi n m) τ * (phi m p τ * phi m q τ)
        = deriv (chi n m) τ * exp (-((m : ℝ) * τ)) := by
      intro τ hτ
      rw [uIcc_of_le hqP] at hτ
      unfold phi
      rw [max_eq_right (hpq.trans hτ.1), max_eq_right hτ.1, ← exp_add]
      congr 2; ring
    have ek : ∀ τ ∈ uIcc q P, chi n m τ * exp (-((m : ℝ) * τ)) = kern n m τ := by
      intro τ _
      unfold chi
      have : exp (m * τ) * exp (-((m : ℝ) * τ)) = 1 := by rw [← exp_add]; simp
      calc exp (m * τ) * kern n m τ * exp (-((m : ℝ) * τ))
          = (exp (m * τ) * exp (-((m : ℝ) * τ))) * kern n m τ := by ring
        _ = kern n m τ := by rw [this, one_mul]
    have hG : ∫ τ in q..P, kern n m τ = Gam n m q - Gam n m P := by
      have := intervalIntegral.integral_Ioi_sub_Ioi hkI hqP
      unfold Gam; linarith
    rw [intervalIntegral.integral_congr e, chi_byParts hn1 hmn hq hqP m,
      intervalIntegral.integral_congr ek, hG]
    have e1 : chi n m P * exp (-((m : ℝ) * P)) = kern n m P := ek P right_mem_uIcc
    have e2 : exp (-((m : ℝ) * q)) = Cq * Cq := by rw [hCq, ← exp_add]; congr 1; ring
    rw [e1, e2]
  -- the integral in `Ktau`
  have hJ : ∫ u in p..q, hK n m q u = Cq * ∫ τ in p..q, chi n m τ * exp (-((m / 2 : ℝ) * τ)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    unfold hK chi
    have : exp (-(m * (q - u) / 2)) = Cq * (exp (m * u) * exp (-((m / 2 : ℝ) * u))) := by
      rw [hCq, ← exp_add, ← exp_add]; congr 1; ring
    simp only [this]; ring
  rw [hsplit, h1, h2, h3]
  unfold Ktau
  rw [hJ]
  ring

/-- **The τ-kernel is positive semidefinite** (in the form needed for the Schur step): its symmetric
extension pairs nonnegatively with every `G` that is nonnegative on rank-one forms `φ φᵀ`, `φ ≥ 0`. -/
theorem tauK_psd {n m : ℕ} (hn : 2 ≤ n) (hm : m ∈ Finset.Icc 1 (n - 2)) {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (G : Fin N → Fin N → ℝ)
    (hG : ∀ φ : Fin N → ℝ, (∀ i, 0 ≤ φ i) → 0 ≤ ∑ i, ∑ j, φ i * φ j * G i j) :
    0 ≤ ∑ i, ∑ j, Ktau n m (min (p i) (p j)) (max (p i) (p j)) * G i j := by
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  have hm2 : m ≤ n - 2 := (Finset.mem_Icc.mp hm).2
  have hn1 : 1 ≤ n := by omega
  have hmn : m ≤ n := by omega
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  set P : ℝ := ∑ i, p i with hPdef
  have hpP : ∀ i, p i ≤ P := fun i => Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  set c0 : ℝ := m * Gam n m P - kern n m P with hc0
  have hc0' : 0 ≤ c0 := by have := kern_le_mul_Gam hm1 hm2 hP; linarith
  have hrep : ∀ i j, m * Ktau n m (min (p i) (p j)) (max (p i) (p j))
      = (∫ τ in (0 : ℝ)..P, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ)) + c0 := by
    intro i j
    rcases le_total (p i) (p j) with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact tauK_repr hn hm (hp i) h (hpP j)
    · have e : (fun τ => deriv (chi n m) τ * (phi m (p j) τ * phi m (p i) τ))
          = fun τ => deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) := by
        funext τ; ring
      rw [min_eq_right h, max_eq_left h, tauK_repr hn hm (hp j) h (hpP i), e]
  have hII : ∀ i j, IntervalIntegrable
      (fun τ => deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j) volume 0 P := fun i j =>
    ((deriv_chi_intervalIntegrable hn1 hmn le_rfl hP).mul_continuousOn
      ((continuous_phi m (p i)).mul (continuous_phi m (p j))).continuousOn).mul_const _
  have hsum : (m : ℝ) * ∑ i, ∑ j, Ktau n m (min (p i) (p j)) (max (p i) (p j)) * G i j
      = (∫ τ in (0 : ℝ)..P, ∑ i, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j)
        + c0 * ∑ i, ∑ j, G i j := by
    have hIi : ∀ i : Fin N, IntervalIntegrable
        (fun τ => ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j) volume 0 P := fun i => by
      have h := IntervalIntegrable.sum Finset.univ
        (f := fun j τ => deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j) (fun j _ => hII i j)
      have e : (∑ j, fun τ => deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j)
          = fun τ => ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j := by
        funext τ; simp
      rw [e] at h; exact h
    have e1 : (∫ τ in (0 : ℝ)..P, ∑ i, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j)
        = ∑ i, ∫ τ in (0 : ℝ)..P, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j :=
      intervalIntegral.integral_finsetSum
        (f := fun i τ => ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j) (fun i _ => hIi i)
    have e2 : ∀ i : Fin N,
        (∫ τ in (0 : ℝ)..P, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j)
        = ∑ j, ∫ τ in (0 : ℝ)..P, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j := fun i =>
      intervalIntegral.integral_finsetSum
        (f := fun j τ => deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j) (fun j _ => hII i j)
    rw [e1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e2 i, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_mul_const, ← mul_assoc, hrep i j]
    ring
  have hint : 0 ≤ ∫ τ in (0 : ℝ)..P, ∑ i, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j := by
    rw [intervalIntegral.integral_of_le hP]
    refine setIntegral_nonneg measurableSet_Ioc fun τ hτ => ?_
    have hd := (chi_hasDerivAt (n := n) hmn hτ.1).2
    have hφ := hG (fun i => phi m (p i) τ) (fun i => (exp_pos _).le)
    have e : ∑ i, ∑ j, deriv (chi n m) τ * (phi m (p i) τ * phi m (p j) τ) * G i j
        = deriv (chi n m) τ * ∑ i, ∑ j, phi m (p i) τ * phi m (p j) τ * G i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e]
    exact mul_nonneg hd hφ
  have hG1 : 0 ≤ ∑ i, ∑ j, G i j := by
    have := hG (fun _ => 1) (fun _ => zero_le_one)
    simpa using this
  have htot : 0 ≤ (m : ℝ) * ∑ i, ∑ j, Ktau n m (min (p i) (p j)) (max (p i) (p j)) * G i j := by
    rw [hsum]; exact add_nonneg hint (mul_nonneg hc0' hG1)
  exact nonneg_of_mul_nonneg_right htot hmr

end MatrixIneq
