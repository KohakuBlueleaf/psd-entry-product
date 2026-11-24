import MatrixIneq.Coefficients

/-!
# Step 3: the kernel inequality and the diagonal case

* `kern_poisson_le`: pointwise in `w > 0`,
  `kern n 0 w / 2 + ∑_{m=1}^{n-2} kern n m w · cos (m θ) ≤ sinh w / (2 (cosh w - cos θ))`,
  i.e. the instantaneous certificate kernel lies below half the Poisson kernel. The difference is a Fejér kernel
  times a Poisson kernel (closed forms `sS_sH_closed`, `sT_closed`, `fejer_nonneg`).
* `integral_poisson`: the Poisson integral `∫_{w > p} (P_w - 1)/2 = - log |1 - e^{-p} z|`.
* `harm_le`, `star_diag`: integrating over `w > p`,
  `Γ_0(p) + ∑_m Γ_m(p) Re (z^m) ≤ - log |1 - e^{-p} z|` on `|z| = 1`. This is the pair inequality at `p = q`.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-! ### Convolution sums -/

section sums

variable (w θ : ℝ)

/-- `∑_{m<n} sinh ((n-m) w) cos (m θ)`. -/
noncomputable def sS (n : ℕ) : ℝ := ∑ m ∈ range n, sinh (((n : ℝ) - m) * w) * cos (m * θ)

/-- `∑_{m<n} cosh ((n-m) w) cos (m θ)`. -/
noncomputable def sH (n : ℕ) : ℝ := ∑ m ∈ range n, cosh (((n : ℝ) - m) * w) * cos (m * θ)

/-- `∑_{m<n} (n-m) cos (m θ)`. -/
noncomputable def sT (n : ℕ) : ℝ := ∑ m ∈ range n, ((n : ℝ) - m) * cos (m * θ)

/-- `∑_{m<n} cos (m θ)`. -/
noncomputable def sU (n : ℕ) : ℝ := ∑ m ∈ range n, cos (m * θ)

theorem sS_succ (n : ℕ) :
    sS w θ (n + 1) = cosh w * sS w θ n + sinh w * sH w θ n + sinh w * cos (n * θ) := by
  unfold sS sH
  rw [sum_range_succ]
  have e : ∀ m : ℕ, sinh ((((n + 1 : ℕ) : ℝ) - m) * w)
      = sinh (((n : ℝ) - m) * w) * cosh w + cosh (((n : ℝ) - m) * w) * sinh w := by
    intro m; rw [← sinh_add]; congr 1; push_cast; ring
  simp only [e]
  rw [sub_self, zero_mul, sinh_zero, cosh_zero, zero_mul, zero_add, one_mul, mul_sum, mul_sum,
    ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun m _ => by ring

theorem sH_succ (n : ℕ) :
    sH w θ (n + 1) = cosh w * sH w θ n + sinh w * sS w θ n + cosh w * cos (n * θ) := by
  unfold sS sH
  rw [sum_range_succ]
  have e : ∀ m : ℕ, cosh ((((n + 1 : ℕ) : ℝ) - m) * w)
      = cosh (((n : ℝ) - m) * w) * cosh w + sinh (((n : ℝ) - m) * w) * sinh w := by
    intro m; rw [← cosh_add]; congr 1; push_cast; ring
  simp only [e]
  rw [sub_self, zero_mul, sinh_zero, cosh_zero, zero_mul, add_zero, one_mul, mul_sum, mul_sum,
    ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun m _ => by ring

theorem cos_succ_succ (n : ℕ) :
    cos (((n : ℝ) + 1 + 1) * θ) = 2 * cos θ * cos (((n : ℝ) + 1) * θ) - cos (n * θ) := by
  have h := Real.cos_add_cos (((n : ℝ) + 1 + 1) * θ) (n * θ)
  have e1 : (((n : ℝ) + 1 + 1) * θ + n * θ) / 2 = ((n : ℝ) + 1) * θ := by ring
  have e2 : (((n : ℝ) + 1 + 1) * θ - n * θ) / 2 = θ := by ring
  rw [e1, e2] at h
  linarith

/-- Closed forms of the two convolution sums, multiplied by `2 (cosh w - cos θ)`. -/
theorem sS_sH_closed (n : ℕ) :
    2 * (cosh w - cos θ) * sS w θ n
        = (cosh w - cos θ) * sinh (n * w) + sinh w * (cosh (n * w) - cos (n * θ)) ∧
    2 * (cosh w - cos θ) * sH w θ n
        = (cosh w - cos θ) * cosh (n * w) + sinh w * sinh (n * w) - cosh w * cos (n * θ)
          + 2 * cos θ * cos (n * θ) - cos (((n : ℝ) + 1) * θ) := by
  induction n with
  | zero =>
    constructor
    · simp [sS]
    · simp [sH]; ring
  | succ n ih =>
    obtain ⟨hS, hH⟩ := ih
    have e1 : sinh (((n + 1 : ℕ) : ℝ) * w) = sinh (n * w) * cosh w + cosh (n * w) * sinh w := by
      rw [← sinh_add]; congr 1; push_cast; ring
    have e2 : cosh (((n + 1 : ℕ) : ℝ) * w) = cosh (n * w) * cosh w + sinh (n * w) * sinh w := by
      rw [← cosh_add]; congr 1; push_cast; ring
    have hrec := cos_succ_succ θ n
    have hcs := Real.cosh_sq w
    rw [sS_succ, sH_succ, e1, e2]
    push_cast
    constructor
    · linear_combination cosh w * hS + sinh w * hH
    · linear_combination cosh w * hH + sinh w * hS + hrec + cos (n * θ) * hcs

theorem sU_closed (n : ℕ) :
    2 * (1 - cos θ) * sU θ (n + 1) = (1 - cos θ) + cos (n * θ) - cos (((n : ℝ) + 1) * θ) := by
  induction n with
  | zero => simp [sU]; ring
  | succ n ih =>
    have hrec := cos_succ_succ θ n
    have e : sU θ (n + 1 + 1) = sU θ (n + 1) + cos (((n : ℝ) + 1) * θ) := by
      unfold sU; rw [sum_range_succ (n := n + 1)]; push_cast; ring
    rw [e]; push_cast
    linear_combination ih + hrec

theorem sT_closed (n : ℕ) :
    2 * (1 - cos θ) * sT θ n = n * (1 - cos θ) + 1 - cos (n * θ) := by
  induction n with
  | zero => simp [sT]
  | succ n ih =>
    have e : sT θ (n + 1) = sT θ n + sU θ (n + 1) := by
      unfold sT sU
      rw [sum_range_succ, sum_range_succ (n := n) (f := fun m : ℕ => cos (m * θ)), ← add_assoc,
        ← sum_add_distrib]
      push_cast
      congr 1
      · exact sum_congr rfl fun m _ => by ring
      · ring
    rw [e]; push_cast
    linear_combination ih + sU_closed θ n

/-- The Fejér sum `2 ∑_{m<n} (n-m) cos (m θ) - n` is nonnegative. -/
theorem fejer_nonneg (n : ℕ) : 0 ≤ 2 * sT θ n - n := by
  by_cases hc : cos θ = 1
  · obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).mp hc
    have hcm : ∀ m : ℕ, cos (m * θ) = 1 := by
      intro m
      have : (m : ℝ) * θ = ((m * k : ℤ) : ℝ) * (2 * π) := by rw [← hk]; push_cast; ring
      rw [this]; exact Real.cos_int_mul_two_pi _
    have h := sT_closed θ n
    -- direct: every term is `n - m ≥ 0`, and the `m = 0` term is `n`
    unfold sT
    simp only [hcm, mul_one]
    cases n with
    | zero => simp
    | succ n =>
      rw [sum_range_succ']
      have : 0 ≤ ∑ m ∈ range n, (((n + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) :=
        sum_nonneg fun m hm => by
          have : m < n := mem_range.mp hm
          have : (m : ℝ) + 1 ≤ n := by exact_mod_cast this
          push_cast; linarith
      push_cast at this ⊢
      linarith
  · have hlt : 0 < 1 - cos θ := by
      have := Real.cos_le_one θ
      exact lt_of_le_of_ne (by linarith) (fun h => hc (by linarith))
    have h := sT_closed θ n
    have h1 : (1 - cos θ) * (2 * sT θ n - n) = 1 - cos (n * θ) := by linarith
    have h2 : 0 ≤ 1 - cos (n * θ) := by linarith [Real.cos_le_one (n * θ)]
    by_contra hneg
    rw [not_le] at hneg
    nlinarith

end sums

/-! ### The pointwise kernel inequality -/

theorem sum_range_kern_cos (n : ℕ) (w θ : ℝ) :
    ∑ m ∈ range n, kern n m w * cos (m * θ) = (sS w θ n - sinh w * sT θ n) / (cosh (n * w) - 1) := by
  unfold sS sT kern
  rw [mul_sum, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m < n := mem_range.mp hm
  have : ((n - m : ℕ) : ℝ) = (n : ℝ) - m := Nat.cast_sub hm'.le
  rw [this]; ring

theorem sum_Icc_kern_cos {n : ℕ} (hn : 1 ≤ n) (w θ : ℝ) :
    ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w * cos (m * θ)
      = ∑ m ∈ range n, kern n m w * cos (m * θ) - kern n 0 w := by
  have h0 : (0 : ℕ) ∈ range n := Finset.mem_range.mpr hn
  have h1 := sum_erase_eq_sub (f := fun m : ℕ => kern n m w * cos (m * θ)) h0
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one] at h1
  rw [← h1]
  refine sum_subset ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [mem_erase, Finset.mem_range]
    omega
  · intro m hm hm'
    rw [mem_erase, Finset.mem_range] at hm
    rw [Finset.mem_Icc] at hm'
    have : m = n - 1 := by omega
    rw [this, kern_pred n hn w, zero_mul]

/-- **Pointwise inequality**: the instantaneous certificate kernel lies below half the Poisson kernel. -/
theorem kern_poisson_le {n : ℕ} (hn : 1 ≤ n) {w : ℝ} (hw : 0 < w) (θ : ℝ) :
    (kern n 0 w - 1) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w * cos (m * θ)
      ≤ (sinh w / (cosh w - cos θ) - 1) / 2 := by
  rw [sum_Icc_kern_cos hn, sum_range_kern_cos]
  have hk0 : kern n 0 w = (sinh (n * w) - n * sinh w) / (cosh (n * w) - 1) := by simp [kern]
  rw [hk0]
  have hnw : (n : ℝ) * w ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hc : 0 < cosh (n * w) - 1 := sub_pos.mpr (Real.one_lt_cosh.mpr hnw)
  have hcw : 1 < cosh w := Real.one_lt_cosh.mpr hw.ne'
  have hΔ : 0 < cosh w - cos θ := by linarith [Real.cos_le_one θ]
  have hsw : 0 < sinh w := Real.sinh_pos_iff.mpr hw
  obtain ⟨hS, -⟩ := sS_sH_closed w θ n
  have hT := sT_closed θ n
  have hF := fejer_nonneg θ n
  have hP : 0 ≤ sinh w * ((cosh w - 1) * (2 * sT θ n - n)) :=
    mul_nonneg hsw.le (mul_nonneg (by linarith) hF)
  have e : (cosh (n * w) - 1) * sinh w
      - (2 * (cosh w - cos θ) * (sS w θ n - sinh w * sT θ n)
          - (cosh w - cos θ) * (sinh (n * w) - n * sinh w))
      = sinh w * ((cosh w - 1) * (2 * sT θ n - n)) := by
    linear_combination (-1 : ℝ) * hS + sinh w * hT
  have key : 2 * (cosh w - cos θ) * (sS w θ n - sinh w * sT θ n)
      - (cosh w - cos θ) * (sinh (n * w) - n * sinh w) ≤ (cosh (n * w) - 1) * sinh w := by linarith
  have e2 : (sS w θ n - sinh w * sT θ n) / (cosh (n * w) - 1)
        - (sinh (n * w) - n * sinh w) / (cosh (n * w) - 1) / 2
      = (2 * (cosh w - cos θ) * (sS w θ n - sinh w * sT θ n)
          - (cosh w - cos θ) * (sinh (n * w) - n * sinh w))
        / (2 * (cosh w - cos θ) * (cosh (n * w) - 1)) := by
    field_simp
  have e3 : sinh w / (cosh w - cos θ) / 2
      = (cosh (n * w) - 1) * sinh w / (2 * (cosh w - cos θ) * (cosh (n * w) - 1)) := by
    field_simp
  have hden : 0 < 2 * (cosh w - cos θ) * (cosh (n * w) - 1) := by positivity
  have h3 := div_le_div_of_nonneg_right key hden.le
  rw [← e2, ← e3] at h3
  linarith

/-! ### Integrability of the kernels -/

theorem integrableOn_kern_parts {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn (fun w => (kern n 0 w - 1) / 2) (Ioi p) ∧
      ∀ m ∈ Finset.Icc 1 (n - 2), IntegrableOn (kern n m) (Ioi p) := by
  have hn1' : 1 ≤ n := by omega
  set A : ℝ → ℝ := fun w => ((n : ℝ) - 1) * ((kern n 0 w - 1) / 2) with hA
  set B : ℝ → ℝ := fun w => ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w with hB
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : ∀ w ∈ Ioi p, 0 ≤ w := fun w hw => hp.trans (le_of_lt hw)
  have hAle : ∀ w ∈ Ioi p, A w ≤ 0 := fun w hw =>
    mul_nonpos_of_nonneg_of_nonpos hn1.le (by have := kern_zero_le_one n (hpos w hw); linarith)
  have hBge : ∀ w ∈ Ioi p, 0 ≤ B w := fun w hw => sum_nonneg fun m _ => kern_nonneg n m (hpos w hw)
  have hderiv : ∀ w ∈ Ioi p, HasDerivAt (logF n) (A w - B w) w := by
    intro w hw
    have hw0 : 0 < w := lt_of_le_of_lt hp hw
    have := hasDerivAt_logF hn1' hw0
    rwa [← kern_identity hn1' hw0] at this
  have hneg : ∀ w ∈ Ioi p, A w - B w ≤ 0 := fun w hw => by linarith [hAle w hw, hBge w hw]
  have hcont : ContinuousWithinAt (logF n) (Ici p) p := (continuous_logF hn1').continuousWithinAt
  have hint : IntegrableOn (fun w => A w - B w) (Ioi p) :=
    integrableOn_Ioi_deriv_of_nonpos hcont hderiv hneg (tendsto_logF hn1')
  have hdom : IntegrableOn (fun w => -(A w - B w)) (Ioi p) := hint.neg
  have hAint : IntegrableOn A (Ioi p) := by
    refine Integrable.mono' hdom ?_ ?_
    · exact ((measurable_const.mul (((measurable_kern n 0).sub measurable_const).div_const 2))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
      rw [Real.norm_eq_abs, abs_of_nonpos (hAle w hw)]
      linarith [hBge w hw]
  refine ⟨?_, ?_⟩
  · have h : IntegrableOn (fun w => ((n : ℝ) - 1)⁻¹ * A w) (Ioi p) := hAint.const_mul _
    refine IntegrableOn.congr_fun h (fun w _ => ?_) measurableSet_Ioi
    simp only [hA]
    field_simp
  · intro m hm
    refine Integrable.mono' hdom (measurable_kern n m).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (kern_nonneg n m (hpos w hw))]
    have h1 : kern n m w ≤ B w :=
      single_le_sum (f := fun m => kern n m w) (fun m _ => kern_nonneg n m (hpos w hw)) hm
    linarith [hAle w hw]

/-! ### The Poisson integral -/

/-- `|1 - e^{-w} z|² = 1 - 2 e^{-w} c + e^{-2w}` with `c = Re z`. -/
noncomputable def qf (c w : ℝ) : ℝ := 1 - 2 * exp (-w) * c + exp (-w) ^ 2

theorem qf_eq (c w : ℝ) : qf c w = 2 * exp (-w) * (cosh w - c) := by
  unfold qf
  rw [cosh_eq, exp_neg]
  have : exp w ≠ 0 := (exp_pos w).ne'
  field_simp
  ring

theorem poisson_eq {w c : ℝ} (hw : 0 < w) (hc : c ≤ 1) :
    (sinh w / (cosh w - c) - 1) / 2 = (exp (-w) * c - exp (-w) ^ 2) / qf c w := by
  have hcw : 1 < cosh w := Real.one_lt_cosh.mpr hw.ne'
  have hD : cosh w - c ≠ 0 := by linarith
  have he : exp (-w) ≠ 0 := (exp_pos _).ne'
  have hs : sinh w = cosh w - exp (-w) := by linarith [Real.cosh_sub_sinh w]
  rw [qf_eq, hs]
  field_simp
  ring

theorem qf_lower {p c : ℝ} (hp : 0 ≤ p) (hc : c ≤ 1) (hne : p ≠ 0 ∨ c ≠ 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ w, p ≤ w → κ ≤ qf c w := by
  rcases hp.eq_or_lt with h0 | hpos
  · have hc1 : c < 1 := by
      rcases hne with h | h
      · exact absurd h0.symm h
      · exact lt_of_le_of_ne hc h
    by_cases hc0 : c ≤ 0
    · refine ⟨1, one_pos, fun w _ => ?_⟩
      unfold qf
      have he := exp_pos (-w)
      nlinarith [sq_nonneg (exp (-w))]
    · refine ⟨1 - c ^ 2, by nlinarith, fun w _ => ?_⟩
      unfold qf
      nlinarith [sq_nonneg (exp (-w) - c)]
  · have h1 : exp (-p) < 1 := by
      have := Real.exp_lt_exp.mpr (by linarith : -p < 0)
      simpa using this
    refine ⟨(1 - exp (-p)) ^ 2, by nlinarith, fun w hw => ?_⟩
    unfold qf
    have he := exp_pos (-w)
    have hle : exp (-w) ≤ exp (-p) := exp_le_exp.mpr (by linarith)
    nlinarith [mul_nonneg he.le (sub_nonneg.mpr hc), mul_nonneg (sub_nonneg.mpr hle) (by linarith : (0:ℝ) ≤ 2 - exp (-w) - exp (-p))]

theorem hasDerivAt_half_log_qf {c w : ℝ} (hq : 0 < qf c w) :
    HasDerivAt (fun w => (1 / 2 : ℝ) * log (qf c w)) ((exp (-w) * c - exp (-w) ^ 2) / qf c w) w := by
  have he : HasDerivAt (fun w : ℝ => exp (-w)) (-exp (-w)) w := by
    have := (hasDerivAt_neg w).exp
    convert this using 1
    ring
  have hq' : HasDerivAt (qf c) (2 * exp (-w) * c - 2 * exp (-w) ^ 2) w := by
    have h1 := (he.const_mul 2).mul_const c
    have h2 := he.pow 2
    have h3 := ((hasDerivAt_const w (1 : ℝ)).sub h1).add h2
    have hfun : qf c = (fun y => (1 : ℝ) - 2 * exp (-y) * c + exp (-y) ^ 2) := rfl
    rw [hfun]
    convert h3 using 1
    simp
    ring
  have h4 := (hq'.log hq.ne').const_mul (1 / 2 : ℝ)
  convert h4 using 1
  field_simp

theorem integral_poisson {p c : ℝ} (hp : 0 ≤ p) (hc : c ≤ 1) (hc' : -1 ≤ c) (hne : p ≠ 0 ∨ c ≠ 1) :
    IntegrableOn (fun w => (exp (-w) * c - exp (-w) ^ 2) / qf c w) (Ioi p) ∧
      ∫ w in Ioi p, (exp (-w) * c - exp (-w) ^ 2) / qf c w = -((1 / 2 : ℝ) * log (qf c p)) := by
  obtain ⟨κ, hκ, hlow⟩ := qf_lower hp hc hne
  have hqpos : ∀ w, p ≤ w → 0 < qf c w := fun w hw => lt_of_lt_of_le hκ (hlow w hw)
  have hint : IntegrableOn (fun w => (exp (-w) * c - exp (-w) ^ 2) / qf c w) (Ioi p) := by
    have hg : IntegrableOn (fun w : ℝ => 2 / κ * exp (-1 * w)) (Ioi p) :=
      (exp_neg_integrableOn_Ioi p one_pos).const_mul (2 / κ)
    refine Integrable.mono' hg ?_ ?_
    · have : Measurable (fun w : ℝ => (exp (-w) * c - exp (-w) ^ 2) / qf c w) := by
        unfold qf; fun_prop
      exact this.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
      have hw0 : 0 < w := lt_of_le_of_lt hp hw
      have he := exp_pos (-w)
      have he1 : exp (-w) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      have hq := hlow w (le_of_lt hw)
      have hqp := hqpos w (le_of_lt hw)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hqp, div_le_iff₀ hqp]
      have hnum : |exp (-w) * c - exp (-w) ^ 2| ≤ 2 * exp (-w) := by
        rw [abs_le]; constructor <;> nlinarith
      have : 2 / κ * exp (-1 * w) * qf c w = 2 * exp (-w) * (qf c w / κ) := by
        rw [show (-1 : ℝ) * w = -w by ring]; field_simp
      rw [this]
      have h1 : 1 ≤ qf c w / κ := by rw [le_div_iff₀ hκ]; linarith
      nlinarith
  refine ⟨hint, ?_⟩
  have hcont : ContinuousWithinAt (fun w => (1 / 2 : ℝ) * log (qf c w)) (Ici p) p :=
    (hasDerivAt_half_log_qf (hqpos p le_rfl)).continuousAt.continuousWithinAt
  have hderiv : ∀ w ∈ Ioi p, HasDerivAt (fun w => (1 / 2 : ℝ) * log (qf c w))
      ((exp (-w) * c - exp (-w) ^ 2) / qf c w) w :=
    fun w hw => hasDerivAt_half_log_qf (hqpos w (le_of_lt hw))
  have htend : Tendsto (fun w => (1 / 2 : ℝ) * log (qf c w)) atTop (𝓝 0) := by
    have he : Tendsto (fun w : ℝ => exp (-w)) atTop (𝓝 0) := tendsto_exp_neg_atTop_nhds_zero
    have hq : Tendsto (qf c) atTop (𝓝 (1 - 2 * 0 * c + 0 ^ 2)) :=
      ((tendsto_const_nhds.sub ((he.const_mul 2).mul_const c)).add (he.pow 2))
    simp only [mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hq
    have hl := ((Real.continuousAt_log (one_ne_zero)).tendsto.comp hq).const_mul (1 / 2 : ℝ)
    simpa using hl
  have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [this]; ring

/-! ### The pair inequality on the diagonal -/

theorem re_pow_exp (θ : ℝ) (m : ℕ) : ((Complex.exp (θ * Complex.I)) ^ m).re = Real.cos (m * θ) := by
  rw [← Complex.exp_nat_mul]
  have : (m : ℂ) * (θ * Complex.I) = ((m * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem harm_le {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (θ : ℝ) (hne : p ≠ 0 ∨ cos θ ≠ 1) :
    Gam0 n p + ∑ m ∈ Finset.Icc 1 (n - 2), Gam n m p * cos (m * θ)
      ≤ -((1 / 2 : ℝ) * log (qf (cos θ) p)) := by
  obtain ⟨h0, hk⟩ := integrableOn_kern_parts hn hp
  obtain ⟨hPint, hPeq⟩ := integral_poisson hp (Real.cos_le_one θ) (Real.neg_one_le_cos θ) hne
  have hterm : ∀ m ∈ Finset.Icc 1 (n - 2), IntegrableOn (fun w => kern n m w * cos (m * θ)) (Ioi p) :=
    fun m hm => (hk m hm).mul_const _
  have hsumint : IntegrableOn (fun w => ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w * cos (m * θ)) (Ioi p) :=
    integrable_finsetSum _ hterm
  have e : Gam0 n p + ∑ m ∈ Finset.Icc 1 (n - 2), Gam n m p * cos (m * θ)
      = ∫ w in Ioi p, ((kern n 0 w - 1) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), kern n m w * cos (m * θ)) := by
    rw [integral_add h0 hsumint, MeasureTheory.integral_finsetSum _ hterm]
    simp only [Gam0, Gam, MeasureTheory.integral_mul_const]
  rw [e, ← hPeq]
  refine setIntegral_mono_on (h0.add hsumint) hPint measurableSet_Ioi (fun w hw => ?_)
  have hw0 : 0 < w := lt_of_le_of_lt hp hw
  rw [← poisson_eq hw0 (Real.cos_le_one θ)]
  exact kern_poisson_le (by omega) hw0 θ

/-- **The pair inequality at `p = q`.**  `-log |1 - e^{-p} z| ≥ Γ_0(p) + ∑_{m=1}^{n-2} Γ_m(p) Re (z^m)` on `|z| = 1`. -/
theorem star_diag {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - (Real.exp (-p) : ℂ) * z‖ ≤ Real.exp (-(harm (Gam0 n p) (fun m => Gam n m p) (n - 2) z)) := by
  have hsq := normSq_one_sub (exp (-p)) hz
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  have hre1 : (Complex.exp (θ * Complex.I)).re = cos θ := Complex.exp_ofReal_mul_I_re θ
  rw [hre1] at hsq
  have hq : ‖1 - (Real.exp (-p) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2 = qf (cos θ) p := by
    rw [hsq]; unfold qf; ring
  have hharm : harm (Gam0 n p) (fun m => Gam n m p) (n - 2) (Complex.exp (θ * Complex.I))
      = Gam0 n p + ∑ m ∈ Finset.Icc 1 (n - 2), Gam n m p * cos (m * θ) := by
    unfold harm; simp only [re_pow_exp]
  rw [hharm]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_pos _).le two_ne_zero).mp ?_
  rw [hq, ← Real.exp_nat_mul]
  by_cases htriv : p = 0 ∧ cos θ = 1
  · obtain ⟨rfl, hc⟩ := htriv
    have : qf (cos θ) 0 = 0 := by unfold qf; rw [hc]; simp; ring
    rw [this]; exact (exp_pos _).le
  · have hne : p ≠ 0 ∨ cos θ ≠ 1 := by tauto
    obtain ⟨κ, hκ, hlow⟩ := qf_lower hp (Real.cos_le_one θ) hne
    have hqp : 0 < qf (cos θ) p := lt_of_lt_of_le hκ (hlow p le_rfl)
    have h := harm_le hn hp θ hne
    calc qf (cos θ) p = exp (log (qf (cos θ) p)) := (exp_log hqp).symm
      _ ≤ _ := exp_le_exp.mpr (by push_cast; linarith)


end MatrixIneq
