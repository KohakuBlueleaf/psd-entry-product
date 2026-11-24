import MatrixIneq.Tail
import Exploration.EqualDiag

/-!
# The one-sided inequality `HIn n`

`HIn n → Star n` (`star_of_hIn`) by monotonicity of the gap in the smaller parameter.
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-- **The one-sided inequality.** For `0 < p < q` and `|z| = 1`,
`k_0(p)/2 + ∑_{m=1}^{n-2} k_m(p) √(Γ_m(q)/Γ_m(p)) Re(z^m) ≤ ½ P_α`, `α = (p+q)/2`,
`P_α = (1 - e^{-2α}) / |1 - e^{-α} z|²`. -/
def HIn (n : ℕ) : Prop :=
  ∀ p q : ℝ, 0 < p → p < q → ∀ z : ℂ, ‖z‖ = 1 →
    kern n 0 p / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), kern n m p * Real.sqrt (Gam n m q / Gam n m p) * (z ^ m).re
      ≤ (1 - Real.exp (-(p + q))) / (2 * ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * z‖ ^ 2)

theorem nat_mul_sinh_lt {N : ℕ} (hN : 2 ≤ N) {w : ℝ} (hw : 0 < w) : N * sinh w < sinh (N * w) := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  have hK : 1 ≤ K := by omega
  have hs : 0 < sinh w := sinh_pos_iff.mpr hw
  have hKw : (0 : ℝ) < K * w := mul_pos (by exact_mod_cast hK) hw
  have h1 := nat_mul_sinh_le_sinh_nat_mul K hw.le
  have h2 : (1 : ℝ) < cosh (K * w) := one_lt_cosh.mpr hKw.ne'
  have h3 : (1 : ℝ) ≤ cosh w := one_le_cosh w
  have h4 : 0 ≤ sinh (K * w) := sinh_nonneg_iff.mpr hKw.le
  have e : sinh ((K + 1 : ℕ) * w) = sinh (K * w) * cosh w + cosh (K * w) * sinh w := by
    rw [← sinh_add]; push_cast; ring_nf
  rw [e]; push_cast
  nlinarith

theorem kern_pos {n m : ℕ} (hm2 : m ≤ n - 2) (hn : 2 ≤ n) {w : ℝ} (hw : 0 < w) : 0 < kern n m w := by
  unfold kern
  have hnw : (n : ℝ) * w ≠ 0 := (mul_pos (by exact_mod_cast (by omega : 0 < n)) hw).ne'
  exact div_pos (sub_pos.mpr (nat_mul_sinh_lt (by omega) hw)) (sub_pos.mpr (one_lt_cosh.mpr hnw))

theorem Gam_pos {n m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ n - 2) {x : ℝ} (hx : 0 ≤ x) : 0 < Gam n m x := by
  have hn : 2 ≤ n := by omega
  have hy : (0 : ℝ) < x + 1 := by linarith
  have h1 := kern_le_mul_Gam hm1 hm2 hy.le
  have h2 := kern_pos hm2 hn hy
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
  have h3 : 0 < Gam n m (x + 1) := by
    by_contra hcon
    have : Gam n m (x + 1) ≤ 0 := not_lt.mp hcon
    nlinarith
  have hI := integrableOn_kern (by omega : 1 ≤ n) (Finset.mem_Icc.mpr ⟨hm1, hm2⟩) hx
  have h4 := intervalIntegral.integral_Ioi_sub_Ioi hI (by linarith : x ≤ x + 1)
  have h5 : 0 ≤ ∫ w in x..(x + 1), kern n m w :=
    intervalIntegral.integral_nonneg (by linarith) fun u hu => kern_nonneg n m (hx.trans hu.1)
  unfold Gam at *
  linarith

/-! ### The gap as a function of the smaller parameter -/

/-- The gap `L(x, q)` of `Star` at `z = e^{iθ}`, as a function of `x`. -/
noncomputable def gapL (n : ℕ) (θ q x : ℝ) : ℝ :=
  -(1 / 2 * log (qf (cos θ) ((x + q) / 2))) -
    ((Gam0 n x + Gam0 n q) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), √(Gam n m x * Gam n m q) * cos (m * θ))

theorem gapL_continuousOn {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousOn (gapL n θ q) (Icc 0 q) := by
  obtain ⟨h0, hk⟩ := integrableOn_kern_parts hn (le_refl (0 : ℝ))
  have hqf : Continuous (qf (cos θ)) := by unfold qf; fun_prop
  have hlog : ContinuousOn (fun x : ℝ => log (qf (cos θ) ((x + q) / 2))) (Icc 0 q) := by
    refine ContinuousOn.log (hqf.comp (by fun_prop)).continuousOn fun x hx => ?_
    exact (qf_pos (cos_le_one θ) (by linarith [hx.1] : 0 < (x + q) / 2)).ne'
  have hG0 : ContinuousOn (Gam0 n) (Icc 0 q) := tail_continuousOn h0 hq.le
  have hGm : ∀ m ∈ Finset.Icc 1 (n - 2), ContinuousOn (Gam n m) (Icc 0 q) :=
    fun m hm => tail_continuousOn (hk m hm) hq.le
  exact ContinuousOn.sub (ContinuousOn.neg (continuousOn_const.mul hlog))
    (ContinuousOn.add ((hG0.add continuousOn_const).div_const 2)
      (continuousOn_finsetSum _ fun m hm =>
        (((hGm m hm).mul continuousOn_const).sqrt).mul continuousOn_const))

theorem gapL_deriv_nonpos {n : ℕ} (hn : 2 ≤ n) (h : HIn n) (θ : ℝ) {q x : ℝ} (hx : 0 < x) (hxq : x < q) :
    ∃ E, HasDerivAt (gapL n θ q) E x ∧ E ≤ 0 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨h0, hk⟩ := integrableOn_kern_parts hn (le_refl (0 : ℝ))
  have hq : 0 < q := hx.trans hxq
  have hα : 0 < (x + q) / 2 := by linarith
  have hQ : 0 < qf (cos θ) ((x + q) / 2) := qf_pos (cos_le_one θ) hα
  -- the three derivatives
  have hin : HasDerivAt (fun x : ℝ => (x + q) / 2) (1 / 2) x := by
    simpa using ((hasDerivAt_id x).add_const q).div_const 2
  have hlog : HasDerivAt (fun x : ℝ => 1 / 2 * log (qf (cos θ) ((x + q) / 2)))
      ((exp (-((x + q) / 2)) * cos θ - exp (-((x + q) / 2)) ^ 2) / qf (cos θ) ((x + q) / 2) * (1 / 2)) x :=
    HasDerivAt.comp (h₂ := fun w : ℝ => 1 / 2 * log (qf (cos θ) w)) (h := fun x : ℝ => (x + q) / 2) x
      (hasDerivAt_half_log_qf (w := (x + q) / 2) hQ) hin
  have hG0 : HasDerivAt (Gam0 n) (-((kern n 0 x - 1) / 2)) x :=
    tail_hasDerivAt h0 (((measurable_kern n 0).sub measurable_const).div_const 2) hx
      (((continuousAt_kern hn1 0 hx).sub continuousAt_const).div_const 2)
  have hGm : ∀ m ∈ Finset.Icc 1 (n - 2), HasDerivAt (Gam n m) (-(kern n m x)) x := fun m hm =>
    tail_hasDerivAt (hk m hm) (measurable_kern n m) hx (continuousAt_kern hn1 m hx)
  have hpos : ∀ m ∈ Finset.Icc 1 (n - 2), 0 < Gam n m x ∧ 0 < Gam n m q := fun m hm =>
    ⟨Gam_pos (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hx.le,
      Gam_pos (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2 hq.le⟩
  have hs : ∀ m ∈ Finset.Icc 1 (n - 2),
      HasDerivAt (fun x => √(Gam n m x * Gam n m q) * cos (m * θ))
        (-(kern n m x) * Gam n m q / (2 * √(Gam n m x * Gam n m q)) * cos (m * θ)) x := fun m hm =>
    (((hGm m hm).mul_const (Gam n m q)).sqrt (mul_pos (hpos m hm).1 (hpos m hm).2).ne').mul_const _
  have hsum : HasDerivAt (fun x => ∑ m ∈ Finset.Icc 1 (n - 2), √(Gam n m x * Gam n m q) * cos (m * θ))
      (∑ m ∈ Finset.Icc 1 (n - 2),
        -(kern n m x) * Gam n m q / (2 * √(Gam n m x * Gam n m q)) * cos (m * θ)) x :=
    HasDerivAt.fun_sum fun m hm => hs m hm
  refine ⟨_, hlog.neg.sub (((hG0.add_const (Gam0 n q)).div_const 2).add hsum), ?_⟩
  -- the sign, from `HIn`
  have hz : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hH := h x q hx hxq _ hz
  have hsq := normSq_one_sub (exp (-(x + q) / 2)) hz
  rw [Complex.exp_ofReal_mul_I_re] at hsq
  simp only [re_pow_exp] at hH
  rw [hsq] at hH
  have e1 : -(x + q) / 2 = -((x + q) / 2) := by ring
  rw [e1] at hH
  set e := exp (-((x + q) / 2)) with he
  have e2 : exp (-(x + q)) = e ^ 2 := by
    rw [he, sq, ← exp_add]; congr 1; ring
  rw [e2] at hH
  have hQ' : (1 : ℝ) - 2 * e * cos θ + e ^ 2 = qf (cos θ) ((x + q) / 2) := rfl
  rw [hQ'] at hH
  set Q := qf (cos θ) ((x + q) / 2) with hQdef
  have hD : (1 - e ^ 2) / (2 * Q) = (e * cos θ - e ^ 2) / Q + 1 / 2 := by
    have hQe : Q = 1 - 2 * e * cos θ + e ^ 2 := rfl
    field_simp
    rw [hQe]; ring
  have hS : ∑ m ∈ Finset.Icc 1 (n - 2),
        -(kern n m x) * Gam n m q / (2 * √(Gam n m x * Gam n m q)) * cos (m * θ)
      = -(1 / 2) * ∑ m ∈ Finset.Icc 1 (n - 2), kern n m x * √(Gam n m q / Gam n m x) * cos (m * θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hx', hq'⟩ := hpos m hm
    have ha : 0 < √(Gam n m x) := Real.sqrt_pos.mpr hx'
    have hb : 0 < √(Gam n m q) := Real.sqrt_pos.mpr hq'
    have hbb : Gam n m q = √(Gam n m q) * √(Gam n m q) := (Real.mul_self_sqrt hq'.le).symm
    rw [Real.sqrt_mul hx'.le, Real.sqrt_div hq'.le]
    generalize √(Gam n m x) = a at *
    generalize √(Gam n m q) = b at *
    rw [hbb]
    field_simp
  rw [hS]
  rw [hD] at hH
  linarith

theorem gapL_diag_nonneg {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) {q : ℝ} (hq : 0 < q) : 0 ≤ gapL n θ q q := by
  have h := harm_le hn hq.le θ (Or.inl hq.ne')
  have e : ∀ m, √(Gam n m q * Gam n m q) = Gam n m q := fun m => Real.sqrt_mul_self (Gam_nonneg n m hq.le)
  unfold gapL
  simp only [e]
  have e2 : (q + q) / 2 = q := by ring
  rw [e2]
  linarith

/-- `HIn` gives `Star` on the half `p ≤ q`. -/
theorem starAt_of_hIn_le {n : ℕ} (hn : 3 ≤ n) (h : HIn n) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    StarAt n p q := by
  have hn2 : 2 ≤ n := by omega
  rcases hpq.eq_or_lt with rfl | hlt
  · exact starAt_diag hn2 hp
  have hq : 0 < q := lt_of_le_of_lt hp hlt
  intro z hz
  have hsq := normSq_one_sub (exp (-(p + q) / 2)) hz
  obtain ⟨θ, rfl⟩ := (Complex.norm_eq_one_iff z).mp hz
  rw [Complex.exp_ofReal_mul_I_re] at hsq
  have e1 : -(p + q) / 2 = -((p + q) / 2) := by ring
  have hqf : ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * Complex.exp (θ * Complex.I)‖ ^ 2
      = qf (cos θ) ((p + q) / 2) := by
    rw [hsq, e1]; unfold qf; ring
  -- monotonicity of the gap
  have hanti : AntitoneOn (gapL n θ q) (Icc 0 q) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 q) (gapL_continuousOn hn2 θ hq) ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨E, hE, -⟩ := gapL_deriv_nonpos hn2 h θ hx.1 hx.2
      exact hE.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨E, hE, hE0⟩ := gapL_deriv_nonpos hn2 h θ hx.1 hx.2
      rw [hE.deriv]; exact hE0
  have hgap : 0 ≤ gapL n θ q p :=
    (gapL_diag_nonneg hn2 θ hq).trans (hanti ⟨hp, hpq⟩ ⟨hq.le, le_rfl⟩ hpq)
  have hharm : harm ((Gam0 n p + Gam0 n q) / 2) (fun m => √(Gam n m p * Gam n m q)) (n - 2)
        (Complex.exp (θ * Complex.I))
      = (Gam0 n p + Gam0 n q) / 2 + ∑ m ∈ Finset.Icc 1 (n - 2), √(Gam n m p * Gam n m q) * cos (m * θ) := by
    unfold harm; simp only [re_pow_exp]
  rw [hharm]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (exp_pos _).le two_ne_zero).mp ?_
  rw [hqf, ← Real.exp_nat_mul]
  have hQ : 0 < qf (cos θ) ((p + q) / 2) := qf_pos (cos_le_one θ) (by linarith)
  unfold gapL at hgap
  calc qf (cos θ) ((p + q) / 2) = exp (log (qf (cos θ) ((p + q) / 2))) := (exp_log hQ).symm
    _ ≤ _ := exp_le_exp.mpr (by push_cast; linarith)

/-- **`Star` follows from the one-sided inequality `HIn`.** -/
theorem star_of_hIn {n : ℕ} (hn : 3 ≤ n) (h : HIn n) : Star n := by
  intro p q hp hq z hz
  rcases le_total p q with hpq | hqp
  · exact starAt_of_hIn_le hn h hp hpq z hz
  · have := starAt_of_hIn_le hn h hq hqp z hz
    have e1 : -(p + q) / 2 = -(q + p) / 2 := by ring
    have e2 : (Gam0 n p + Gam0 n q) / 2 = (Gam0 n q + Gam0 n p) / 2 := by ring
    have e3 : (fun m => √(Gam n m p * Gam n m q)) = fun m => √(Gam n m q * Gam n m p) := by
      funext m; rw [mul_comm]
    rw [e1, e2, e3]; exact this

/-- The main theorem follows from `HIn n` for all `n ≥ 3`. -/
theorem mainTheorem_of_hIn (h : ∀ n, 3 ≤ n → HIn n) : Statement.MainTheorem :=
  mainTheorem_of_star fun n hn => star_of_hIn hn (h n hn)


end MatrixIneq
