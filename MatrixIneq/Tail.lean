import MatrixIneq.Poisson
import MatrixIneq.Chi

/-!
# Tail integrals as functions of the lower limit

* `tail_eq`, `tail_continuousOn`, `tail_hasDerivAt`: for `f` integrable on `(0, ∞)`, the tail `x ↦ ∫_{w > x} f`
  is continuous on `[0, q]` and has derivative `-f x`; in particular `Γ_m' = -k_m`.
* `continuousAt_kern`, `qf_pos`: regularity of the kernels and positivity of `|1 - e^{-w} z|²` for `w > 0`.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

/-! ### Tail integrals as functions of the lower limit -/

theorem tail_eq {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) {x : ℝ} (hx : 0 ≤ x) :
    ∫ w in Ioi x, f w = (∫ w in Ioi 0, f w) - ∫ w in (0 : ℝ)..x, f w := by
  have := intervalIntegral.integral_Ioi_sub_Ioi hf hx
  linarith

theorem tail_continuousOn {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) {q : ℝ} (hq : 0 ≤ q) :
    ContinuousOn (fun x => ∫ w in Ioi x, f w) (Icc 0 q) := by
  have hint : IntervalIntegrable f volume 0 q :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hq).mpr (hf.mono_set Ioc_subset_Ioi_self)
  have h := intervalIntegral.continuousOn_primitive_interval' hint (a := 0) left_mem_uIcc
  rw [uIcc_of_le hq] at h
  exact (continuousOn_const.sub h).congr fun x hx => tail_eq hf hx.1

theorem tail_hasDerivAt {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hm : Measurable f) {x : ℝ} (hx : 0 < x)
    (hc : ContinuousAt f x) : HasDerivAt (fun x => ∫ w in Ioi x, f w) (-(f x)) x := by
  have hint : IntervalIntegrable f volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.le).mpr (hf.mono_set Ioc_subset_Ioi_self)
  have h := intervalIntegral.integral_hasDerivAt_right hint
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  have h2 := (hasDerivAt_const x (∫ w in Ioi 0, f w)).sub h
  rw [zero_sub] at h2
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with u hu using tail_eq hf hu.le

theorem continuousAt_kern {n : ℕ} (hn : 1 ≤ n) (m : ℕ) {x : ℝ} (hx : 0 < x) : ContinuousAt (kern n m) x := by
  have hnx : (n : ℝ) * x ≠ 0 := (mul_pos (by exact_mod_cast hn) hx).ne'
  have hne : cosh (n * x) - 1 ≠ 0 := (sub_pos.mpr (one_lt_cosh.mpr hnx)).ne'
  have h1 : Continuous fun w : ℝ => sinh ((n - m : ℕ) * w) - (n - m : ℕ) * sinh w :=
    (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul Real.continuous_sinh)
  have h2 : Continuous fun w : ℝ => cosh (n * w) - 1 :=
    (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).sub continuous_const
  exact h1.continuousAt.div h2.continuousAt hne

theorem qf_pos {c w : ℝ} (hc : c ≤ 1) (hw : 0 < w) : 0 < qf c w := by
  rw [qf_eq]
  have := one_lt_cosh.mpr hw.ne'
  exact mul_pos (mul_pos two_pos (exp_pos _)) (by linarith)


end MatrixIneq
