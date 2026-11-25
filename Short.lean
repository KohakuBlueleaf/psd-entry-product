import Mathlib
open Finset

/-! Single-file proof: for complex positive semidefinite `A`, `∏ᵢⱼ |1 - aᵢⱼ| ≤ ∏ᵢ |1 - aᵢᵢⁿ|`.
Cap the diagonal at `s²` (`al`), and show `Psi` is nondecreasing in `s` (`step`), `Psi 0 = 0`. -/
namespace Short
noncomputable section

def ν (K : ℕ) (t : ℝ) : ℝ := 1 - t ^ (2 * K + 2) - (K + 1) * (t ^ K * (1 - t ^ 2))
def χ (n m : ℕ) (t : ℝ) : ℝ := ν (n - 1 - m) t / (1 - t ^ n) ^ 2
def gC (n : ℕ) (t : ℝ) (a : ℂ) : ℂ :=
  a / (1 - a) + (1 + χ n 0 t) / 2 - ∑ m ∈ range n, χ n m t * a ^ m
def cf (N m : ℕ) (s : ℝ) : ℝ := χ (N + 1) (m + 1) (s ^ 2) / (m + 1)

lemma ν_nonneg (K : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ ν K t := by
  induction K with
  | zero => simp [ν]
  | succ K ih =>
    rw [show ν (K + 1) t = t * ν K t + (1 - t) * (1 - t ^ (K + 1)) * (1 - t ^ (K + 2)) by
      simp only [ν]; push_cast; ring]
    exact add_nonneg (mul_nonneg h0 ih) (mul_nonneg (mul_nonneg (sub_nonneg.2 h1)
      (sub_nonneg.2 (pow_le_one₀ h0 h1))) (sub_nonneg.2 (pow_le_one₀ h0 h1)))

lemma J (K : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * t * (1 - t ^ K) ≤ K * (1 - t) * (1 + t ^ (K + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have h3 := mul_nonneg (sub_nonneg.2 h1)
      (sub_nonneg.2 (one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ t - 1) (K + 2)))
    have h4 := mul_le_mul_of_nonneg_left ih h0
    simp only [pow_succ, add_sub_cancel] at *; push_cast at *; nlinarith

lemma geo (N : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    N * t ^ N * (1 - t) ≤ 1 - t ^ N ∧ 1 - t ^ N ≤ N * (1 - t) := by
  rw [← mul_neg_geom_sum t N]
  have a : ∑ i ∈ range N, t ^ i ≤ N := by
    simpa using sum_le_card_nsmul (range N) (fun i => t ^ i) 1 fun i _ => pow_le_one₀ h0 h1
  have b : N * t ^ N ≤ ∑ i ∈ range N, t ^ i := by
    simpa using card_nsmul_le_sum (range N) (fun i => t ^ i) (t ^ N) fun i hi =>
      pow_le_pow_of_le_one h0 h1 (mem_range.1 hi).le
  constructor <;> nlinarith [sub_nonneg.2 h1]

lemma χ_deriv {m K : ℕ} {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∃ d, HasDerivAt (χ (m + 1 + K) m) d t ∧ d ≤ 0 := by
  have hτ : t ^ (m + 1 + K) < 1 := pow_lt_one₀ h0.le h1 (by omega)
  have hν : HasDerivAt (ν K) _ t := ((hasDerivAt_pow (2 * K + 2) t).const_sub 1).sub
    (((hasDerivAt_pow K t).mul ((hasDerivAt_pow 2 t).const_sub 1)).const_mul ((K : ℝ) + 1))
  rw [show χ (m + 1 + K) m = ν K / (fun x => 1 - x ^ (m + 1 + K)) ^ 2 from
    funext fun x => by simp [χ]]
  refine ⟨_, hν.div (((hasDerivAt_pow (m + 1 + K) t).const_sub 1).pow 2)
    (pow_ne_zero 2 (sub_pos.2 hτ).ne'), div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)⟩
  have eK : (K : ℝ) * t ^ (K - 1) * t = K * t ^ K := by
    rcases K with _ | K <;> simp [pow_succ, mul_assoc]
  have hP : 0 < t ^ K := by positivity
  have hP1 : t ^ K ≤ 1 := pow_le_one₀ h0.le h1.le
  have hm : 0 < t ^ m := by positivity
  have hν0 := ν_nonneg K h0.le h1.le
  have hJ := J K h0.le h1.le
  obtain ⟨g1, -⟩ := geo m h0.le h1.le
  obtain ⟨-, g2⟩ := geo (K + 1) h0.le h1.le
  simp only [ν, pow_succ, show 2 * K + 2 - 1 = 2 * K + 1 by omega,
    show m + 1 + K - 1 = m + K by omega, pow_add, pow_mul, pow_zero, one_mul] at *
  push_cast at *
  set P := t ^ K
  set T := t ^ m
  simp only [mul_pow t t K, Pi.mul_apply] at *
  have h1' : 0 < 1 - t * P := by nlinarith
  have key : 2 * t * (1 - P * P * t * t - (↑K + 1) * (P * (1 - t * t))) ≤
      (2 * t * t * P + K * (1 - t * t) - 2 * t * t) * (1 - t * P) := by
    linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) (sub_nonneg.2 hJ)]
  have hB := nonneg_of_mul_nonneg_left (le_trans (by positivity) key) h1'
  have h2 : (↑m + 1 + ↑K) * T * (1 - t * P) ≤ (↑K + 1) * (1 - T * t * P) := by
    nlinarith [mul_le_mul_of_nonneg_left g2 (mul_nonneg m.cast_nonneg hm.le),
      mul_le_mul_of_nonneg_left g1 (by positivity : (0 : ℝ) ≤ K + 1)]
  have h3 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (↑m + 1 + ↑K) * T * P)
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hP.le hB)
  refine nonpos_of_mul_nonpos_left (b := t) ?_ h0
  have h5 : 0 ≤ (1 - T * t * P) * ((↑K + 1) * P * (2 * t * t * P + K * (1 - t * t) - 2 * t * t) *
      (1 - T * t * P) - 2 * (↑m + 1 + ↑K) * (1 - P * P * t * t - (↑K + 1) * (P * (1 - t * t))) *
      (T * t * P)) := mul_nonneg (by linarith) (by linarith)
  linear_combination h5 + (-(K + 1) * (1 - t * t) * (1 - T * t * P) ^ 2) * eK

lemma cf_deriv {N m : ℕ} (hm : m < N) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    ∃ d, HasDerivAt (cf N m) d s ∧ d ≤ 0 := by
  obtain ⟨K, hK⟩ : ∃ K, N + 1 = m + 1 + 1 + K := ⟨N - m - 1, by omega⟩
  obtain ⟨d, hd, hd0⟩ := χ_deriv (m := m + 1) (K := K) (t := s ^ 2) (by positivity) (by nlinarith)
  show ∃ d, HasDerivAt (fun s => χ (N + 1) (m + 1) (s ^ 2) / (m + 1)) d s ∧ d ≤ 0
  rw [hK]
  exact ⟨_, (hd.comp s (hasDerivAt_pow 2 s)).div_const _, div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hd0 (by positivity)) (by positivity)⟩

lemma refl' (n : ℕ) {z w : ℂ} (h : z * w = 1) :
    z ^ n * ∑ m ∈ range n, w ^ m = ∑ m ∈ range n, z ^ m - 1 + z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ]
    linear_combination z * ih + z * (by rw [← mul_pow, h, one_pow] : z ^ n * w ^ n = 1) +
      geom_sum_mul z n

lemma fej (n : ℕ) {z w : ℂ} (h : z * w = 1) : ∑ m ∈ range n, ((n : ℂ) - m) * (z ^ m + w ^ m) =
    n + (∑ m ∈ range n, z ^ m) * ∑ m ∈ range n, w ^ m := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [sum_range_succ, Nat.cast_succ, add_sub_right_comm, add_mul, one_mul, sum_add_distrib]
    linear_combination ih - refl' n h - refl' n (mul_comm z w ▸ h) -
      (by rw [← mul_pow, h, one_pow] : z ^ n * w ^ n = 1)

lemma hD (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : (1 - (t : ℂ) ^ (N + 1)) ≠ 0 := by
  exact_mod_cast (sub_pos.2 (pow_lt_one₀ h0.le h1 N.succ_ne_zero)).ne'

lemma ksum (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (x : ℂ) :
    (∑ m ∈ range (N + 1), (χ (N + 1) m t : ℂ) * (t * x) ^ m) * (1 - (t : ℂ) ^ (N + 1)) ^ 2 =
      ∑ m ∈ range (N + 1), (t * x) ^ m -
        t ^ 2 * ∑ m ∈ range (N + 1), (t * x) ^ m * ((t : ℂ) ^ 2) ^ (N + 1 - 1 - m) -
        (1 - t ^ 2) * t ^ N * ∑ m ∈ range (N + 1), (((N + 1 : ℕ) : ℂ) - m) * x ^ m := by
  have := hD N h0 h1
  rw [sum_mul, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_range_succ_iff.1 hm
  rw [← pow_sub_mul_pow (t : ℂ) hm']
  simp only [χ, ν, Nat.add_sub_cancel]; push_cast [Nat.cast_sub hm']; field_simp; ring

lemma circ (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {z w : ℂ} (h : z * w = 1) (hz : ‖z‖ = 1) :
    gC (N + 1) t (t * z) + gC (N + 1) t (t * w) = (t ^ N * (1 - t ^ 2) * (1 - t) ^ 2 : ℝ) *
      ((∑ m ∈ range (N + 1), z ^ m) * ∑ m ∈ range (N + 1), w ^ m) /
        ((1 - (t : ℂ) ^ (N + 1)) ^ 2 * ((1 - t * z) * (1 - t * w))) := by
  have hw : ‖w‖ = 1 := by simpa [hz] using congrArg norm h
  have hne : ∀ x : ℂ, ‖x‖ = 1 → 1 - (t : ℂ) * x ≠ 0 := fun x hx e => by
    have := congrArg norm (sub_eq_zero.1 e); simp [hx, abs_of_pos h0] at this; linarith
  have R3 : (χ (N + 1) 0 t : ℂ) * (1 - (t : ℂ) ^ (N + 1)) ^ 2 =
      1 - (t : ℂ) ^ (2 * N + 2) - (N + 1) * (t ^ N * (1 - t ^ 2)) := by
    have := hD N h0 h1
    simp only [χ, ν, Nat.add_sub_cancel, Nat.sub_zero]; push_cast; field_simp
  have hf := fej (N + 1) h
  simp only [mul_add, sum_add_distrib] at hf
  rw [eq_div_iff (mul_ne_zero (pow_ne_zero 2 (hD N h0 h1)) (mul_ne_zero (hne z hz) (hne w hw)))]
  simp only [gC]
  linear_combination (norm := (push_cast; ring1))
    ((1 - (t : ℂ) ^ (N + 1)) ^ 2 * (1 - t * w)) * div_mul_cancel₀ (t * z) (hne z hz) +
    ((1 - (t : ℂ) ^ (N + 1)) ^ 2 * (1 - t * z)) * div_mul_cancel₀ (t * w) (hne w hw) +
    ((1 - t * z) * (1 - t * w)) * R3 - ((1 - t * z) * (1 - t * w)) * ksum N h0 h1 z -
    ((1 - t * z) * (1 - t * w)) * ksum N h0 h1 w + (1 - t * w) * geom_sum_mul (t * z) (N + 1) +
    (1 - t * z) * geom_sum_mul (t * w) (N + 1) +
    ((1 - t * z) * (t * w)) * geom_sum₂_mul (t * z) ((t : ℂ) ^ 2) (N + 1) +
    ((1 - t * w) * (t * z)) * geom_sum₂_mul (t * w) ((t : ℂ) ^ 2) (N + 1) +
    ((1 - (t : ℂ) ^ 2) * t ^ N * ((1 - t * z) * (1 - t * w))) * hf +
    ((1 - (t : ℂ) ^ 2) * t ^ N * t) * ((∑ m ∈ range (N + 1), w ^ m) * (w - 1) *
      geom_sum_mul z (N + 1) + (z ^ (N + 1) - 1) * geom_sum_mul w (N + 1) -
      (∑ m ∈ range (N + 1), z ^ m) * (∑ m ∈ range (N + 1), w ^ m) * h +
      (by rw [← mul_pow, h, one_pow] : z ^ (N + 1) * w ^ (N + 1) = 1)) +
    ((t : ℂ) ^ 2 * ((∑ m ∈ range (N + 1), z ^ m) * (∑ m ∈ range (N + 1), w ^ m) * t ^ N *
      (1 - t ^ 2) - (∑ i ∈ range (N + 1), (t * z) ^ i * ((t : ℂ) ^ 2) ^ (N + 1 - 1 - i)) *
      (1 - t * z) - (∑ i ∈ range (N + 1), (t * w) ^ i * ((t : ℂ) ^ 2) ^ (N + 1 - 1 - i)) *
      (1 - t * w) + t ^ N * t * (2 - z ^ (N + 1) - w ^ (N + 1)))) * h

open ComplexConjugate in
lemma circ_re (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {a : ℂ} (ha : ‖a‖ = t) :
    0 ≤ (gC (N + 1) t a).re := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hz : ‖a / t‖ = 1 := by simp [ha, abs_of_pos h0, h0.ne']
  have h := circ N h0 h1 (z := a / t) (w := conj (a / t))
    (by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp) hz
  have e2 : (t : ℂ) * conj (a / t) = conj a := by simp [map_div₀]; field_simp
  rw [mul_div_cancel₀ _ ht, e2, show gC (N + 1) t (conj a) = conj (gC (N + 1) t a) by
    simp [gC, map_sum, map_ofNat], Complex.add_conj,
    show (1 - a) * (1 - conj a) = Complex.normSq (1 - a) by rw [← Complex.mul_conj]; simp,
    show (∑ m ∈ range (N + 1), (a / t) ^ m) * ∑ m ∈ range (N + 1), conj (a / t) ^ m =
      Complex.normSq (∑ m ∈ range (N + 1), (a / t) ^ m) by
      rw [← Complex.mul_conj]; simp [map_sum]] at h
  have h5 : 2 * (gC (N + 1) t a).re = t ^ N * (1 - t ^ 2) * (1 - t) ^ 2 *
      Complex.normSq (∑ m ∈ range (N + 1), (a / t) ^ m) /
        ((1 - t ^ (N + 1)) ^ 2 * Complex.normSq (1 - a)) := by exact_mod_cast h
  have : 0 ≤ 2 * (gC (N + 1) t a).re := h5 ▸ div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (pow_nonneg h0.le _) (by nlinarith)) (sq_nonneg _)) (Complex.normSq_nonneg _))
    (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
  linarith

lemma slit {a : ℂ} (h : ‖a‖ < 1) : 1 - a ∈ Complex.slitPlane :=
  Or.inl (by have := (Complex.abs_re_le_norm a).trans_lt h; simp; linarith [abs_lt.1 this])

lemma disc (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) {a : ℂ} (ha : ‖a‖ ≤ t) :
    0 ≤ (gC (N + 1) t a).re := by
  have hd : DiffContOnCl ℂ (fun a => Complex.exp (-gC (N + 1) t a)) (Metric.ball 0 t) := by
    refine DifferentiableOn.diffContOnCl fun a ha => DifferentiableAt.differentiableWithinAt ?_
    rw [closure_ball _ h0.ne', Metric.mem_closedBall, dist_zero_right] at ha
    have := Complex.slitPlane_ne_zero (slit (ha.trans_lt h1))
    unfold gC; fun_prop (disch := exact this)
  have := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd (C := 1)
    (fun z hz => ?_) (z := a) (by rw [closure_ball _ h0.ne']; simpa using ha)
  · simpa [Complex.norm_exp] using this
  · rw [frontier_ball _ h0.ne', mem_sphere_zero_iff_norm] at hz
    simpa [Complex.norm_exp] using circ_re N h0 h1 hz

lemma diag (N : ℕ) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : (gC (N + 1) t t).re =
    (N + 1) * t ^ (N + 1) / (1 - t ^ (N + 1)) + (N + 1) * ((1 - χ (N + 1) 0 t) / 2) := by
  have hD : 1 - t ^ (N + 1) ≠ 0 := (sub_pos.2 (pow_lt_one₀ h0.le h1 (by omega))).ne'
  have ht : 1 - t ≠ 0 := (sub_pos.2 h1).ne'
  have h := circ N h0 h1 (z := 1) (w := 1) (by simp) (by simp)
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul] at h
  have := congrArg Complex.re (h.trans (by push_cast; ring : _ = ((t ^ N * (1 - t ^ 2) *
    (1 - t) ^ 2 * ((N + 1) * (N + 1)) / ((1 - t ^ (N + 1)) ^ 2 * ((1 - t) * (1 - t))) : ℝ) : ℂ)))
  rw [Complex.ofReal_re, Complex.add_re] at this
  simp only [χ, ν, Nat.add_sub_cancel, Nat.sub_zero]
  field_simp at this ⊢
  linear_combination this

lemma entry {N : ℕ} {β : ℝ → ℂ} {k s : ℝ} {c : ℕ → ℝ}
    (hc : ∀ m, m < N → HasDerivAt (cf N m) (c m) s)
    (hβ : HasDerivWithinAt β ((k : ℂ) * β s) (Set.Ici s) s) (hn : ‖β s‖ < 1) :
    HasDerivWithinAt
      (fun x => (-Complex.log (1 - β x) - ∑ m ∈ range N, (cf N m x : ℂ) * β x ^ (m + 1)).re)
      (k * ((gC (N + 1) (s ^ 2) (β s)).re - (1 - χ (N + 1) 0 (s ^ 2)) / 2)
        - ∑ m ∈ range N, c m * (β s ^ (m + 1)).re) (Set.Ici s) s := by
  have hsum := HasDerivWithinAt.sum (u := range N) fun m hm =>
    ((hc m (mem_range.1 hm)).ofReal_comp.hasDerivWithinAt (s := Set.Ici s)).mul (hβ.pow (m + 1))
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s
    ((((hβ.const_sub 1).clog_real (slit hn)).neg).sub hsum)
  refine (this.congr (fun x _ => by simp) (by simp)).congr_deriv ?_
  have e1 : ∀ m : ℕ, (cf N m s : ℂ) * (((m + 1 : ℕ) : ℂ) * β s ^ m * (k * β s)) =
      k * ((χ (N + 1) (m + 1) (s ^ 2) : ℂ) * β s ^ (m + 1)) := fun m => by
    have : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    simp only [cf]; push_cast; field_simp; ring
  simp only [Pi.pow_apply, Nat.add_sub_cancel, e1, sum_add_distrib, ← mul_sum, gC, sum_range_succ',
    pow_zero, mul_one, Complex.reCLM_apply, neg_div, neg_neg, mul_div_assoc]
  simp [Complex.re_sum]; ring

open scoped ComplexOrder
variable {N : ℕ} (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

def lam (i : Fin (N + 1)) (s : ℝ) : ℝ := min (√(A i i).re) s / √(A i i).re
def al (i j : Fin (N + 1)) (s : ℝ) : ℂ := ((lam A i s * lam A j s : ℝ) : ℂ) * A i j
def ep (i : Fin (N + 1)) (s : ℝ) : ℝ := if s < √(A i i).re then 1 else 0
def Psi (s : ℝ) : ℝ :=
  ∑ i, (Complex.log (1 - al A i i s ^ (N + 1))).re + ∑ i, ∑ j,
    (-Complex.log (1 - al A i j s) - ∑ m ∈ range N, (cf N m s : ℂ) * al A i j s ^ (m + 1)).re

lemma al_deriv (i j : Fin (N + 1)) {s : ℝ} (hs : 0 < s) : HasDerivWithinAt (al A i j)
    (((ep A i s + ep A j s) / s : ℝ) * al A i j s) (Set.Ici s) s := by
  have hl : ∀ i, HasDerivWithinAt (lam A i) (ep A i s / s * lam A i s) (Set.Ici s) s := fun i => by
    unfold ep; split_ifs with h
    · have e : lam A i =ᶠ[nhds s] fun x => x / √(A i i).re :=
        (eventually_lt_nhds h).mono fun x hx => by simp [lam, min_eq_right hx.le]
      refine (((hasDerivAt_id s).div_const _).congr_of_eventuallyEq
        e).hasDerivWithinAt.congr_deriv ?_
      simp [lam, min_eq_right h.le]; field_simp
    · refine ((hasDerivWithinAt_const s _ (lam A i s)).congr (fun x hx => ?_)
        rfl).congr_deriv (by simp)
      simp [lam, min_eq_left (le_trans (not_lt.1 h) hx), min_eq_left (not_lt.1 h)]
  refine ((((hl i).mul (hl j)).ofReal_comp).mul_const (A i j)).congr_deriv ?_
  simp only [al]; push_cast; ring

lemma al_cont (i j : Fin (N + 1)) : Continuous (al A i j) :=
  (Complex.continuous_ofReal.comp (((continuous_const.min continuous_id).div_const _).mul
    ((continuous_const.min continuous_id).div_const _))).mul continuous_const

variable {A}

lemma nle (hA : A.PosSemidef) (i j : Fin (N + 1)) : ‖A i j‖ ≤ √(A i i).re * √(A j j).re := by
  have hi := Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
  have hj := Complex.nonneg_iff.1 (hA.diag_nonneg (i := j))
  have hB := (Complex.nonneg_iff.1 (hA.submatrix ![i, j]).det_nonneg).1
  rw [Matrix.det_fin_two] at hB
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ← hA.1.apply j i] at hB
  rw [← Real.sqrt_mul hi.1]
  refine Real.le_sqrt_of_sq_le ?_
  simp [Complex.mul_re, ← hi.2, ← hj.2, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hB ⊢
  linarith

lemma lam_mul (i : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    lam A i s * √(A i i).re = min (√(A i i).re) s := by
  rcases eq_or_ne (√(A i i).re) 0 with h | h <;> simp [lam, h, hs]

lemma al_norm (hA : A.PosSemidef) (i j : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    ‖al A i j s‖ ≤ s ^ 2 := by
  have hl : ∀ i, 0 ≤ lam A i s := fun i =>
    div_nonneg (le_min (Real.sqrt_nonneg _) hs) (Real.sqrt_nonneg _)
  have hm := mul_le_mul (min_le_right (√(A i i).re) s) (min_le_right (√(A j j).re) s)
    (le_min (Real.sqrt_nonneg _) hs) hs
  rw [← lam_mul i hs, ← lam_mul j hs] at hm
  rw [al, norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (hl i) (hl j))]
  nlinarith [mul_le_mul_of_nonneg_left (nle hA i j) (mul_nonneg (hl i) (hl j))]

lemma al_diag (hA : A.PosSemidef) (i : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    al A i i s = ((min (√(A i i).re) s ^ 2 : ℝ) : ℂ) := by
  have hi := Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
  have : A i i = (((√(A i i).re) ^ 2 : ℝ) : ℂ) := by
    rw [Real.sq_sqrt hi.1]; exact Complex.ext rfl (by simpa using hi.2.symm)
  rw [al, ← lam_mul i hs]; conv_lhs => arg 2; rw [this]
  push_cast; ring

lemma schur (hA : A.PosSemidef) (s : ℝ) (m : ℕ) : 0 ≤ ∑ i, ∑ j, (al A i j s ^ (m + 1)).re := by
  have hP : (A.map (· ^ (m + 1))).PosSemidef := by
    induction m with
    | zero => simpa using hA
    | succ m ih =>
      rw [show A.map (· ^ (m + 1 + 1)) = (A.map (· ^ (m + 1))).hadamard A by ext; simp [pow_succ]]
      exact ih.hadamard hA
  have e : (∑ i, ∑ j, al A i j s ^ (m + 1)) = star (fun i => ((lam A i s ^ (m + 1) : ℝ) : ℂ)) ⬝ᵥ
      ((A.map (· ^ (m + 1))).mulVec fun i => ((lam A i s ^ (m + 1) : ℝ) : ℂ)) := by
    simp only [dotProduct, Matrix.mulVec, mul_sum, al, mul_pow, Pi.star_apply, Matrix.map_apply,
      RCLike.star_def, Complex.conj_ofReal]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by push_cast; ring
  simp only [← Complex.re_sum]
  rw [e]; exact (Complex.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg _)).1

lemma step (hA : A.PosSemidef) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    ∃ d, HasDerivWithinAt (Psi A) d (Set.Ici s) s ∧ 0 ≤ d := by
  choose! c hc hc0 using fun m (hm : m < N) => cf_deriv hm h0 h1
  have ht0 : 0 < s ^ 2 := by positivity
  have ht1 : s ^ 2 < 1 := by nlinarith
  have hn := fun i j => al_norm hA i j h0.le
  set k : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => (ep A i s + ep A j s) / s with hk
  set δ : ℝ := (N + 1) * (s ^ 2) ^ (N + 1) / (1 - (s ^ 2) ^ (N + 1)) with hδ
  have hcap : ∀ i, s < √(A i i).re → al A i i s = ((s ^ 2 : ℝ) : ℂ) := fun i h => by
    rw [al_diag hA i h0.le, min_eq_right h.le]
  have hunc : ∀ i, ¬ s < √(A i i).re → k i i = 0 := fun i h => by simp [hk, ep, h]
  have hD : ∀ i, HasDerivWithinAt (fun x => (Complex.log (1 - al A i i x ^ (N + 1))).re)
      (-(k i i) * δ) (Set.Ici s) s := fun i => by
    have hs : 1 - al A i i s ^ (N + 1) ∈ Complex.slitPlane := slit (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) ((hn i i).trans_lt ht1) (by omega))
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s
      ((((al_deriv A i i h0).pow (N + 1)).const_sub 1).clog_real hs)
    refine (this.congr (fun x _ => by simp) (by simp)).congr_deriv ?_
    by_cases h : s < √(A i i).re
    · simp only [Pi.pow_apply, Complex.reCLM_apply, Nat.add_sub_cancel]
      rw [hcap i h,
        show (-(((N + 1 : ℕ) : ℂ) * ((s ^ 2 : ℝ) : ℂ) ^ N * (((ep A i s + ep A i s) / s : ℝ) *
          ((s ^ 2 : ℝ) : ℂ))) / (1 - ((s ^ 2 : ℝ) : ℂ) ^ (N + 1))) = ((-(k i i) * δ : ℝ) : ℂ) by
          simp only [hk, hδ]; push_cast; ring, Complex.ofReal_re]
    · have hz : (ep A i s + ep A i s) / s = 0 := hunc i h
      simp [hz, hunc i h]
  refine ⟨_, ((HasDerivWithinAt.sum (u := univ) fun i _ => hD i).add
    (HasDerivWithinAt.sum (u := univ) fun i _ => HasDerivWithinAt.sum (u := univ)
      fun j _ => entry hc (al_deriv A i j h0) ((hn i j).trans_lt ht1))).congr
        (fun x _ => by simp [Psi]) (by simp [Psi]), ?_⟩
  set g : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => (gC (N + 1) (s ^ 2) (al A i j s)).re with hg
  set cb : ℝ := (1 - χ (N + 1) 0 (s ^ 2)) / 2 with hcb
  have he0 : ∀ i, 0 ≤ ep A i s := fun i => by unfold ep; split_ifs <;> norm_num
  have h2 : ∑ i, ∑ j, k i j * g i j ≥ ∑ i, k i i * g i i := sum_le_sum fun i _ =>
    single_le_sum (f := fun j => k i j * g i j) (fun j _ => mul_nonneg
      (div_nonneg (add_nonneg (he0 i) (he0 j)) h0.le) (disc N ht0 ht1 (hn i j))) (mem_univ i)
  have h3 : ∑ i, ∑ j, k i j = (N + 1) * ∑ i, k i i := by
    simp only [hk, ← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_sum, mul_div_assoc]
    push_cast; ring
  have h4 : ∑ i, ∑ j, ∑ m ∈ range N, c m * (al A i j s ^ (m + 1)).re ≤ 0 := by
    rw [sum_congr rfl fun i _ => sum_comm, sum_comm]
    simp only [← mul_sum]
    exact sum_nonpos fun m hm => mul_nonpos_of_nonpos_of_nonneg (hc0 m (mem_range.1 hm))
      (schur hA s m)
  have e3 : ∑ i, k i i * g i i = (∑ i, k i i) * (δ + (N + 1) * cb) := by
    rw [sum_mul]; refine sum_congr rfl fun i _ => ?_
    by_cases h : s < √(A i i).re
    · simp only [hg, hcap i h, diag N ht0 ht1, hδ, hcb]
    · rw [hunc i h, zero_mul, zero_mul]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, sum_neg_distrib]
  simp only [hk, hg] at h2 h3 e3
  rw [h3]; linarith

open Filter Topology in
theorem flow (hA : A.PosSemidef) {s0 : ℝ} (h0 : 0 < s0) (h1 : s0 < 1) :
    ∏ i, ∏ j, ‖1 - al A i j s0‖ ≤ ∏ i, ‖1 - al A i i s0 ^ (N + 1)‖ := by
  have hn : ∀ i j, ∀ x ∈ Set.Icc 0 s0, ‖al A i j x‖ < 1 := fun i j x hx =>
    (al_norm hA i j hx.1).trans_lt (by nlinarith [hx.1, hx.2])
  have hn' : ∀ i, ∀ x ∈ Set.Icc 0 s0, ‖al A i i x ^ (N + 1)‖ < 1 := fun i x hx => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (hn i i x hx) (by omega)
  have hcf : ∀ m, ContinuousOn (cf N m) (Set.Icc 0 s0) := fun m => by
    have hν : ∀ K, Continuous (ν K) := fun K => by unfold ν; fun_prop
    have h2 : Continuous fun s : ℝ => (1 - (s ^ 2) ^ (N + 1)) ^ 2 := by fun_prop
    refine (ContinuousOn.div ((hν _).comp (continuous_pow 2)).continuousOn h2.continuousOn
      fun x hx => pow_ne_zero 2 (sub_pos.2 (pow_lt_one₀ (by positivity)
        (by nlinarith [hx.1, hx.2] : x ^ 2 < 1) N.succ_ne_zero)).ne').div_const _
  have c1 : ContinuousOn (fun s => ∑ i, (Complex.log (1 - al A i i s ^ (N + 1))).re)
      (Set.Icc 0 s0) := continuousOn_finsetSum _ fun i _ =>
    Complex.continuous_re.comp_continuousOn (ContinuousOn.clog
      (continuous_const.sub ((al_cont A i i).pow _)).continuousOn fun x hx => slit (hn' i x hx))
  have c2 : ContinuousOn (fun s => ∑ i, ∑ j, (-Complex.log (1 - al A i j s) -
      ∑ m ∈ range N, (cf N m s : ℂ) * al A i j s ^ (m + 1)).re) (Set.Icc 0 s0) := by
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    refine Complex.continuous_re.comp_continuousOn (ContinuousOn.sub (ContinuousOn.clog
      (continuous_const.sub (al_cont A i j)).continuousOn fun x hx => slit (hn i j x hx)).neg ?_)
    exact continuousOn_finsetSum _ fun m _ => (Complex.continuous_ofReal.comp_continuousOn
      (hcf m)).mul ((al_cont A i j).pow _).continuousOn
  have hc : ContinuousOn (Psi A) (Set.Icc 0 s0) := c1.add c2
  have hmono : ∀ s1 ∈ Set.Ioc 0 s0, Psi A s1 ≤ Psi A s0 := fun s1 hs1 => by
    choose! d hd hd0 using fun x (hx : x ∈ Set.Ico s1 s0) =>
      step hA (hs1.1.trans_le hx.1) (hx.2.trans h1)
    exact image_le_of_deriv_right_le_deriv_boundary (f := fun _ => Psi A s1) (f' := fun _ => 0)
      continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) le_rfl
      (hc.mono (Set.Icc_subset_Icc hs1.1.le le_rfl)) hd (fun x hx => hd0 x hx)
      (Set.right_mem_Icc.2 hs1.2)
  have hl0 : ∀ i, lam A i 0 = 0 := fun i => by simp [lam, min_eq_right (Real.sqrt_nonneg _)]
  have hpos : 0 ≤ Psi A s0 := by
    have := left_nhdsWithin_Ioc_neBot h0
    have ht : Tendsto (Psi A) (𝓝[Set.Ioc 0 s0] 0) (𝓝 (Psi A 0)) :=
      (hc 0 ⟨le_rfl, h0.le⟩).mono_left (nhdsWithin_mono 0 Set.Ioc_subset_Icc_self)
    rw [show Psi A 0 = 0 by simp [Psi, al, hl0]] at ht
    exact le_of_tendsto ht (eventually_mem_nhdsWithin.mono hmono)
  have hs0 : s0 ∈ Set.Icc 0 s0 := ⟨h0.le, le_rfl⟩
  have hS : 0 ≤ ∑ i, ∑ j, ∑ m ∈ range N, cf N m s0 * (al A i j s0 ^ (m + 1)).re := by
    rw [sum_congr rfl fun i _ => sum_comm, sum_comm]
    simp only [← mul_sum]
    exact sum_nonneg fun m hm => mul_nonneg (div_nonneg (div_nonneg
      (ν_nonneg _ (by positivity) (by nlinarith)) (sq_nonneg _)) (by positivity)) (schur hA s0 m)
  have key : ∑ i, ∑ j, Real.log ‖1 - al A i j s0‖ ≤ ∑ i, Real.log ‖1 - al A i i s0 ^ (N + 1)‖ := by
    simp only [Psi, Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.re_sum,
      Complex.re_ofReal_mul, sum_sub_distrib, sum_neg_distrib] at hpos
    linarith
  have hp : ∀ i j, 0 < ‖1 - al A i j s0‖ := fun i j =>
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (slit (hn i j s0 hs0)))
  have hp' : ∀ i, 0 < ‖1 - al A i i s0 ^ (N + 1)‖ := fun i =>
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (slit (hn' i s0 hs0)))
  rw [← Real.log_le_log_iff (prod_pos fun i _ => prod_pos fun j _ => hp i j)
    (prod_pos fun i _ => hp' i), Real.log_prod fun i _ => (prod_pos fun j _ => hp i j).ne',
    Real.log_prod fun i _ => (hp' i).ne']
  simpa only [Real.log_prod fun j _ => (hp _ j).ne'] using key

theorem core (hA : A.PosSemidef) (hd : ∀ i, (A i i).re ≤ 1) :
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ (N + 1)‖ := by
  have hb : ∀ i, √(A i i).re ≤ 1 := fun i => Real.sqrt_le_one.2 (hd i)
  have e : ∀ i j, al A i j 1 = A i j := fun i j => by
    by_cases h : √(A i i).re * √(A j j).re = 0
    · have := nle hA i j
      rw [h] at this
      simp [al, norm_le_zero_iff.1 this]
    · obtain ⟨hi, hj⟩ := mul_ne_zero_iff.1 h
      simp [al, lam, min_eq_left (hb i), min_eq_left (hb j), hi, hj]
  have hcl : IsClosed {s : ℝ | ∏ i, ∏ j, ‖1 - al A i j s‖ ≤ ∏ i, ‖1 - al A i i s ^ (N + 1)‖} :=
    isClosed_le (continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ =>
      (continuous_const.sub (al_cont A i j)).norm) (continuous_finsetProd _ fun i _ =>
      (continuous_const.sub ((al_cont A i i).pow _)).norm)
  simpa [e] using hcl.closure_subset_iff.2 (fun s (hs : s ∈ Set.Ioo 0 1) => flow hA hs.1 hs.2)
    (by rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ closure (Set.Ioo 0 1))

lemma scal {μ : ℝ} (hμ : 1 ≤ μ) {z : ℂ} (hz : ‖z‖ ≤ μ) :
    ‖1 - z‖ ≤ μ * ‖1 - z / (μ ^ 2 : ℝ)‖ := by
  have h0 : 0 < μ := by linarith
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ μ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg z) hz 2
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at this
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im]
  field_simp
  nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ μ ^ 2 - 1) (sub_nonneg.2 h2)]

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖ := by
  rintro (_ | N) A hA
  · simp
  set σ : Fin (N + 1) → ℝ := fun i => √(max 1 (A i i).re) with hσ
  have hσ1 : ∀ i, 1 ≤ σ i := fun i => Real.one_le_sqrt.2 (le_max_left _ _)
  have hσ2 : ∀ i, σ i ^ 2 = max 1 (A i i).re := fun i => Real.sq_sqrt (by positivity)
  have hd := fun i => Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
  set D : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
    Matrix.diagonal fun i => (((σ i ^ 2)⁻¹ : ℝ) : ℂ) with hD
  have hB : (D * A * D.conjTranspose).PosSemidef := hA.mul_mul_conjTranspose_same D
  have eB : ∀ i j, (D * A * D.conjTranspose) i j = A i j / ((σ i * σ j) ^ 2 : ℝ) := fun i j => by
    have := (zero_lt_one.trans_le (hσ1 i)).ne'
    have := (zero_lt_one.trans_le (hσ1 j)).ne'
    simp [hD, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    field_simp
  have h := core hB fun i => by
    rw [eB, Complex.div_ofReal_re, ← sq, ← pow_mul, div_le_one (by have := hσ1 i; positivity)]
    have h1 := le_max_left 1 (A i i).re
    have h2 := le_max_right 1 (A i i).re
    rw [← hσ2 i] at h1 h2
    rw [show σ i ^ (2 * 2) = σ i ^ 2 * σ i ^ 2 by ring]
    nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg (σ i))]
  calc ∏ i, ∏ j, ‖1 - A i j‖
      ≤ ∏ i, ∏ j, (σ i * σ j) * ‖1 - (D * A * D.conjTranspose) i j‖ :=
        prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => norm_nonneg _) fun i _ =>
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => by
            rw [eB]
            exact scal (one_le_mul_of_one_le_of_one_le (hσ1 i) (hσ1 j)) ((nle hA i j).trans
              (mul_le_mul (Real.sqrt_le_sqrt (le_max_right _ _))
                (Real.sqrt_le_sqrt (le_max_right _ _)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
    _ = (∏ i, σ i ^ (2 * (N + 1))) * ∏ i, ∏ j, ‖1 - (D * A * D.conjTranspose) i j‖ := by
        simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow]; ring
    _ ≤ (∏ i, σ i ^ (2 * (N + 1))) * ∏ i, ‖1 - (D * A * D.conjTranspose) i i ^ (N + 1)‖ :=
        mul_le_mul_of_nonneg_left h (prod_nonneg fun i _ => by have := hσ1 i; positivity)
    _ = ∏ i, ‖1 - A i i ^ (N + 1)‖ := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        have ha : A i i = ((A i i).re : ℂ) := Complex.ext rfl (by simpa using (hd i).2.symm)
        rw [eB, ha]
        set d := (A i i).re
        rw [show (1 - ((d : ℂ) / ((σ i * σ i) ^ 2 : ℝ)) ^ (N + 1)) =
            ((1 - (d / (σ i * σ i) ^ 2) ^ (N + 1) : ℝ) : ℂ) by push_cast; ring,
          show 1 - (d : ℂ) ^ (N + 1) = ((1 - d ^ (N + 1) : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        rcases le_total d 1 with h | h
        · have : σ i = 1 := by simp [hσ, d, max_eq_left h]
          simp [this]
        · have e1 : σ i ^ (2 * (N + 1)) = d ^ (N + 1) := by rw [pow_mul, hσ2, max_eq_right h]
          have e2 : d / (σ i * σ i) ^ 2 = d⁻¹ := by rw [← sq, hσ2, max_eq_right h]; field_simp
          rw [e1, e2, inv_pow, abs_of_nonneg (sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ h))),
            abs_of_nonpos (sub_nonpos.2 (one_le_pow₀ h))]
          field_simp; ring

end
end Short
