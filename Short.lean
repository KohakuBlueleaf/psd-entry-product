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

lemma χ_deriv {n m : ℕ} (hm : m < n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) :
    ∃ d, HasDerivAt (χ n m) d t ∧ (0 < t → d ≤ 0) := by
  obtain ⟨K, rfl⟩ : ∃ K, n = m + 1 + K := ⟨n - 1 - m, by omega⟩
  have hτ : t ^ (m + 1 + K) < 1 := pow_lt_one₀ h0 h1 (by omega)
  have hν : HasDerivAt (ν K) _ t := ((hasDerivAt_pow (2 * K + 2) t).const_sub 1).sub
    (((hasDerivAt_pow K t).mul ((hasDerivAt_pow 2 t).const_sub 1)).const_mul ((K : ℝ) + 1))
  rw [show χ (m + 1 + K) m = ν K / (fun x => 1 - x ^ (m + 1 + K)) ^ 2 from
    funext fun x => by simp [χ]]
  refine ⟨_, hν.div (((hasDerivAt_pow (m + 1 + K) t).const_sub 1).pow 2)
    (pow_ne_zero 2 (sub_pos.2 hτ).ne'), fun h0 => div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)⟩
  have eK : (K : ℝ) * t ^ (K - 1) * t = K * t ^ K := by
    rcases K with _ | K <;> simp [pow_succ, mul_assoc]
  have hP : 0 < t ^ K := by positivity
  have hP1 : t ^ K ≤ 1 := pow_le_one₀ h0.le h1.le
  have hT : 0 < t ^ m := by positivity
  have hν0 := ν_nonneg K h0.le h1.le
  have hJ := J K h0.le h1.le
  have g1 : m * t ^ m * (1 - t) ≤ 1 - t ^ m := by
    have := pow_le_one₀ (n := m) (by nlinarith : 0 ≤ t * (1 + (1 - t))) (by nlinarith)
    nlinarith [mul_pow t (1 + (1 - t)) m, mul_le_mul_of_nonneg_left
      (one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ 1 - t) m) hT.le]
  have g2 := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ t - 1) (K + 1)
  simp only [ν, pow_succ, show 2 * K + 2 - 1 = 2 * K + 1 by omega,
    show m + 1 + K - 1 = m + K by omega, pow_add, pow_mul, pow_zero, one_mul, add_sub_cancel] at *
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
    nlinarith [mul_le_mul_of_nonneg_left g2 (mul_nonneg m.cast_nonneg hT.le),
      mul_le_mul_of_nonneg_left g1 (by positivity : (0 : ℝ) ≤ K + 1)]
  have h3 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (↑m + 1 + ↑K) * T * P)
  have h4 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hP.le hB)
  refine nonpos_of_mul_nonpos_left (b := t) ?_ h0
  have h5 : 0 ≤ (1 - T * t * P) * ((↑K + 1) * P * (2 * t * t * P + K * (1 - t * t) - 2 * t * t) *
      (1 - T * t * P) - 2 * (↑m + 1 + ↑K) * (1 - P * P * t * t - (↑K + 1) * (P * (1 - t * t))) *
      (T * t * P)) := mul_nonneg (by linarith) (by linarith)
  linear_combination h5 + (-(K + 1) * (1 - t * t) * (1 - T * t * P) ^ 2) * eK

lemma cf_deriv {N m : ℕ} (hm : m < N) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    ∃ d, HasDerivAt (cf N m) d s ∧ (0 < s → d ≤ 0) := by
  obtain ⟨d, hd, hd0⟩ := χ_deriv (n := N + 1) (m := m + 1) (by omega) (t := s ^ 2)
    (by positivity) (by nlinarith)
  exact ⟨_, (hd.comp s (hasDerivAt_pow 2 s)).div_const _, fun h => div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (hd0 (by positivity)) (by positivity)) (by positivity)⟩

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
    (hβ : HasDerivWithinAt β ((k : ℂ) * β s) (Set.Ici s) s) (hn : ‖β s‖ < 1) : HasDerivWithinAt
      (fun x => -Complex.log (1 - β x) - ∑ m ∈ range N, (cf N m x : ℂ) * β x ^ (m + 1))
      (k * (gC (N + 1) (s ^ 2) (β s) - ((1 - χ (N + 1) 0 (s ^ 2)) / 2 : ℝ))
        - ∑ m ∈ range N, c m * β s ^ (m + 1)) (Set.Ici s) s := by
  refine ((((hβ.const_sub 1).clog_real (slit hn)).neg).sub (HasDerivWithinAt.fun_sum fun m hm =>
    ((hc m (mem_range.1 hm)).ofReal_comp.hasDerivWithinAt (s := Set.Ici s)).fun_mul
      (hβ.fun_pow (m + 1)))).congr_deriv ?_
  have e1 : ∀ m : ℕ, (cf N m s : ℂ) * (((m + 1 : ℕ) : ℂ) * β s ^ m * (k * β s)) =
      k * ((χ (N + 1) (m + 1) (s ^ 2) : ℂ) * β s ^ (m + 1)) := fun m => by
    have : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
    simp only [cf]; push_cast; field_simp; ring
  simp only [Nat.add_sub_cancel, e1, sum_add_distrib, ← mul_sum, gC, sum_range_succ', pow_zero,
    mul_one, neg_div, neg_neg, mul_div_assoc]
  push_cast; ring

open scoped ComplexOrder
variable {N : ℕ} {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}

def sc (v : Fin (N + 1) → ℝ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ := .of fun i j => ((v i * v j : ℝ) : ℂ) * A i j

lemma sc_psd (hA : A.PosSemidef) (v : Fin (N + 1) → ℝ) : (sc v A).PosSemidef := by
  convert hA.mul_mul_conjTranspose_same (Matrix.diagonal fun i => (v i : ℂ)) using 1
  ext i j
  simp [sc, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]; ring

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

lemma dre (hA : A.PosSemidef) (i : Fin (N + 1)) : A i i = ((√(A i i).re ^ 2 : ℝ) : ℂ) := by
  have hi := Complex.nonneg_iff.1 (hA.diag_nonneg (i := i))
  rw [Real.sq_sqrt hi.1]; exact Complex.ext rfl (by simpa using hi.2.symm)

lemma schur (hA : A.PosSemidef) (m : ℕ) : 0 ≤ ∑ i, ∑ j, (A i j ^ (m + 1)).re := by
  have hP : (A.map (· ^ (m + 1))).PosSemidef := by
    induction m with
    | zero => simpa using hA
    | succ m ih =>
      rw [show A.map (· ^ (m + 1 + 1)) = (A.map (· ^ (m + 1))).hadamard A by ext; simp [pow_succ]]
      exact ih.hadamard hA
  simpa [dotProduct, Matrix.mulVec] using
    (Complex.nonneg_iff.1 (hP.dotProduct_mulVec_nonneg fun _ => 1)).1

variable (A) in
def lam (i : Fin (N + 1)) (s : ℝ) : ℝ := min (√(A i i).re) s / √(A i i).re
variable (A) in
def al (i j : Fin (N + 1)) (s : ℝ) : ℂ := sc (fun i => lam A i s) A i j
variable (A) in
def ep (i : Fin (N + 1)) (s : ℝ) : ℝ := if s < √(A i i).re then 1 else 0
variable (A) in
def Psi (s : ℝ) : ℂ := ∑ i, Complex.log (1 - al A i i s ^ (N + 1)) + ∑ i, ∑ j,
  (-Complex.log (1 - al A i j s) - ∑ m ∈ range N, (cf N m s : ℂ) * al A i j s ^ (m + 1))

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
  simp only [al, sc, Matrix.of_apply]; push_cast; ring

@[fun_prop]
lemma al_cont (i j : Fin (N + 1)) : Continuous (al A i j) := by
  unfold al sc lam; simp only [Matrix.of_apply]; fun_prop

lemma lam_mul (i : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    lam A i s * √(A i i).re = min (√(A i i).re) s := by
  rcases eq_or_ne (√(A i i).re) 0 with h | h <;> simp [lam, h, hs]

lemma al_diag (hA : A.PosSemidef) (i : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    al A i i s = ((min (√(A i i).re) s ^ 2 : ℝ) : ℂ) := by
  rw [al, sc, Matrix.of_apply, ← lam_mul i hs]; conv_lhs => arg 2; rw [dre hA i]
  push_cast; ring

lemma al_norm (hA : A.PosSemidef) (i j : Fin (N + 1)) {s : ℝ} (hs : 0 ≤ s) :
    ‖al A i j s‖ ≤ s ^ 2 := by
  have e : ∀ i, √(al A i i s).re ≤ s := fun i => by
    rw [al_diag hA i hs, Complex.ofReal_re, Real.sqrt_sq (le_min (Real.sqrt_nonneg _) hs)]
    exact min_le_right _ _
  exact (nle (sc_psd hA _) i j).trans ((mul_le_mul (e i) (e j) (Real.sqrt_nonneg _) hs).trans_eq
    (sq s).symm)

lemma step (hA : A.PosSemidef) {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    ∃ d, HasDerivWithinAt (Psi A) d (Set.Ici s) s ∧ 0 ≤ d.re := by
  choose! c hc hc0 using fun m (hm : m < N) => cf_deriv hm h0.le h1
  have ht0 : 0 < s ^ 2 := by positivity
  have ht1 : s ^ 2 < 1 := by nlinarith
  have hn := fun i j => (al_norm hA i j h0.le).trans_lt ht1
  set k : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => (ep A i s + ep A j s) / s with hk
  set δ : Fin (N + 1) → ℂ := fun i =>
    (N + 1) * al A i i s ^ (N + 1) / (1 - al A i i s ^ (N + 1)) with hδ
  have hD : ∀ i, HasDerivWithinAt (fun x => Complex.log (1 - al A i i x ^ (N + 1)))
      (-(k i i * δ i)) (Set.Ici s) s := fun i =>
    ((((al_deriv i i h0).fun_pow (N + 1)).const_sub 1).clog_real (slit (by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (hn i i) (by omega)))).congr_deriv (by
        simp only [Nat.add_sub_cancel, hk, hδ]; push_cast; ring)
  refine ⟨_, (HasDerivWithinAt.fun_sum fun i _ => hD i).add (HasDerivWithinAt.fun_sum fun i _ =>
    HasDerivWithinAt.fun_sum fun j _ => entry hc (al_deriv i j h0) (hn i j)), ?_⟩
  set g : Fin (N + 1) → Fin (N + 1) → ℝ := fun i j => (gC (N + 1) (s ^ 2) (al A i j s)).re with hg
  have he0 : ∀ i, 0 ≤ ep A i s := fun i => by unfold ep; split_ifs <;> norm_num
  have h2 : ∑ i, k i i * g i i ≤ ∑ i, ∑ j, k i j * g i j := sum_le_sum fun i _ =>
    single_le_sum (f := fun j => k i j * g i j) (fun j _ => mul_nonneg (div_nonneg
      (add_nonneg (he0 i) (he0 j)) h0.le) (disc N ht0 ht1 (al_norm hA i j h0.le))) (mem_univ i)
  have h3 : ∑ i, ∑ j, k i j = (N + 1) * ∑ i, k i i := by
    simp only [hk, ← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← mul_sum]
    push_cast; ring
  have h4 : ∑ i, ∑ j, ∑ m ∈ range N, c m * (al A i j s ^ (m + 1)).re ≤ 0 := by
    rw [sum_congr rfl fun i _ => sum_comm, sum_comm]
    simp only [← mul_sum]
    exact sum_nonpos fun m hm => mul_nonpos_of_nonpos_of_nonneg (hc0 m (mem_range.1 hm) h0)
      (schur (sc_psd hA _) m)
  have e3 : ∀ i, k i i * g i i =
      k i i * ((δ i).re + (N + 1) * ((1 - χ (N + 1) 0 (s ^ 2)) / 2)) := fun i => by
    by_cases h : s < √(A i i).re
    · simp only [hg, hδ, al_diag hA i h0.le, min_eq_right h.le, diag N ht0 ht1]
      norm_cast
    · simp [hk, ep, h]
  simp only [e3] at h2
  simp only [Complex.add_re, Complex.re_sum, Complex.sub_re, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.ofReal_re]
  simp only [mul_sub, mul_add, sum_sub_distrib, sum_add_distrib, ← sum_mul, sum_neg_distrib] at h2 ⊢
  simp only [hk, hg] at h2 h3 ⊢
  rw [h3]; linarith

theorem flow (hA : A.PosSemidef) {s0 : ℝ} (h0 : 0 < s0) (h1 : s0 < 1) :
    ∏ i, ∏ j, ‖1 - al A i j s0‖ ≤ ∏ i, ‖1 - al A i i s0 ^ (N + 1)‖ := by
  have hn : ∀ i j, ∀ x ∈ Set.Icc 0 s0, ‖al A i j x‖ < 1 := fun i j x hx =>
    (al_norm hA i j hx.1).trans_lt (by nlinarith [hx.1, hx.2])
  have hn' : ∀ i, ∀ x ∈ Set.Icc 0 s0, ‖al A i i x ^ (N + 1)‖ < 1 := fun i x hx => by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (hn i i x hx) (by omega)
  have hcf : ∀ m, m < N → ContinuousOn (cf N m) (Set.Icc 0 s0) := fun m hm x hx =>
    (cf_deriv hm hx.1 (hx.2.trans_lt h1)).choose_spec.1.continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun s => (Psi A s).re) (Set.Icc 0 s0) := by
    unfold Psi
    exact Complex.continuous_re.comp_continuousOn (.add (continuousOn_finsetSum _ fun i _ =>
      .clog (continuous_const.sub ((al_cont i i).pow _)).continuousOn fun x hx => slit (hn' i x hx))
      (continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => .sub (.neg (.clog
        (continuous_const.sub (al_cont i j)).continuousOn fun x hx => slit (hn i j x hx)))
        (continuousOn_finsetSum _ fun m hm => .mul (Complex.continuous_ofReal.comp_continuousOn
          (hcf m (mem_range.1 hm))) ((al_cont i j).pow _).continuousOn)))
  have hmono : ∀ s1 ∈ Set.Ioc 0 s0, (Psi A s1).re ≤ (Psi A s0).re := fun s1 hs1 => by
    choose! d hd hd0 using fun x (hx : x ∈ Set.Ico s1 s0) =>
      step hA (hs1.1.trans_le hx.1) (hx.2.trans h1)
    exact image_le_of_deriv_right_le_deriv_boundary (f := fun _ => (Psi A s1).re) (f' := fun _ => 0)
      continuousOn_const (fun x _ => hasDerivWithinAt_const _ _ _) le_rfl
      (hc.mono (Set.Icc_subset_Icc hs1.1.le le_rfl))
      (fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt x (hd x hx))
      (fun x hx => hd0 x hx) (Set.right_mem_Icc.2 hs1.2)
  have hpos := ContinuousWithinAt.closure_le (f := fun s => (Psi A s).re)
    (g := fun _ => (Psi A s0).re) (by rw [closure_Ioc h0.ne]; exact ⟨le_rfl, h0.le⟩)
    ((hc 0 ⟨le_rfl, h0.le⟩).mono Set.Ioc_subset_Icc_self) continuousWithinAt_const hmono
  rw [show Psi A 0 = 0 by simp [Psi, al, sc, lam]] at hpos
  have hs0 : s0 ∈ Set.Icc 0 s0 := ⟨h0.le, le_rfl⟩
  have hS : 0 ≤ ∑ i, ∑ j, ∑ m ∈ range N, cf N m s0 * (al A i j s0 ^ (m + 1)).re := by
    rw [sum_congr rfl fun i _ => sum_comm, sum_comm]
    simp only [← mul_sum]
    exact sum_nonneg fun m hm => mul_nonneg (div_nonneg (div_nonneg
      (ν_nonneg _ (by positivity) (by nlinarith)) (sq_nonneg _)) (by positivity))
      (schur (sc_psd hA _) m)
  have hp : ∀ i j, 0 < ‖1 - al A i j s0‖ := fun i j =>
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (slit (hn i j s0 hs0)))
  have hp' : ∀ i, 0 < ‖1 - al A i i s0 ^ (N + 1)‖ := fun i =>
    norm_pos_iff.2 (Complex.slitPlane_ne_zero (slit (hn' i s0 hs0)))
  simp only [Psi, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.re_sum,
    Complex.re_ofReal_mul, sum_sub_distrib, sum_neg_distrib, Complex.zero_re] at hpos
  calc ∏ i, ∏ j, ‖1 - al A i j s0‖ = Real.exp (∑ i, ∑ j, Real.log ‖1 - al A i j s0‖) := by
        simp [Real.exp_sum, Real.exp_log, hp]
    _ ≤ Real.exp (∑ i, Real.log ‖1 - al A i i s0 ^ (N + 1)‖) := Real.exp_le_exp.2 (by linarith)
    _ = _ := by simp [Real.exp_sum, Real.exp_log, hp']

theorem core (hA : A.PosSemidef) (hd : ∀ i, (A i i).re ≤ 1) :
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ (N + 1)‖ := by
  have hb : ∀ i, √(A i i).re ≤ 1 := fun i => Real.sqrt_le_one.2 (hd i)
  have e : ∀ i j, al A i j 1 = A i j := fun i j => by
    have := nle hA i j
    by_cases hi : √(A i i).re = 0 <;> by_cases hj : √(A j j).re = 0 <;>
      simp_all [al, sc, lam]
  have hcl : IsClosed {s : ℝ | ∏ i, ∏ j, ‖1 - al A i j s‖ ≤ ∏ i, ‖1 - al A i i s ^ (N + 1)‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  simpa [e] using hcl.closure_subset_iff.2 (fun s (hs : s ∈ Set.Ioo 0 1) => flow hA hs.1 hs.2)
    (by rw [closure_Ioo zero_ne_one]; exact ⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ closure (Set.Ioo 0 1))

lemma scal {μ c : ℝ} (hμ : 1 ≤ μ) (h0 : 0 ≤ c) (hc : c * μ ^ 2 = 1) {z : ℂ} (hz : ‖z‖ ≤ μ) :
    ‖1 - z‖ ≤ μ * ‖1 - c * z‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ μ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg z) hz 2
    rwa [Complex.sq_norm, Complex.normSq_apply, ← sq, ← sq] at this
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.re_ofReal_mul,
    Complex.im_ofReal_mul]
  have e : μ ^ 2 * ((1 - c * z.re) * (1 - c * z.re) + (0 - c * z.im) * (0 - c * z.im)) -
      ((1 - z.re) * (1 - z.re) + (0 - z.im) * (0 - z.im)) = c * (μ ^ 2 - 1) *
        (μ ^ 2 - (z.re ^ 2 + z.im ^ 2)) := by
    linear_combination (-2 * z.re + (c + 1) * (z.re ^ 2 + z.im ^ 2) - μ ^ 2 + 1) * hc
  linarith [mul_nonneg (mul_nonneg h0 (by nlinarith : 0 ≤ μ ^ 2 - 1)) (sub_nonneg.2 h2)]

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), A.PosSemidef →
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖ := by
  rintro (_ | N) A hA
  · simp
  set μ : Fin (N + 1) → ℝ := fun i => max 1 √(A i i).re with hμ
  have h1 : ∀ i, 1 ≤ μ i := fun i => le_max_left _ _
  have hp : ∀ i, 0 < μ i := fun i => zero_lt_one.trans_le (h1 i)
  have h := core (sc_psd hA fun i => (μ i ^ 2)⁻¹) fun i => by
    have a := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right 1 _ : _ ≤ μ i) 2
    have b := one_le_pow₀ (h1 i) (n := 2)
    have := hp i
    simp only [sc, Matrix.of_apply, Complex.re_ofReal_mul]
    rw [congrArg Complex.re (dre hA i), Complex.ofReal_re, ← mul_inv,
      inv_mul_le_one₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left b (sq_nonneg (μ i))]
  calc ∏ i, ∏ j, ‖1 - A i j‖
      ≤ ∏ i, ∏ j, (μ i * μ j) * ‖1 - sc (fun i => (μ i ^ 2)⁻¹) A i j‖ :=
        prod_le_prod₀ (fun _ _ => prod_nonneg fun _ _ => norm_nonneg _) fun i _ =>
          prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ =>
            scal (one_le_mul_of_one_le_of_one_le (h1 i) (h1 j)) (by positivity)
              (by have := hp i; have := hp j; field_simp) ((nle hA i j).trans (mul_le_mul
                (le_max_right _ _) (le_max_right _ _) (Real.sqrt_nonneg _) (hp i).le))
    _ = (∏ i, μ i ^ (2 * (N + 1))) * ∏ i, ∏ j, ‖1 - sc (fun i => (μ i ^ 2)⁻¹) A i j‖ := by
        simp only [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_pow]; ring
    _ ≤ (∏ i, μ i ^ (2 * (N + 1))) * ∏ i, ‖1 - sc (fun i => (μ i ^ 2)⁻¹) A i i ^ (N + 1)‖ :=
        mul_le_mul_of_nonneg_left h (prod_nonneg fun i _ => (pow_pos (hp i) _).le)
    _ = ∏ i, ‖1 - A i i ^ (N + 1)‖ := by
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i _ => ?_
        rw [← Real.norm_of_nonneg (pow_pos (hp i) _).le, ← Complex.norm_real, ← norm_mul]
        simp only [sc, Matrix.of_apply]
        rcases le_total √(A i i).re 1 with h | h
        · simp [hμ, max_eq_left h]
        · have : (√(A i i).re : ℂ) ≠ 0 := mod_cast (zero_lt_one.trans_le h).ne'
          rw [← norm_neg, dre hA i, show μ i = √(A i i).re from max_eq_right h]
          congr 1; push_cast; field_simp
          rw [one_div, inv_pow, ← pow_mul, mul_sub, mul_inv_cancel₀ (pow_ne_zero _ this)]; ring

end
end Short
