import MatrixIneq.TauKernel
import MatrixIneq.Small

/-!
# Step 5: the main theorem

`mainTheorem : Statement.MainTheorem`, unconditionally.

The proof is the certificate method with the τ-kernel of `MatrixIneq/TauKernel.lean` as the cross
coefficient kernel:

* `KCertificate`: a certificate whose cross coefficients are a general kernel `κ m s t` that is positive
  semidefinite (in the cone form used by the Schur step) and equals `c m s` on the diagonal;
* `reducedAt_of_kcertificate`: such a certificate implies `ReducedAt n`;
* `tauCertificate`: the Fejér coefficients `coef n` together with the τ-kernel form a `KCertificate`;
* `mainTheorem`.

A written version of the proof is in `docs/PROOF.md`.
-/

open scoped ComplexOrder
open Finset Matrix

namespace MatrixIneq

/-- A certificate with a general positive semidefinite cross kernel. -/
structure KCertificate (n : ℕ) where
  /-- the degree -/
  D : ℕ
  /-- the diagonal coefficient functions -/
  c : ℕ → ℝ → ℝ
  /-- the cross coefficient kernel -/
  κ : ℕ → ℝ → ℝ → ℝ
  nonneg : ∀ m, 1 ≤ m → ∀ s, 0 ≤ s → 0 ≤ c m s
  total : ∀ s, 0 ≤ s →
    -Real.log (∑ k ∈ range n, s ^ k) ≤ ((n : ℝ) - 1) * c 0 s - ∑ m ∈ Icc 1 D, c m s
  diag : ∀ m, 1 ≤ m → ∀ s, 0 ≤ s → κ m s s = c m s
  psd : ∀ m ∈ Icc 1 D, ∀ s : Fin n → ℝ, (∀ i, 0 ≤ s i) → ∀ G : Fin n → Fin n → ℝ,
    (∀ φ : Fin n → ℝ, (∀ i, 0 ≤ φ i) → 0 ≤ ∑ i, ∑ j, φ i * φ j * G i j) →
      0 ≤ ∑ i, ∑ j, κ m (s i) (s j) * G i j
  circle : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ z : ℂ, ‖z‖ = 1 →
    ‖1 - (Real.sqrt (s * t) : ℂ) * z‖ ≤
      Real.exp (-(harm ((c 0 s + c 0 t) / 2) (fun m => κ m s t) D z))

section main

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}

/-- **A certificate with a positive semidefinite cross kernel implies the reduced form.** -/
theorem reducedAt_of_kcertificate (C : KCertificate n) : ReducedAt n := by
  intro A hA
  set d : Fin n → ℝ := fun i => (A i i).re with hd
  have hd0 : ∀ i, 0 ≤ d i := fun i => (diag_eq_re hA i).1
  set κ : Fin n → Fin n → ℝ := fun i j => (C.c 0 (d i) + C.c 0 (d j)) / 2 with hκ
  set b : Fin n → Fin n → ℕ → ℝ := fun i j m => C.κ m (d i) (d j) with hb
  have hpair : ∀ i j, ‖1 - A i j‖ ≤ Real.exp (-(harm (κ i j) (b i j) C.D (nz A i j))) := by
    intro i j
    have := disc_of_circle (Real.sqrt (d i * d j)) (κ i j) (b i j) C.D
      (C.circle (d i) (d j) (hd0 i) (hd0 j)) (nz A i j) (norm_nz_le hA i j)
    rwa [← eq_sqrt_mul_nz hA i j] at this
  have hprod : ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖
      ≤ Real.exp (-(∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun i _ => prod_nonneg fun j _ => norm_nonneg _) fun i _ => ?_
    rw [← sum_neg_distrib, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => hpair i j
  have hS : ∑ i, (((n : ℝ) - 1) * C.c 0 (d i) - ∑ m ∈ Icc 1 C.D, C.c m (d i))
      ≤ ∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j) := by
    have hsplit : ∀ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j)
        = ∑ j, harm (κ i j) (b i j) C.D (nz A i j) - harm (κ i i) (b i i) C.D (nz A i i) := by
      intro i; rw [sum_erase_eq_sub (mem_univ i)]
    simp only [hsplit, sum_sub_distrib]
    have hfull : ∑ i, ∑ j, harm (κ i j) (b i j) C.D (nz A i j)
        = (n : ℝ) * ∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re := by
      simp only [harm, sum_add_distrib]
      congr 1
      · simp only [hκ, add_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← sum_div, ← mul_sum]
        ring
      · rw [show (∑ m ∈ Icc 1 C.D, ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re)
            = ∑ i, ∑ m ∈ Icc 1 C.D, ∑ j, b i j m * ((nz A i j) ^ m).re from sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    have hdiag : ∑ i, harm (κ i i) (b i i) C.D (nz A i i)
        ≤ ∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, C.c m (d i) := by
      simp only [harm, sum_add_distrib]
      refine add_le_add (le_of_eq ?_) ?_
      · exact sum_congr rfl fun i _ => by simp [hκ]
      · rw [sum_comm]
        refine sum_le_sum fun m hm => sum_le_sum fun i _ => ?_
        have hm1 : 1 ≤ m := (mem_Icc.mp hm).1
        have hc := C.nonneg m hm1 (d i) (hd0 i)
        have hbii : b i i m = C.c m (d i) := C.diag m hm1 (d i) (hd0 i)
        rw [hbii]
        have : ((nz A i i) ^ m).re ≤ 1 :=
          (Complex.re_le_norm _).trans (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_nz_le hA i i))
        nlinarith
    have hschur : ∀ m ∈ Icc 1 C.D, 0 ≤ ∑ i, ∑ j, b i j m * ((nz A i j) ^ m).re := by
      intro m hm
      refine C.psd m hm d hd0 (fun i j => ((nz A i j) ^ m).re) ?_
      intro φ hφ
      have h := sum_sqrt_mul_nz_pow_nonneg hA (mem_Icc.mp hm).1 (fun i => φ i ^ 2) (fun i => sq_nonneg _)
      refine le_of_le_of_eq h ?_
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [← mul_pow, Real.sqrt_sq (mul_nonneg (hφ i) (hφ j))]
    have hschur' := sum_nonneg hschur
    rw [hfull]
    have e : ∑ i, (((n : ℝ) - 1) * C.c 0 (d i)) - ∑ i, ∑ m ∈ Icc 1 C.D, C.c m (d i)
        = (n : ℝ) * ∑ i, C.c 0 (d i) - (∑ i, C.c 0 (d i) + ∑ m ∈ Icc 1 C.D, ∑ i, C.c m (d i)) := by
      rw [← mul_sum, sum_comm]; ring
    rw [e]
    linarith
  have hT : -(∑ i, Real.log (∑ k ∈ range n, d i ^ k))
      ≤ ∑ i, (((n : ℝ) - 1) * C.c 0 (d i) - ∑ m ∈ Icc 1 C.D, C.c m (d i)) := by
    rw [← sum_neg_distrib]
    exact sum_le_sum fun i _ => C.total (d i) (hd0 i)
  have hFpos : ∀ i, 0 < ∑ k ∈ range n, d i ^ k := by
    intro i
    by_cases hn : n = 0
    · exact (Fin.elim0 (hn ▸ i))
    · have : (1 : ℝ) ≤ ∑ k ∈ range n, d i ^ k := by
        calc (1 : ℝ) = d i ^ 0 := by simp
          _ ≤ ∑ k ∈ range n, d i ^ k :=
            single_le_sum (f := fun k => d i ^ k) (fun k _ => pow_nonneg (hd0 i) k)
              (mem_range.mpr (Nat.pos_of_ne_zero hn))
      linarith
  calc ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖
      ≤ Real.exp (-(∑ i, ∑ j ∈ univ.erase i, harm (κ i j) (b i j) C.D (nz A i j))) := hprod
    _ ≤ Real.exp (∑ i, Real.log (∑ k ∈ range n, d i ^ k)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = ∏ i, ∑ k ∈ range n, d i ^ k := by
        rw [Real.exp_sum]; exact prod_congr rfl fun i _ => Real.exp_log (hFpos i)

end main

/-! ### The τ-certificate -/

open Real in
/-- The pair inequality for the symmetrised τ-kernel, all `p, q ≥ 0`. -/
theorem tauStar_symm {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - (Real.exp (-(p + q) / 2) : ℂ) * z‖ ≤
      Real.exp (-(harm ((Gam0 n p + Gam0 n q) / 2) (fun m => Ktau n m (min p q) (max p q)) (n - 2) z)) := by
  rcases le_total p q with h | h
  · simp only [min_eq_left h, max_eq_right h]
    exact tauStar hn hp h z hz
  · simp only [min_eq_right h, max_eq_left h]
    have := tauStar hn hq h z hz
    have e1 : -(p + q) / 2 = -(q + p) / 2 := by ring
    have e2 : (Gam0 n p + Gam0 n q) / 2 = (Gam0 n q + Gam0 n p) / 2 := by ring
    rw [e1, e2]; exact this

/-- The cross kernel in the diagonal variable `s = e^{∓p}`, `p = |log s|`. -/
noncomputable def tauCoefK (n m : ℕ) (s t : ℝ) : ℝ :=
  if s = 0 ∨ t = 0 then 0
  else Ktau n m (min |Real.log s| |Real.log t|) (max |Real.log s| |Real.log t|)

open Real in
theorem tauCoef_circle {n : ℕ} (hn : 2 ≤ n) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖1 - (Real.sqrt (s * t) : ℂ) * z‖ ≤
      Real.exp (-(harm ((coef n 0 s + coef n 0 t) / 2) (fun m => tauCoefK n m s t) (n - 2) z)) := by
  by_cases hzero : s = 0 ∨ t = 0
  · have hk : ∀ m, tauCoefK n m s t = 0 := fun m => by simp [tauCoefK, hzero]
    have hst : s * t = 0 := by rcases hzero with h | h <;> simp [h]
    simp only [harm, hk, zero_mul, sum_const_zero, add_zero, hst, Real.sqrt_zero, Complex.ofReal_zero,
      sub_zero, norm_one]
    have h1 := coef_zero_nonpos n s
    have h2 := coef_zero_nonpos n t
    exact Real.one_le_exp (by linarith)
  have hs' : s ≠ 0 := fun h => hzero (Or.inl h)
  have ht' : t ≠ 0 := fun h => hzero (Or.inr h)
  have hs0 : 0 < s := lt_of_le_of_ne hs (Ne.symm hs')
  have ht0 : 0 < t := lt_of_le_of_ne ht (Ne.symm ht')
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
  have hstar := tauStar_symm hn (abs_nonneg a) (abs_nonneg b) z hz
  have hharm : harm ((coef n 0 s + coef n 0 t) / 2) (fun m => tauCoefK n m s t) (n - 2) z
      = harm ((Gam0 n |a| + Gam0 n |b|) / 2) (fun m => Ktau n m (min |a| |b|) (max |a| |b|)) (n - 2) z - A := by
    unfold harm
    have e1 : ∑ m ∈ Finset.Icc 1 (n - 2), tauCoefK n m s t * (z ^ m).re
        = ∑ m ∈ Finset.Icc 1 (n - 2), Ktau n m (min |a| |b|) (max |a| |b|) * (z ^ m).re := by
      refine sum_congr rfl fun m _ => ?_
      simp [tauCoefK, hs', ht', ha, hb]
    rw [e1]
    simp only [coef, hs', ht', ↓reduceIte, ← ha, ← hb, hA]
    ring
  rw [hsqrt, hharm]
  calc ‖1 - (exp ((a + b) / 2) : ℂ) * z‖
      ≤ exp A * ‖1 - (exp (-(|a| + |b|) / 2) : ℂ) * z‖ := hstep
    _ ≤ exp A * Real.exp (-(harm ((Gam0 n |a| + Gam0 n |b|) / 2)
          (fun m => Ktau n m (min |a| |b|) (max |a| |b|)) (n - 2) z)) :=
        mul_le_mul_of_nonneg_left hstar (exp_pos _).le
    _ = _ := by rw [← exp_add]; congr 1; ring

theorem tauCoefK_psd {n : ℕ} (hn : 2 ≤ n) {m : ℕ} (hm : m ∈ Icc 1 (n - 2)) (s : Fin n → ℝ)
    (G : Fin n → Fin n → ℝ)
    (hG : ∀ φ : Fin n → ℝ, (∀ i, 0 ≤ φ i) → 0 ≤ ∑ i, ∑ j, φ i * φ j * G i j) :
    0 ≤ ∑ i, ∑ j, tauCoefK n m (s i) (s j) * G i j := by
  set p : Fin n → ℝ := fun i => |Real.log (s i)| with hp
  set G' : Fin n → Fin n → ℝ := fun i j => if s i = 0 ∨ s j = 0 then 0 else G i j with hG'
  have hcone : ∀ φ : Fin n → ℝ, (∀ i, 0 ≤ φ i) → 0 ≤ ∑ i, ∑ j, φ i * φ j * G' i j := by
    intro φ hφ
    have h := hG (fun i => if s i = 0 then 0 else φ i) (fun i => by split_ifs <;> simp [hφ i])
    refine le_of_le_of_eq h ?_
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hi : s i = 0
    · simp [hG', hi]
    · by_cases hj : s j = 0
      · simp [hG', hj]
      · simp [hG', hi, hj]
  have h := tauK_psd hn hm p (fun i => abs_nonneg _) G' hcone
  refine le_of_le_of_eq h ?_
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  by_cases hij : s i = 0 ∨ s j = 0
  · simp [tauCoefK, hG', hij]
  · simp [tauCoefK, hG', hij, hp]

/-- **The τ-certificate**: Fejér coefficients on the diagonal, the τ-kernel off the diagonal. -/
noncomputable def tauCertificate {n : ℕ} (hn : 2 ≤ n) : KCertificate n where
  D := n - 2
  c := coef n
  κ := tauCoefK n
  nonneg := fun _ hm s _ => coef_nonneg n hm s
  total := fun _ hs => coef_total (by omega) hs
  diag := by
    intro m hm s _
    have hm0 : m ≠ 0 := by omega
    by_cases h : s = 0
    · simp [tauCoefK, coef, h]
    · simp [tauCoefK, coef, h, hm0, Ktau_self]
  psd := fun _ hm s _ G hG => tauCoefK_psd hn hm s G hG
  circle := fun s t hs ht z hz => tauCoef_circle hn s t hs ht z hz

theorem reducedAt_all (n : ℕ) : ReducedAt n := by
  by_cases hn : 2 ≤ n
  · exact reducedAt_of_kcertificate (tauCertificate hn)
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact reducedAt_zero
    · exact reducedAt_one

/-- **The main theorem.** For every complex positive semidefinite `n × n` matrix `A`,
`∏_{i,j} |1 - a_ij| ≤ ∏_i |1 - a_ii ^ n|`. -/
theorem mainTheorem : Statement.MainTheorem :=
  mainTheorem_of_reduced reducedAt_all

end MatrixIneq

#print axioms MatrixIneq.mainTheorem
