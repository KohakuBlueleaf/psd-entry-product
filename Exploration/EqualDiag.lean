import MatrixIneq.Poisson
import Exploration.Star
import Exploration.CertificateOn

/-!
# Matrices with constant diagonal

`Star` at `p = q`, the main inequality for constant diagonal (`mainTheorem_const_diag`) and
`∏_{i ≠ j} |1 - a_ij| ≤ n ^ n` for unit diagonal.
This file is not used by the final proof (`MatrixIneq.mainTheorem`); it records an intermediate direction.
-/

open Real Finset MeasureTheory Set Filter Topology

namespace MatrixIneq

theorem starAt_diag {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp : 0 ≤ p) : StarAt n p p := by
  intro z hz
  have h := star_diag hn hp z hz
  have e1 : -(p + p) / 2 = -p := by ring
  have e2 : (Gam0 n p + Gam0 n p) / 2 = Gam0 n p := by ring
  have e3 : (fun m => Real.sqrt (Gam n m p * Gam n m p)) = fun m => Gam n m p := by
    funext m; exact Real.sqrt_mul_self (Gam_nonneg n m hp)
  rw [e1, e2, e3]; exact h

/-! ### Matrices with constant diagonal -/

/-- The Fejér certificate on a single diagonal value. -/
noncomputable def certificateOn_diag {n : ℕ} (hn : 2 ≤ n) (d : ℝ) (hd : 0 ≤ d) : CertificateOn n {d} where
  D := n - 2
  c := coef n
  nonneg := fun _ hm s _ => coef_nonneg n hm s
  total := fun s hs => by
    obtain rfl := Set.mem_singleton_iff.mp hs
    exact coef_total (by omega) hd
  circle := fun s hs t ht z hz => by
    obtain rfl := Set.mem_singleton_iff.mp hs
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact coef_circle t t (starAt_diag hn (abs_nonneg _)) hd hd z hz

open scoped ComplexOrder in
/-- **Reduced form for constant diagonal**, all `n`. -/
theorem reduced_const_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hconst : ∀ i j, A i i = A j j) :
    ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ ≤ ∏ i, ∑ k ∈ range n, (A i i).re ^ k := by
  by_cases hn : 2 ≤ n
  · let i0 : Fin n := ⟨0, by omega⟩
    exact reducedOn_of_certificate (certificateOn_diag hn (A i0 i0).re (diag_eq_re hA i0).1) A hA
      (fun i => by rw [hconst i i0]; exact Set.mem_singleton _)
  · have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl
    · exact reducedAt_zero A hA
    · exact reducedAt_one A hA

open scoped ComplexOrder in
/-- **The main inequality for positive semidefinite matrices with constant diagonal**, all `n`. -/
theorem mainTheorem_const_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hconst : ∀ i j, A i i = A j j) :
    ∏ i, ∏ j, ‖1 - A i j‖ ≤ ∏ i, ‖1 - A i i ^ n‖ := by
  have hL : ∏ i, ∏ j, ‖1 - A i j‖ = (∏ i, ‖1 - A i i‖) * ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun i _ => (mul_prod_erase univ (fun j => ‖1 - A i j‖) (mem_univ i)).symm
  have hR : ∏ i, ‖1 - A i i ^ n‖ = (∏ i, ‖1 - A i i‖) * ∏ i, ∑ k ∈ range n, (A i i).re ^ k := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    obtain ⟨h0, he⟩ := diag_eq_re hA i
    rw [he, norm_one_sub_pow _ h0, Complex.ofReal_re]
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left (reduced_const_diag A hA hconst) (prod_nonneg fun i _ => norm_nonneg _)

open scoped ComplexOrder in
/-- **Unit diagonal**: `∏_{i ≠ j} |1 - a_ij| ≤ n ^ n`. -/
theorem prod_offdiag_le_pow_of_unit_diag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (hunit : ∀ i, A i i = 1) :
    ∏ i, ∏ j ∈ univ.erase i, ‖1 - A i j‖ ≤ (n : ℝ) ^ n := by
  have h := reduced_const_diag A hA (fun i j => by rw [hunit i, hunit j])
  refine h.trans (le_of_eq ?_)
  simp [hunit]


end MatrixIneq
