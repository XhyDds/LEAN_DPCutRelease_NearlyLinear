import DPCut.SDPCoordinates

/-! Quantitative bounds for the log-determinant objective used by the external
cutting-plane theorem. All dependence on objective magnitudes is explicit. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped RealInnerProductSpace BigOperators
namespace DPCut

lemma feasible_eigenvalue_lower {n : ℕ} (_hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (j : Fin n) : 1 / (n : ℝ) ≤ hX.1.eigenvalues j := by
  let v := hX.1.eigenvectorBasis j
  have hunit : (v : Fin n → ℝ) ⬝ᵥ v = 1 := by
    have := v.norm_sq_eq
    have hv : ‖v‖ = 1 := hX.1.eigenvectorBasis.orthonormal.1 j
    simpa [dotProduct, Real.norm_eq_abs, sq_abs, hv, pow_two] using this.symm
  have heig : (v : Fin n → ℝ) ⬝ᵥ (X *ᵥ v) = hX.1.eigenvalues j := by
    simpa [v] using (hX.1.eigenvalues_eq j).symm
  have hpos := hX.2.2.2 (v : Fin n → ℝ)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, star_trivial,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hunit, heig, mul_one] at hpos
  linarith

lemma feasible_logdet_bounds {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n) :
    -(n : ℝ) ^ 2 ≤ Real.log X.det ∧ Real.log X.det ≤ 0 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hp := feasible_posDef hn hX
  have hl (j : Fin n) : -(n : ℝ) ≤ Real.log (hX.1.eigenvalues j) := by
    have hm := Real.log_le_log (one_div_pos.mpr hn0) (feasible_eigenvalue_lower hn hX j)
    have hu := Real.log_le_sub_one_of_pos hn0
    simp only [one_div, Real.log_inv] at hm
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hl j)
  have hlog : Real.log X.det = ∑ j, Real.log (hX.1.eigenvalues j) := by
    rw [hX.1.det_eq_prod_eigenvalues]
    exact Real.log_prod _ _ (fun j _ => (hp.eigenvalues_pos j).ne')
  constructor
  · rw [hlog]
    simpa [pow_two] using hsum
  · have hh := logdet_tangent_upper (Matrix.PosDef.one : (1 : Mat n).PosDef) hp
    simpa [Matrix.trace, Matrix.diag, hX.2.1] using hh

lemma feasible_pairing_abs_le {n : ℕ} (hn : 2 ≤ n) (D : Weights n)
    {X : Mat n} (hX : X ∈ feasible n) : |pairing D (fractionalQuery X)| ≤ l1 D := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  have hq := feasible_fractionalQuery_bounds hn hX e
  rw [abs_mul, abs_of_nonneg hq.1.le]
  exact mul_le_of_le_one_right (abs_nonneg _) hq.2

lemma objective_range_bound {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam)
    {D : Weights n} (hD : l1 D ≤ B) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n) :
    objective lam D X - objective lam D Y ≤ 2 * B + lam * (n : ℝ) ^ 2 := by
  have hx := abs_le.mp ((feasible_pairing_abs_le hn D hX).trans hD)
  have hy := abs_le.mp ((feasible_pairing_abs_le hn D hY).trans hD)
  have hlx := feasible_logdet_bounds hn hX
  have hly := feasible_logdet_bounds hn hY
  have hu := mul_le_mul_of_nonneg_left hlx.2 hlam
  have hl := mul_le_mul_of_nonneg_left hly.1 hlam
  unfold objective
  nlinarith

lemma matrixPairing_smul_right {n : ℕ} (a : ℝ) (A X : Mat n) :
    matrixPairing A (a • X) = a * matrixPairing A X := by
  simp [matrixPairing, Finset.mul_sum, mul_left_comm]

lemma matrixPairing_add_right {n : ℕ} (A X Y : Mat n) :
    matrixPairing A (X + Y) = matrixPairing A X + matrixPairing A Y := by
  simp [matrixPairing, mul_add, Finset.sum_add_distrib]

/-- Concavity follows from the certified supergradient, including at the
boundary of the spectrahedron. -/
theorem objective_concaveOn {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam)
    (D : Weights n) : ConcaveOn ℝ (feasible n) (objective lam D) := by
  refine ⟨feasible_convex n, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := a • X + b • Y
  have hZ : Z ∈ feasible n := feasible_convex n hX hY ha hb hab
  let G := objectiveMatrix D + lam • Z⁻¹
  have hx := mul_le_mul_of_nonneg_left (objective_tangent_upper hn hlam D hZ hX) ha
  have hy := mul_le_mul_of_nonneg_left (objective_tangent_upper hn hlam D hZ hY) hb
  have hg : matrixPairing G Z = a * matrixPairing G X + b * matrixPairing G Y := by
    simp [Z, matrixPairing_add_right, matrixPairing_smul_right]
  change a * objective lam D X + b * objective lam D Y ≤ objective lam D Z
  change a * objective lam D X ≤ a * (objective lam D Z + matrixPairing G (X-Z)) at hx
  change b * objective lam D Y ≤ b * (objective lam D Z + matrixPairing G (Y-Z)) at hy
  rw [matrixPairing_sub_right] at hx hy
  have hcancel : a * (objective lam D Z + (matrixPairing G X - matrixPairing G Z)) +
      b * (objective lam D Z + (matrixPairing G Y - matrixPairing G Z)) = objective lam D Z := by
    calc
      _ = (a+b) * objective lam D Z +
          (a * matrixPairing G X + b * matrixPairing G Y) - (a+b) * matrixPairing G Z := by ring
      _ = _ := by rw [hab, ← hg]; ring
  linarith

end DPCut
