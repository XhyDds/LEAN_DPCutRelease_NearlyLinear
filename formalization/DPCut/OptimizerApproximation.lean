import DPCut.Optimizer
import DPCut.GaussianComparisonMatrix
import DPCut.Utility

/-! Objective-gap control of the normalized covariance error. This verifies
the paper's unnumbered numerical bridge; it does not assume an approximate
optimizer algorithm or its running time. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace DPCut

lemma sqrt_log_gap_le {r : ℝ} (hr : 0 < r) :
    (Real.sqrt r - 1) ^ 2 ≤ r - 1 - Real.log r := by
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hr)
  rw [Real.log_sqrt hr.le] at hs
  nlinarith [Real.sq_sqrt hr.le]

lemma square_le_nine_log_gap {r : ℝ} (hr : 0 < r)
    (hg : r - 1 - Real.log r ≤ 1) :
    (r - 1) ^ 2 ≤ 9 * (r - 1 - Real.log r) := by
  have hs := sqrt_log_gap_le hr
  have hs0 := Real.sqrt_nonneg r
  have hsq := Real.sq_sqrt hr.le
  have hs2 : Real.sqrt r ≤ 2 := by nlinarith
  have hf : (r - 1) ^ 2 = (Real.sqrt r - 1) ^ 2 * (Real.sqrt r + 1) ^ 2 := by
    calc
      (r - 1) ^ 2 = (Real.sqrt r ^ 2 - 1) ^ 2 := by rw [hsq]
      _ = _ := by ring
  calc
    (r - 1) ^ 2 = (Real.sqrt r - 1) ^ 2 * (Real.sqrt r + 1) ^ 2 := hf
    _ ≤ (Real.sqrt r - 1) ^ 2 * 9 := by gcongr; nlinarith
    _ ≤ 9 * (r - 1 - Real.log r) := by linarith

lemma hermitian_frobenius_sub_one {n : ℕ} {B : Mat n} (hB : B.IsHermitian) :
    frobenius (B - 1) ^ 2 = ∑ i, (hB.eigenvalues i - 1) ^ 2 := by
  let U : Mat n := hB.eigenvectorUnitary
  let D : Mat n := diagonal hB.eigenvalues
  have hU : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using unitary.coe_star_mul_self hB.eigenvectorUnitary
  have hspec : B = U * D * Uᵀ := by
    simpa [U, D, Matrix.star_eq_conjTranspose] using hB.spectral_theorem
  have htr : (B * B).trace = ∑ i, hB.eigenvalues i ^ 2 := by
    conv_lhs => rw [hspec]
    have he : (U * D * Uᵀ) * (U * D * Uᵀ) = U * (D * D) * Uᵀ := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul]
    rw [he, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    simp [D, Matrix.diagonal_mul_diagonal, pow_two]
  have hBt : Bᵀ = B := by simpa using hB.eq
  rw [frobenius_sq_trace, Matrix.transpose_sub, hBt, Matrix.transpose_one]
  have he : (B - 1) * (B - 1) = B * B - B - B + 1 := by noncomm_ring
  rw [he, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, htr,
    hB.trace_eq_sum_eigenvalues]
  simp only [sub_sq, one_pow, mul_one, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Matrix.trace_one, RCLike.ofReal_real_eq_id, id_eq]
  ring

def normalizedCovariance {n : ℕ} (X Y : Mat n) : Mat n :=
  (CFC.sqrt X)⁻¹ * Y * (CFC.sqrt X)⁻¹

lemma normalizedCovariance_posDef {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) : (normalizedCovariance X Y).PosDef := by
  have hi : Function.Injective (fun v => (CFC.sqrt X)⁻¹ *ᵥ v) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hX.posDef_sqrt.inv.isUnit
  have h := hY.conjTranspose_mul_mul_same hi
  simpa only [normalizedCovariance, Matrix.conjTranspose_eq_transpose_of_trivial,
    posDef_transpose hX.posDef_sqrt.inv] using h

lemma normalizedCovariance_trace {n : ℕ} {X : Mat n} (hX : X.PosDef) (Y : Mat n) :
    (normalizedCovariance X Y).trace = (X⁻¹ * Y).trace := by
  rw [normalizedCovariance, Matrix.trace_mul_cycle, inv_sqrt_sq hX]

lemma normalizedCovariance_logdet {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    Real.log (normalizedCovariance X Y).det = Real.log Y.det - Real.log X.det := by
  rw [show normalizedCovariance X Y = (relativePrecision X Y)⁻¹ from
    (relativePrecision_inv hY).symm, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Real.log_inv,
    relativePrecision_logdet hX hY]
  ring

lemma normalizedCovariance_difference {n : ℕ} {X : Mat n} (hX : X.PosDef) (Y : Mat n) :
    (CFC.sqrt X)⁻¹ * (X - Y) * (CFC.sqrt X)⁻¹ = -(normalizedCovariance X Y - 1) := by
  letI := hX.posDef_sqrt.isUnit.invertible
  have he : (CFC.sqrt X)⁻¹ * X * (CFC.sqrt X)⁻¹ = 1 := by
    conv_lhs => arg 1; arg 2; rw [← CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]
    simp [← Matrix.mul_assoc]
  simp only [Matrix.mul_sub, Matrix.sub_mul, he, normalizedCovariance]
  abel

lemma optimizer_log_gap_bound {n : ℕ} (hn : 2 ≤ n) {lam : ℝ}
    (D : Weights n) {Y : Mat n} (hY : Y ∈ feasible n) :
    let hB := normalizedCovariance_posDef (feasible_posDef hn (optimizer_isOptimizer hn lam D).1)
      (feasible_posDef hn hY)
    lam * (∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i))) ≤
      optimum lam D - objective lam D Y := by
  dsimp
  let X := optimizer lam D
  have hX := optimizer_isOptimizer hn lam D
  have hpX := feasible_posDef hn hX.1
  have hpY := feasible_posDef hn hY
  let hB := normalizedCovariance_posDef hpX hpY
  have hf := matrixOptimizer_first_order hn
    ((isOptimizer_iff_matrixOptimizer lam D _).mp hX) hY
  rw [matrixPairing_sub_right, matrixPairing_objectiveMatrix D hY,
    matrixPairing_objectiveMatrix D hX.1, Matrix.mul_sub] at hf
  have hi : (optimizer lam D)⁻¹ * optimizer lam D = 1 := by
    letI := hpX.isUnit.invertible
    simp
  rw [hi, Matrix.trace_sub, Matrix.trace_one] at hf
  have hl : (∑ i, Real.log (hB.1.eigenvalues i)) = Real.log Y.det - Real.log X.det := by
    rw [← normalizedCovariance_logdet hpX hpY, hB.1.det_eq_prod_eigenvalues]
    exact (Real.log_prod _ _ (fun i _ => (hB.eigenvalues_pos i).ne')).symm
  have ht : (∑ i, hB.1.eigenvalues i) = ((optimizer lam D)⁻¹ * Y).trace := by
    have ht0 := hB.1.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at ht0
    rw [← ht0, normalizedCovariance_trace hpX]
  change lam * (∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i))) ≤ _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ht, hl,
    optimum_eq_objective_optimizer hn, objective, objective]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  dsimp [X] at *
  simp only [Fintype.card_fin] at hf
  linarith

theorem objective_gap : ObjectiveGapStatement := by
  intro n hn lam μ hlam hμ hμhalf D Y hY hgap
  let X := optimizer lam D
  have hpX := feasible_posDef hn (optimizer_isOptimizer hn lam D).1
  have hpY := feasible_posDef hn hY
  let B := normalizedCovariance X Y
  let hB : B.PosDef := normalizedCovariance_posDef hpX hpY
  let g : Fin n → ℝ := fun i => hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i)
  have hg0 (i : Fin n) : 0 ≤ g i :=
    sub_nonneg.mpr (Real.log_le_sub_one_of_pos (hB.eigenvalues_pos i))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by nlinarith [sq_nonneg ((n : ℝ) ^ 2 - 4)]
  have hn4pos : (0 : ℝ) < 2 * (n : ℝ) ^ 4 := by positivity
  have hs : (∑ i, g i) ≤ μ ^ 2 / (2 * (n : ℝ) ^ 4) := by
    have h := (optimizer_log_gap_bound hn D hY).trans hgap
    apply (mul_le_mul_iff_right₀ hlam).mp
    change lam * (∑ i, g i) ≤ _ at h
    simpa only [mul_div_assoc] using h
  have hs1 : (∑ i, g i) ≤ 1 := by
    refine hs.trans ((div_le_iff₀ hn4pos).mpr ?_)
    nlinarith
  have hgi (i : Fin n) : g i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hg0 j) (Finset.mem_univ i)).trans hs1
  have hsq : frobenius (B - 1) ^ 2 ≤ μ ^ 2 := by
    rw [hermitian_frobenius_sub_one hB.1]
    calc
      (∑ i, (hB.1.eigenvalues i - 1) ^ 2) ≤ ∑ i, 9 * g i :=
        Finset.sum_le_sum fun i _ => square_le_nine_log_gap (hB.eigenvalues_pos i) (hgi i)
      _ = 9 * ∑ i, g i := (Finset.mul_sum _ _ _).symm
      _ ≤ 9 * (μ ^ 2 / (2 * (n : ℝ) ^ 4)) := by gcongr
      _ ≤ μ ^ 2 := by
        rw [← mul_div_assoc, div_le_iff₀ hn4pos]
        nlinarith [sq_nonneg μ, mul_nonneg (sq_nonneg μ) (show 0 ≤ 2 * (n : ℝ) ^ 4 - 9 by linarith)]
  dsimp only
  rw [normalizedCovariance_difference hpX]
  have hfneg : frobenius (-(B - 1)) = frobenius (B - 1) := by
    letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
    exact norm_neg (B - 1)
  rw [show normalizedCovariance (optimizer lam D) Y = B from rfl, hfneg]
  exact (sq_le_sq₀ (frobenius_nonneg _) hμ.le).mp hsq

end DPCut
