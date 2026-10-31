import DPCut.RelativeMatrix
import DPCut.GaussianQuadratic

/-! Relative precision eigenvalues and the deterministic estimates for Lemma 14. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace DPCut

/-- Precision of the second covariance after whitening samples from the first. -/
def relativePrecision {n : ℕ} (X Y : Mat n) : Mat n := CFC.sqrt X * Y⁻¹ * CFC.sqrt X

lemma relativePrecision_posDef {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    (relativePrecision X Y).PosDef := by
  have hi : Function.Injective (fun v => (CFC.sqrt X) *ᵥ v) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hX.posDef_sqrt.isUnit
  have h := hY.inv.conjTranspose_mul_mul_same hi
  simpa only [relativePrecision, Matrix.conjTranspose_eq_transpose_of_trivial,
    posDef_transpose hX.posDef_sqrt] using h

lemma relativePrecision_inv {n : ℕ} {X Y : Mat n} (hY : Y.PosDef) :
    (relativePrecision X Y)⁻¹ = (CFC.sqrt X)⁻¹ * Y * (CFC.sqrt X)⁻¹ := by
  letI := hY.isUnit.invertible
  simp only [relativePrecision, Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, Matrix.mul_assoc]

lemma relativePrecision_logdet {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    Real.log (relativePrecision X Y).det = Real.log X.det - Real.log Y.det := by
  have hs : (CFC.sqrt X).det * (CFC.sqrt X).det = X.det := by
    rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]
  have he : (relativePrecision X Y).det = X.det / Y.det := by
    simp only [relativePrecision, Matrix.det_mul, Matrix.det_nonsing_inv]
    rw [mul_right_comm, hs, div_eq_mul_inv]
    simp
  rw [he, Real.log_div hX.det_pos.ne' hY.det_pos.ne']

lemma covarianceDistance_sq_precision {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    covarianceDistance X Y ^ 2 =
      (relativePrecision X Y).trace + (relativePrecision X Y)⁻¹.trace - 2 * n := by
  letI := hX.isUnit.invertible
  letI := hY.isUnit.invertible
  rw [covarianceDistance_sq hX hY]
  have he : (X⁻¹ - Y⁻¹) * (Y - X) = X⁻¹ * Y + Y⁻¹ * X - 2 • (1 : Mat n) := by
    simp only [two_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.inv_mul_of_invertible]
    abel
  rw [he, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul]
  have hb : (relativePrecision X Y).trace = (Y⁻¹ * X).trace := by
    rw [relativePrecision, Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]
    exact Matrix.trace_mul_comm _ _
  have hc : (relativePrecision X Y)⁻¹.trace = (X⁻¹ * Y).trace := by
    rw [relativePrecision_inv hY, Matrix.trace_mul_cycle, inv_sqrt_sq hX]
  rw [hb, hc]
  simp
  ring

lemma posDef_trace_inverse {n : ℕ} {B : Mat n} (hB : B.PosDef) :
    B⁻¹.trace = ∑ i, (hB.1.eigenvalues i)⁻¹ := by
  let U : Mat n := hB.1.eigenvectorUnitary
  have hUtU : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using unitary.coe_star_mul_self hB.1.eigenvectorUnitary
  have hUUt : U * Uᵀ = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using unitary.coe_mul_star_self hB.1.eigenvectorUnitary
  have he : B = U * diagonal hB.1.eigenvalues * Uᵀ := by
    simpa [U, Matrix.star_eq_conjTranspose] using hB.1.spectral_theorem
  have hi : B⁻¹ = U * diagonal (fun i => (hB.1.eigenvalues i)⁻¹) * Uᵀ := by
    apply Matrix.inv_eq_left_inv
    conv_lhs => arg 2; rw [he]
    calc
      _ = U * (diagonal (fun i => (hB.1.eigenvalues i)⁻¹) * diagonal hB.1.eigenvalues) * Uᵀ := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul]
      _ = U * 1 * Uᵀ := by
        congr 2
        rw [Matrix.diagonal_mul_diagonal]
        ext i j
        simp [inv_mul_cancel₀ (hB.eigenvalues_pos _).ne']
      _ = 1 := by simpa using hUUt
  rw [hi, Matrix.trace_mul_cycle, hUtU, Matrix.one_mul, Matrix.trace_diagonal]

lemma covarianceDistance_sq_eigenvalues {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    let hB := relativePrecision_posDef hX hY
    covarianceDistance X Y ^ 2 =
      ∑ i, (hB.1.eigenvalues i - 1) ^ 2 / hB.1.eigenvalues i := by
  dsimp
  let hB := relativePrecision_posDef hX hY
  rw [covarianceDistance_sq_precision hX hY, hB.1.trace_eq_sum_eigenvalues, posDef_trace_inverse hB]
  have he (r : ℝ) (hr : 0 < r) : (r - 1) ^ 2 / r = r + r⁻¹ - 2 := by
    field_simp
    ring
  simp_rw [he _ (hB.eigenvalues_pos _)]
  simp [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

lemma relativePrecision_logdet_eigenvalues {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    let hB := relativePrecision_posDef hX hY
    Real.log Y.det - Real.log X.det = -∑ i, Real.log (hB.1.eigenvalues i) := by
  dsimp
  have hl := relativePrecision_logdet hX hY
  have hB := relativePrecision_posDef hX hY
  have he : Real.log (relativePrecision X Y).det = ∑ i, Real.log (hB.1.eigenvalues i) := by
    rw [hB.1.det_eq_prod_eigenvalues]
    simpa using Real.log_prod Finset.univ hB.1.eigenvalues (fun i _ => (hB.eigenvalues_pos i).ne')
  linarith

lemma relativePrecision_spectral_bounds {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) (hd : covarianceDistance X Y < 1 / 2) :
    let hB := relativePrecision_posDef hX hY
    let r := hB.1.eigenvalues
    (0 ≤ ∑ i, (r i - 1 - Real.log (r i))) ∧
    (∑ i, (r i - 1 - Real.log (r i))) ≤ covarianceDistance X Y ^ 2 ∧
    (∑ i, (r i - 1) ^ 2) ≤ 2 * covarianceDistance X Y ^ 2 ∧
    ∀ i, |r i - 1| ≤ 2 * covarianceDistance X Y := by
  dsimp
  let hB := relativePrecision_posDef hX hY
  let r := hB.1.eigenvalues
  let e : Fin n → ℝ := fun i => (r i - 1) ^ 2 / r i
  have hr (i : Fin n) : 0 < r i := hB.eigenvalues_pos i
  have he (i : Fin n) : 0 ≤ e i := div_nonneg (sq_nonneg _) (hr i).le
  have hsum : ∑ i, e i = covarianceDistance X Y ^ 2 := (covarianceDistance_sq_eigenvalues hX hY).symm
  have hd0 : 0 ≤ covarianceDistance X Y := frobenius_nonneg _
  have hd2 : covarianceDistance X Y ^ 2 < 1 / 4 := by nlinarith
  have hei (i : Fin n) : e i ≤ covarianceDistance X Y ^ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => he j) (Finset.mem_univ i)
  have heq (i : Fin n) : e i * r i = (r i - 1) ^ 2 := div_mul_cancel₀ _ (hr i).ne'
  have hr2 (i : Fin n) : r i ≤ 2 := by
    have hbound := mul_le_mul_of_nonneg_right (hei i) (hr i).le
    rw [heq] at hbound
    have hbound' := mul_lt_mul_of_pos_right hd2 (hr i)
    by_contra h
    push_neg at h
    have hp : 0 ≤ (r i - 2) * (r i - 1 / 4) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hsqi (i : Fin n) : (r i - 1) ^ 2 ≤ 2 * e i := by
    rw [← heq]
    nlinarith [mul_nonneg (he i) (sub_nonneg.mpr (hr2 i))]
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), ?_, ?_, ?_⟩
  · exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos (hr i))
  · rw [← hsum]
    apply Finset.sum_le_sum
    intro i _
    have hl := Real.one_sub_inv_le_log_of_pos (hr i)
    have he' : e i = r i + (r i)⁻¹ - 2 := by
      change (r i - 1) ^ 2 / r i = _
      field_simp [(hr i).ne']
      ring
    change r i - 1 - Real.log (r i) ≤ e i
    rw [he']
    linarith
  · change (∑ i, (r i - 1) ^ 2) ≤ _
    calc
      _ ≤ ∑ i, 2 * e i := Finset.sum_le_sum fun i _ => hsqi i
      _ = _ := by rw [← Finset.mul_sum, hsum]
  · intro i
    change |r i - 1| ≤ _
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * covarianceDistance X Y)).mp
    rw [sq_abs]
    nlinarith [hsqi i, hei i, sq_nonneg (covarianceDistance X Y)]

end DPCut
