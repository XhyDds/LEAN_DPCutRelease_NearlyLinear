import DPCut.SDPGeometry

/-! Matrix identities and Cauchy–Schwarz estimates immediately needed by Lemma 13. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace DPCut

lemma frobenius_nonneg {n : ℕ} (E : Mat n) : 0 ≤ frobenius E := by
  exact @norm_nonneg (Mat n)
    Matrix.frobeniusNormedAddCommGroup.toNormedAddGroup.toSeminormedAddGroup E

lemma frobenius_sq {n : ℕ} (E : Mat n) :
    frobenius E ^ 2 = ∑ i, ∑ j, E i j ^ 2 := by
  unfold frobenius
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

lemma frobenius_sq_trace {n : ℕ} (E : Mat n) :
    frobenius E ^ 2 = (E * Eᵀ).trace := by
  rw [frobenius_sq]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]

lemma posDef_transpose {n : ℕ} {X : Mat n} (hX : X.PosDef) : Xᵀ = X := by
  simpa using (show X.conjTranspose = X from hX.1)

lemma inv_sqrt_sq {n : ℕ} {X : Mat n} (hX : X.PosDef) :
    (CFC.sqrt X)⁻¹ * (CFC.sqrt X)⁻¹ = X⁻¹ := by
  rw [← Matrix.mul_inv_rev, CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]

lemma inverse_difference {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    X⁻¹ - Y⁻¹ = X⁻¹ * (Y - X) * Y⁻¹ := by
  letI := hX.isUnit.invertible
  letI := hY.isUnit.invertible
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

lemma relativeDifference_reconstruct {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    CFC.sqrt X * relativeDifference X Y * CFC.sqrt Y = Y - X := by
  letI := hX.posDef_sqrt.isUnit.invertible
  letI := hY.posDef_sqrt.isUnit.invertible
  simp only [relativeDifference, ← Matrix.mul_assoc,
    Matrix.mul_inv_of_invertible, Matrix.one_mul,
    Matrix.inv_mul_cancel_right_of_invertible]

lemma covarianceDistance_sq {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    covarianceDistance X Y ^ 2 = ((X⁻¹ - Y⁻¹) * (Y - X)).trace := by
  rw [covarianceDistance, frobenius_sq_trace, relativeDifference, Matrix.transpose_mul,
    Matrix.transpose_mul]
  have hL : ((CFC.sqrt X)⁻¹)ᵀ = (CFC.sqrt X)⁻¹ := posDef_transpose hX.posDef_sqrt.inv
  have hR : ((CFC.sqrt Y)⁻¹)ᵀ = (CFC.sqrt Y)⁻¹ := posDef_transpose hY.posDef_sqrt.inv
  have hD : (Y - X)ᵀ = Y - X := by
    rw [Matrix.transpose_sub, posDef_transpose hX, posDef_transpose hY]
  rw [hL, hR, hD, inverse_difference hX hY]
  calc
    _ = ((CFC.sqrt X)⁻¹ * (Y - X) *
        ((CFC.sqrt Y)⁻¹ * (CFC.sqrt Y)⁻¹) * (Y - X) * (CFC.sqrt X)⁻¹).trace := by
      congr 1; noncomm_ring
    _ = ((CFC.sqrt X)⁻¹ * (CFC.sqrt X)⁻¹ * (Y - X) * Y⁻¹ * (Y - X)).trace := by
      rw [inv_sqrt_sq hY, Matrix.trace_mul_comm]
      congr 1; noncomm_ring
    _ = _ := by rw [inv_sqrt_sq hX]

lemma covarianceDistance_eq_zero_iff {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) : covarianceDistance X Y = 0 ↔ X = Y := by
  letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
  constructor
  · intro h
    have hE : relativeDifference X Y = 0 :=
      norm_eq_zero.mp h
    have hd := relativeDifference_reconstruct hX hY
    rw [hE, Matrix.mul_zero, Matrix.zero_mul] at hd
    exact (sub_eq_zero.mp hd.symm).symm
  · rintro rfl
    simp [covarianceDistance, relativeDifference, frobenius]

lemma matrix_bilinear_sq_le {n : ℕ} (E : Mat n) (u v : Fin n → ℝ) :
    (u ⬝ᵥ (E *ᵥ v)) ^ 2 ≤
      (∑ i, u i ^ 2) * (∑ j, v j ^ 2) * frobenius E ^ 2 := by
  classical
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
    (fun p => u p.1 * v p.2) (fun p => E p.1 p.2)
  simp only [Fintype.sum_prod_type, mul_pow] at h
  rw [frobenius_sq]
  have hsum : (∑ i, ∑ j, (u i * v j) * E i j) = u ⬝ᵥ (E *ᵥ v) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  rw [hsum] at h
  simpa only [← Finset.mul_sum, ← Finset.sum_mul] using h

lemma sqrt_mulVec_sq {n : ℕ} {X : Mat n} (hX : X.PosDef) (b : Fin n → ℝ) :
    (∑ i, ((CFC.sqrt X) *ᵥ b) i ^ 2) = b ⬝ᵥ (X *ᵥ b) := by
  simp only [pow_two]
  change ((CFC.sqrt X) *ᵥ b) ⬝ᵥ ((CFC.sqrt X) *ᵥ b) = _
  rw [dotProduct_mulVec, Matrix.vecMul_mulVec, ← dotProduct_mulVec,
    posDef_transpose hX.posDef_sqrt, CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]

lemma fractionalQuery_difference_sq_le {n : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n) (e : Edge n) :
    (fractionalQuery Y e - fractionalQuery X e) ^ 2 ≤
      fractionalQuery X e * fractionalQuery Y e * covarianceDistance X Y ^ 2 := by
  have hpX := feasible_posDef hn hX
  have hpY := feasible_posDef hn hY
  have hb := matrix_bilinear_sq_le (relativeDifference X Y)
    ((CFC.sqrt X) *ᵥ edgeVector e) ((CFC.sqrt Y) *ᵥ edgeVector e)
  rw [sqrt_mulVec_sq hpX, sqrt_mulVec_sq hpY,
    edgeVector_quadratic hX, edgeVector_quadratic hY] at hb
  have he : ((CFC.sqrt X) *ᵥ edgeVector e) ⬝ᵥ
      (relativeDifference X Y *ᵥ ((CFC.sqrt Y) *ᵥ edgeVector e)) =
      4 * (fractionalQuery Y e - fractionalQuery X e) := by
    rw [dotProduct_mulVec, Matrix.vecMul_mulVec, ← dotProduct_mulVec,
      Matrix.mulVec_mulVec, posDef_transpose hpX.posDef_sqrt,
      relativeDifference_reconstruct hpX hpY, Matrix.sub_mulVec, dotProduct_sub,
      edgeVector_quadratic hX, edgeVector_quadratic hY]
    ring
  rw [he] at hb
  change _ ≤ _ * frobenius (relativeDifference X Y) ^ 2
  nlinarith

lemma fractionalQuery_difference_le {n : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n) (e : Edge n) :
    |fractionalQuery Y e - fractionalQuery X e| ≤
      Real.sqrt (fractionalQuery X e * fractionalQuery Y e) * covarianceDistance X Y := by
  have hp : 0 ≤ fractionalQuery X e * fractionalQuery Y e :=
    mul_nonneg (feasible_fractionalQuery_bounds hn hX e).1.le
      (feasible_fractionalQuery_bounds hn hY e).1.le
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (frobenius_nonneg (relativeDifference X Y)))).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hp]
  exact fractionalQuery_difference_sq_le hn hX hY e

end DPCut
