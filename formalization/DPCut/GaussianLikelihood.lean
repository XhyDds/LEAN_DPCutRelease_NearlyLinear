import DPCut.GaussianComparisonMatrix
import DPCut.WitnessQuadratic

/-! Exact diagonal representation of the batch Gaussian log-likelihood ratio. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal MatrixOrder

namespace DPCut

def diagonalBatch {n k : ℕ} (X : Mat n) (U : Matrix.unitaryGroup (Fin n) ℝ)
    (z : Fin k × Fin n → ℝ) : Fin k → Fin n → ℝ :=
  fun j => (CFC.sqrt X) *ᵥ ((U : Mat n) *ᵥ fun i => z (j, i))

lemma measurable_diagonalBatch {n k : ℕ} (X : Mat n) (U : Matrix.unitaryGroup (Fin n) ℝ) :
    Measurable (diagonalBatch (k := k) X U) := by
  unfold diagonalBatch Matrix.mulVec dotProduct
  fun_prop

lemma gaussianProduct_map_diagonalBatch {n k : ℕ} (X : Mat n)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    (gaussianProduct (Fin k × Fin n)).map (diagonalBatch X U) = gaussianBatch X k := by
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun z => CFC.sqrt X *ᵥ ((U : Mat n) *ᵥ z)
  have hf : Measurable f := (measurable_mulVec _).comp (measurable_mulVec _)
  have hmap : (standardGaussian n).map f = gaussian X := by
    change (gaussianProduct (Fin n)).map ((fun z => CFC.sqrt X *ᵥ z) ∘
      (fun z => (U : Mat n) *ᵥ z)) = _
    rw [← Measure.map_map (measurable_mulVec _) (measurable_mulVec _), gaussianProduct_map_unitary]
    rfl
  have he : diagonalBatch (k := k) X U =
      (fun z : Fin k → Fin n → ℝ => fun j => f (z j)) ∘
        MeasurableEquiv.curry (Fin k) (Fin n) ℝ := rfl
  rw [he, ← Measure.map_map (by fun_prop) (MeasurableEquiv.curry (Fin k) (Fin n) ℝ).measurable,
    (gaussianProduct_curry n k).map_eq, Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  simp only [hmap, gaussianBatch]

lemma quadratic_congruence {n : ℕ} (A S : Mat n) (z : Fin n → ℝ) :
    quadratic A (S *ᵥ z) = quadratic (Sᵀ * A * S) z := by
  unfold quadratic
  rw [dotProduct_mulVec, Matrix.vecMul_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec]

lemma sqrt_precision_cancel {n : ℕ} {X : Mat n} (hX : X.PosDef) :
    CFC.sqrt X * X⁻¹ * CFC.sqrt X = (1 : Mat n) := by
  letI := hX.posDef_sqrt.isUnit.invertible
  rw [← inv_sqrt_sq hX]
  simp [← Matrix.mul_assoc]

lemma gaussianLogDensity_sub {n : ℕ} (X Y : Mat n) (z : Fin n → ℝ) :
    2 * (gaussianLogDensity X z - gaussianLogDensity Y z) =
      Real.log Y.det - Real.log X.det + quadratic (Y⁻¹ - X⁻¹) z := by
  simp only [gaussianLogDensity, quadratic, Matrix.sub_mulVec, dotProduct,
    Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

lemma gaussianLogDensity_diagonal {n : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) (z : Fin n → ℝ) :
    let hB := relativePrecision_posDef hX hY
    let U : Mat n := hB.1.eigenvectorUnitary
    2 * (gaussianLogDensity X (CFC.sqrt X *ᵥ (U *ᵥ z)) -
      gaussianLogDensity Y (CFC.sqrt X *ᵥ (U *ᵥ z))) =
      ∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i)) +
      ∑ i, (hB.1.eigenvalues i - 1) * (z i ^ 2 - 1) := by
  dsimp
  let hB := relativePrecision_posDef hX hY
  let U : Mat n := hB.1.eigenvectorUnitary
  have hUtU : Uᵀ * U = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using unitary.coe_star_mul_self hB.1.eigenvectorUnitary
  have hdiag : Uᵀ * (relativePrecision X Y) * U = diagonal hB.1.eigenvalues := by
    simpa [U, Matrix.star_eq_conjTranspose] using hB.1.star_mul_self_mul_eq_diagonal
  rw [gaussianLogDensity_sub, quadratic_congruence, posDef_transpose hX.posDef_sqrt,
    Matrix.mul_sub, Matrix.sub_mul, sqrt_precision_cancel hX]
  change Real.log Y.det - Real.log X.det + quadratic (relativePrecision X Y - 1) (U *ᵥ z) = _
  rw [quadratic_congruence, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hdiag, hUtU]
  have hq : quadratic (diagonal hB.1.eigenvalues - 1) z =
      ∑ i, (hB.1.eigenvalues i - 1) * z i ^ 2 := by
    simp only [quadratic, Matrix.sub_mulVec, Matrix.mulVec_diagonal, Matrix.one_mulVec,
      dotProduct, Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hq, relativePrecision_logdet_eigenvalues hX hY]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_one]
  ring

lemma batchLogRatio_diagonal {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) (z : Fin k × Fin n → ℝ) :
    let hB := relativePrecision_posDef hX hY
    2 * batchLogRatio X Y (diagonalBatch X hB.1.eigenvectorUnitary z) =
      k * (∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i))) +
      ∑ p : Fin k × Fin n, (hB.1.eigenvalues p.2 - 1) * (z p ^ 2 - 1) := by
  dsimp
  simp only [batchLogRatio, Finset.mul_sum, diagonalBatch]
  simp_rw [gaussianLogDensity_diagonal hX hY]
  simp [Fintype.sum_prod_type, mul_sub, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

lemma measurable_batchLogRatio {n k : ℕ} (X Y : Mat n) :
    Measurable (batchLogRatio (k := k) X Y) := by
  unfold batchLogRatio gaussianLogDensity Matrix.mulVec dotProduct
  fun_prop

/-- The Gaussian density formula appearing in Lemma 14, in exponential form. -/
def gaussianDensity {n : ℕ} (X : Mat n) (z : Fin n → ℝ) : ℝ :=
  Real.exp (gaussianLogDensity X z)

lemma gaussianDensity_eq {n : ℕ} {X : Mat n} (hX : X.PosDef) (z : Fin n → ℝ) :
    gaussianDensity X z = (Real.sqrt ((2 * Real.pi) ^ n * X.det))⁻¹ *
      Real.exp (-quadratic X⁻¹ z / 2) := by
  have hp : 0 < (2 * Real.pi) ^ n * X.det := mul_pos (pow_pos (by positivity) _) hX.det_pos
  have hl : Real.log (Real.sqrt ((2 * Real.pi) ^ n * X.det)) =
      (n : ℝ) / 2 * Real.log (2 * Real.pi) + Real.log X.det / 2 := by
    rw [Real.log_sqrt hp.le, Real.log_mul (by positivity) hX.det_pos.ne', Real.log_pow]
    ring
  change Real.exp (-(n : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log X.det / 2 -
    quadratic X⁻¹ z / 2) = _
  have he : -(n : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log X.det / 2 - quadratic X⁻¹ z / 2 =
      -Real.log (Real.sqrt ((2 * Real.pi) ^ n * X.det)) + (-quadratic X⁻¹ z / 2) := by
    rw [hl]
    ring
  rw [he, Real.exp_add, Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hp)]

lemma batch_density_bound_iff {n k : ℕ} (X Y : Mat n) (z : Fin k → Fin n → ℝ) (ε : ℝ) :
    (Real.exp (-ε) * (∏ j, gaussianDensity Y (z j)) ≤ (∏ j, gaussianDensity X (z j)) ∧
      (∏ j, gaussianDensity X (z j)) ≤ Real.exp ε * (∏ j, gaussianDensity Y (z j))) ↔
        |batchLogRatio X Y z| ≤ ε := by
  simp only [gaussianDensity, ← Real.exp_sum, ← Real.exp_add, Real.exp_le_exp,
    batchLogRatio, Finset.sum_sub_distrib, abs_le]
  constructor <;> rintro ⟨hl, hu⟩ <;> constructor <;> linarith

end DPCut
