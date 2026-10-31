import DPCut.GaussianLikelihood
import DPCut.DensityTools
import DPCut.OptimizerMeasurable

/-! The actual covariance Gaussian law has the density used in Lemmas 14 and 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace DPCut

lemma standardGaussian_withDensity (n : ℕ) :
    standardGaussian n = volume.withDensity
      (fun z : Fin n → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))) := by
  unfold standardGaussian
  have h : gaussianReal (0 : ℝ) 1 =
      volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) :=
    gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : ℝ≥0) ≠ 0)
  simp_rw [h]
  exact pi_withDensity_ofReal (fun _ => volume) (fun _ => gaussianPDFReal 0 1)
    (fun _ => integrable_gaussianPDFReal 0 1) (fun _ => gaussianPDFReal_nonneg 0 1)

lemma standardGaussian_density_exp {n : ℕ} (z : Fin n → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (z i)) =
      Real.exp (-(n : ℝ) / 2 * Real.log (2 * Real.pi) - (∑ i, z i ^ 2) / 2) := by
  have he (x : ℝ) : gaussianPDFReal 0 1 x =
      Real.exp (-Real.log (2 * Real.pi) / 2 - x ^ 2 / 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show -Real.log (2 * Real.pi) / 2 - x ^ 2 / 2 =
        -Real.log (Real.sqrt (2 * Real.pi)) + (-x ^ 2 / 2) by
      rw [Real.log_sqrt (by positivity)]; ring,
      Real.exp_add, Real.exp_neg, Real.exp_log (by positivity)]
  simp_rw [he, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
  ring

def posDefMulVecEquiv {n : ℕ} {X : Mat n} (hX : X.PosDef) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun := fun z => X *ᵥ z
  invFun := fun z => X⁻¹ *ᵥ z
  left_inv := by
    intro z
    letI := hX.isUnit.invertible
    simp [Matrix.mulVec_mulVec]
  right_inv := by
    intro z
    letI := hX.isUnit.invertible
    simp [Matrix.mulVec_mulVec]
  measurable_toFun := measurable_mulVec _
  measurable_invFun := measurable_mulVec _

lemma gaussianDensity_change_variables {n : ℕ} {X : Mat n} (hX : X.PosDef)
    (z : Fin n → ℝ) :
    |(CFC.sqrt X).det⁻¹| *
      (∏ i, gaussianPDFReal 0 1 (((CFC.sqrt X)⁻¹ *ᵥ z) i)) = gaussianDensity X z := by
  have hd : 0 < (CFC.sqrt X).det := hX.posDef_sqrt.det_pos
  have hlog : 2 * Real.log (CFC.sqrt X).det = Real.log X.det := by
    have hs : (CFC.sqrt X).det * (CFC.sqrt X).det = X.det := by
      rw [← Matrix.det_mul, CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg]
    have ht := congrArg Real.log hs
    rw [Real.log_mul hd.ne' hd.ne'] at ht
    linarith
  have hq : (∑ i, (((CFC.sqrt X)⁻¹ *ᵥ z) i) ^ 2) = quadratic X⁻¹ z := by
    have h := quadratic_congruence (1 : Mat n) (CFC.sqrt X)⁻¹ z
    rw [posDef_transpose hX.posDef_sqrt.inv, Matrix.mul_one, inv_sqrt_sq hX] at h
    simpa [quadratic, dotProduct, pow_two] using h
  rw [abs_of_pos (inv_pos.mpr hd), standardGaussian_density_exp, hq,
    show (CFC.sqrt X).det⁻¹ = Real.exp (-Real.log (CFC.sqrt X).det) by
      rw [Real.exp_neg, Real.exp_log hd], ← Real.exp_add]
  apply congrArg Real.exp
  change _ = -(n : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log X.det / 2 -
    quadratic X⁻¹ z / 2
  linarith

@[fun_prop] lemma measurable_gaussianDensity {n : ℕ} (X : Mat n) :
    Measurable (gaussianDensity X) := by
  unfold gaussianDensity gaussianLogDensity Matrix.mulVec dotProduct
  fun_prop

theorem gaussian_withDensity {n : ℕ} {X : Mat n} (hX : X.PosDef) :
    gaussian X = volume.withDensity (fun z => ENNReal.ofReal (gaussianDensity X z)) := by
  let e := posDefMulVecEquiv hX.posDef_sqrt
  have hm : Measurable (fun z : Fin n → ℝ =>
      ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (z i))) := by fun_prop
  have hv : (volume : Measure (Fin n → ℝ)).map e =
      ENNReal.ofReal |(CFC.sqrt X).det⁻¹| • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi hX.posDef_sqrt.det_pos.ne'
  change (standardGaussian n).map e = _
  rw [standardGaussian_withDensity, map_withDensity_equiv _ e hm, hv,
    withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change ENNReal.ofReal |(CFC.sqrt X).det⁻¹| *
    ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (((CFC.sqrt X)⁻¹ *ᵥ z) i)) = _
  rw [← ENNReal.ofReal_mul (abs_nonneg _), gaussianDensity_change_variables hX]

lemma integrable_gaussianDensity {n : ℕ} {X : Mat n} (hX : X.PosDef) :
    Integrable (gaussianDensity X) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gaussianDensity X).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).mp
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← gaussian_withDensity hX, measure_univ]
  exact ENNReal.one_ne_top

theorem gaussianBatch_withDensity {n k : ℕ} {X : Mat n} (hX : X.PosDef) :
    gaussianBatch X k = volume.withDensity
      (fun z : Fin k → Fin n → ℝ => ENNReal.ofReal (∏ j, gaussianDensity X (z j))) := by
  unfold gaussianBatch
  simp_rw [gaussian_withDensity hX]
  exact pi_withDensity_ofReal (fun _ => volume) (fun _ => gaussianDensity X)
    (fun _ => integrable_gaussianDensity hX) (fun _ _ => Real.exp_nonneg _)

lemma measurable_matrix_inv (n : ℕ) : Measurable (fun X : Mat n => X⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  change Measurable (fun X : Mat n => fun i j => X.det⁻¹ * X.adjugate i j)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact continuous_id.matrix_det.measurable.inv.mul
    ((continuous_id.matrix_adjugate).matrix_elem i j).measurable

lemma measurable_gaussianLogDensity_pair (n : ℕ) :
    Measurable (fun p : Mat n × (Fin n → ℝ) => gaussianLogDensity p.1 p.2) := by
  have hi : Measurable (fun p : Mat n × (Fin n → ℝ) => p.1⁻¹) :=
    (measurable_matrix_inv n).comp measurable_fst
  have he (i j : Fin n) : Measurable (fun p : Mat n × (Fin n → ℝ) => p.1⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hi)
  have hv (i : Fin n) : Measurable (fun p : Mat n × (Fin n → ℝ) => p.2 i) := by fun_prop
  unfold gaussianLogDensity Matrix.mulVec dotProduct
  exact (measurable_const.sub (continuous_fst.matrix_det.measurable.log.div_const 2)).sub
    ((Finset.measurable_sum _ fun i _ => (hv i).mul
      (Finset.measurable_sum _ fun j _ => (he i j).mul (hv j))).div_const 2)

lemma measurable_gaussian_optimizer {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam) :
    Measurable (fun D : Weights n => gaussian (optimizer lam D)) := by
  have hd : Measurable (fun p : Weights n × (Fin n → ℝ) =>
      ENNReal.ofReal (gaussianDensity (optimizer lam p.1) p.2)) :=
    (((measurable_gaussianLogDensity_pair n).comp
      (((measurable_optimizer hn hlam).comp measurable_fst).prodMk measurable_snd)).exp).ennreal_ofReal
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [gaussian_withDensity (feasible_posDef hn (optimizer_isOptimizer hn lam _).1),
    withDensity_apply _ hs]
  exact Measurable.lintegral_prod_right
    (show Measurable (Function.uncurry (fun D z =>
      ENNReal.ofReal (gaussianDensity (optimizer lam D) z))) from hd)

end DPCut
