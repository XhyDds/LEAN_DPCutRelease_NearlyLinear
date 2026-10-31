import DPCut.GaussianDensity
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! The exact KL divergence of the implemented Gaussian batch law, derived
from its density and integrable quadratic log likelihood. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal MatrixOrder
namespace DPCut

lemma gaussianBatch_likelihood_density {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    (gaussianBatch Y k).withDensity (fun z => ENNReal.ofReal (Real.exp (batchLogRatio X Y z))) =
      gaussianBatch X k := by
  rw [gaussianBatch_withDensity hY, gaussianBatch_withDensity hX,
    ← withDensity_mul _ (by fun_prop) ((measurable_batchLogRatio X Y).exp.ennreal_ofReal)]
  congr 1
  funext z
  simp only [Pi.mul_apply, gaussianDensity, ← Real.exp_sum,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
    batchLogRatio, Finset.sum_sub_distrib]
  congr 2
  ring

lemma gaussianBatch_ac {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) : gaussianBatch X k ≪ gaussianBatch Y k := by
  rw [← gaussianBatch_likelihood_density hX hY]
  exact withDensity_absolutelyContinuous _ _

lemma gaussianBatch_llr {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    llr (gaussianBatch X k) (gaussianBatch Y k) =ᵐ[gaussianBatch X k] batchLogRatio X Y := by
  have hr := Measure.rnDeriv_withDensity (gaussianBatch Y k)
    ((measurable_batchLogRatio X Y).exp.ennreal_ofReal)
  rw [gaussianBatch_likelihood_density hX hY] at hr
  filter_upwards [(gaussianBatch_ac hX hY).ae_le hr] with z hz
  simp [llr, hz, ENNReal.toReal_ofReal (Real.exp_nonneg _)]

lemma integrable_diagonal_logRatio {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    Integrable (fun z => batchLogRatio X Y
      (diagonalBatch (k := k) X (relativePrecision_posDef hX hY).1.eigenvectorUnitary z))
      (gaussianProduct (Fin k × Fin n)) := by
  let hB := relativePrecision_posDef hX hY
  let a : Fin k × Fin n → ℝ := fun p => hB.1.eigenvalues p.2 - 1
  have hs : Integrable (fun z => ∑ p, a p * (z p ^ 2 - 1))
      (gaussianProduct (Fin k × Fin n)) :=
    integrable_finset_sum _ fun p _ =>
      (((allLp_standardGaussian_eval p).pow 2).integrable.sub (integrable_const 1)).const_mul _
  have h := ((integrable_const ((k : ℝ) *
    ∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i)))).add hs).div_const 2
  apply h.congr
  filter_upwards [] with z
  have he := batchLogRatio_diagonal hX hY z
  change _ = batchLogRatio X Y (diagonalBatch X hB.1.eigenvectorUnitary z)
  dsimp [a, hB] at *
  linarith

lemma integrable_batchLogRatio {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    Integrable (batchLogRatio X Y) (gaussianBatch X k) := by
  rw [← gaussianProduct_map_diagonalBatch X (relativePrecision_posDef hX hY).1.eigenvectorUnitary]
  apply (integrable_map_measure (measurable_batchLogRatio X Y).aestronglyMeasurable
    (measurable_diagonalBatch _ _).aemeasurable).mpr
  exact integrable_diagonal_logRatio hX hY

lemma gaussianBatch_integral_logRatio {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    (∫ z, batchLogRatio X Y z ∂gaussianBatch X k) =
      (k : ℝ) / 2 * ((Y⁻¹ * X).trace - n + Real.log Y.det - Real.log X.det) := by
  let hB := relativePrecision_posDef hX hY
  let a : Fin k × Fin n → ℝ := fun p => hB.1.eigenvalues p.2 - 1
  have hs (p : Fin k × Fin n) : Integrable (fun z => a p * (z p ^ 2 - 1))
      (gaussianProduct (Fin k × Fin n)) :=
    (((allLp_standardGaussian_eval p).pow 2).integrable.sub (integrable_const 1)).const_mul _
  have hi (p : Fin k × Fin n) :
      (∫ z, a p * (z p ^ 2 - 1) ∂gaussianProduct (Fin k × Fin n)) = 0 := by
    rw [integral_const_mul]
    have he := integral_map (μ := gaussianProduct (Fin k × Fin n))
      (measurable_pi_apply p).aemeasurable
      (show Measurable (fun x : ℝ => x ^ 2 - 1) by fun_prop).aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin k × Fin n => gaussianReal 0 1) p).map_eq] at he
    rw [← he, centered_gaussian_square_moments.1, mul_zero]
  have he : (fun z => batchLogRatio X Y (diagonalBatch X hB.1.eigenvectorUnitary z)) =
      (fun z => ((k : ℝ) * ∑ i, (hB.1.eigenvalues i - 1 - Real.log (hB.1.eigenvalues i)) +
        ∑ p : Fin k × Fin n, a p * (z p ^ 2 - 1)) / 2) := by
    funext z
    have hh := batchLogRatio_diagonal hX hY z
    dsimp [a, hB] at *
    linarith
  rw [← gaussianProduct_map_diagonalBatch X hB.1.eigenvectorUnitary,
    integral_map (measurable_diagonalBatch _ _).aemeasurable
      (measurable_batchLogRatio X Y).aestronglyMeasurable, he,
    integral_div, integral_add (integrable_const _) (integrable_finset_sum _ (fun p _ => hs p)),
    integral_finset_sum _ (fun p _ => hs p)]
  simp only [hi, Finset.sum_const_zero, integral_const, measureReal_univ_eq_one,
    smul_eq_mul, one_mul, add_zero]
  have ht : (∑ i, hB.1.eigenvalues i) = (Y⁻¹ * X).trace := by
    have htr := hB.1.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at htr
    rw [← htr, relativePrecision, Matrix.trace_mul_cycle,
      CFC.sqrt_mul_sqrt_self X hX.posSemidef.nonneg, Matrix.trace_mul_comm]
  have hl := relativePrecision_logdet_eigenvalues hX hY
  change Real.log Y.det - Real.log X.det = -∑ i, Real.log (hB.1.eigenvalues i) at hl
  simp only [Finset.sum_sub_distrib, ht, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [show (∑ i, Real.log (hB.1.eigenvalues i)) =
    Real.log X.det - Real.log Y.det by linarith]
  ring

theorem gaussianBatch_klDiv {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) :
    InformationTheory.klDiv (gaussianBatch X k) (gaussianBatch Y k) =
      ENNReal.ofReal ((k : ℝ) / 2 * ((Y⁻¹ * X).trace - n + Real.log Y.det - Real.log X.det)) := by
  have hi := (integrable_batchLogRatio (k := k) hX hY).congr (gaussianBatch_llr hX hY).symm
  rw [InformationTheory.klDiv_of_ac_of_integrable (gaussianBatch_ac hX hY) hi,
    integral_congr_ae (gaussianBatch_llr hX hY), gaussianBatch_integral_logRatio hX hY,
    measureReal_univ_eq_one, measureReal_univ_eq_one]
  congr 1
  ring

end DPCut
