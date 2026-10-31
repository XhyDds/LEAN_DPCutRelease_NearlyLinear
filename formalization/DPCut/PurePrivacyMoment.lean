import DPCut.KernelLikelihood
import Mathlib.Probability.Moments.SubGaussian

/-! Hoeffding bounds for the privacy loss of a pure-private kernel. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DPCut

variable {Y : Type*} [MeasurableSpace Y]

/-- Bounded privacy loss has mean at most half the squared privacy parameter.
The normalization of the inverse likelihood is essential here. -/
lemma privacy_loss_mean_le (μ : Measure Y) [IsProbabilityMeasure μ]
    {z : Y → ℝ} (hz : Measurable z) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ᵐ y ∂μ, z y ∈ Set.Icc (-ε) ε)
    (hinv : ∫ y, Real.exp (-z y) ∂μ = 1) :
    (∫ y, z y ∂μ) ≤ ε ^ 2 / 2 := by
  have hsg := hasSubgaussianMGF_of_mem_Icc hz.aemeasurable hb
  have hm := hsg.mgf_le (-1)
  have hc : (((‖ε - -ε‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = ε ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ ε - -ε)]
    ring
  rw [hc] at hm
  have heq : mgf (fun y => z y - ∫ x, z x ∂μ) μ (-1) =
      Real.exp (∫ x, z x ∂μ) := by
    unfold mgf
    simp_rw [show ∀ y, (-1 : ℝ) * (z y - ∫ x, z x ∂μ) =
      (∫ x, z x ∂μ) + -z y by intro y; ring, Real.exp_add]
    rw [integral_const_mul, hinv, mul_one]
  rw [heq] at hm
  exact Real.exp_le_exp.mp (by simpa using hm)

lemma privacy_loss_exp_moment (μ : Measure Y) [IsProbabilityMeasure μ]
    {z : Y → ℝ} (hz : Measurable z) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hb : ∀ᵐ y ∂μ, z y ∈ Set.Icc (-ε) ε)
    (hinv : ∫ y, Real.exp (-z y) ∂μ = 1) :
    ∫⁻ y, ENNReal.ofReal (Real.exp
      (t * z y - (t + t ^ 2) * ε ^ 2 / 2)) ∂μ ≤ 1 := by
  have hmean := privacy_loss_mean_le μ hz hε hb hinv
  have hsg := hasSubgaussianMGF_of_mem_Icc hz.aemeasurable hb
  have hc : (((‖ε - -ε‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = ε ^ 2 := by
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ ε - -ε)]
    ring
  have hm := hsg.mgf_le t
  rw [hc] at hm
  have hf : Integrable (fun y => Real.exp
      (t * z y - (t + t ^ 2) * ε ^ 2 / 2)) μ := by
    have hi := integrable_exp_mul_of_mem_Icc (t := t) hz.aemeasurable hb
    convert hi.const_mul (Real.exp (-((t + t ^ 2) * ε ^ 2 / 2))) using 1
    funext y
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hf
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le), ENNReal.ofReal_le_one]
  calc
    _ = Real.exp (t * (∫ y, z y ∂μ) - (t + t ^ 2) * ε ^ 2 / 2) *
        mgf (fun y => z y - ∫ x, z x ∂μ) μ t := by
      unfold mgf
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t * (∫ y, z y ∂μ) - (t + t ^ 2) * ε ^ 2 / 2) *
        Real.exp (ε ^ 2 * t ^ 2 / 2) := by gcongr
    _ ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]
      nlinarith only [mul_le_mul_of_nonneg_left hmean ht]

lemma kernel_privacy_exp_moment {α : Type*} [MeasurableSpace α]
    [StandardBorelSpace Y] (K H : Kernel α Y)
    [IsMarkovKernel K] [IsMarkovKernel H] (h : α) {ε t : ℝ}
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hp : Indistinguishable (K h) (H h) ε 0) :
    ∫⁻ y, ENNReal.ofReal (Real.exp
      (t * kernelLogRatio K H h y - (t + t ^ 2) * ε ^ 2 / 2)) ∂K h ≤ 1 :=
  privacy_loss_exp_moment (K h)
    ((measurable_kernelLogRatio K H).comp measurable_prodMk_left) hε ht
    (kernelLogRatio_bounds K H h hp)
    (integral_exp_neg_kernelLogRatio K H h hp.ac hp.symm.ac)

end DPCut
