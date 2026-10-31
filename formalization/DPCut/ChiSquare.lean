import DPCut.Definitions
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! The chi-square concentration estimate used immediately by Lemma 10. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace DPCut

instance standardGaussian_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussian n) := by
  unfold standardGaussian
  infer_instance

/-- The scalar squared-Gaussian exponential moment, in the range where it is finite. -/
lemma integral_exp_mul_sq_gaussian (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul,
    mul_assoc, ← Real.exp_add]
  have he : ∀ x : ℝ, -x ^ 2 / 2 + t * x ^ 2 = -(1 / 2 - t) * x ^ 2 := by
    intro x; ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  have hpos : 0 < 1 - 2 * t := by linarith
  have hhalf : 0 < 1 / 2 - t := by linarith
  rw [Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by positivity : 0 ≤ (2 : ℝ))]
  have hs := Real.sqrt_pos.2 Real.pi_pos
  have hh := Real.sqrt_pos.2 hhalf
  have htwo : Real.sqrt 2 * Real.sqrt (1 / 2 - t) = Real.sqrt (1 - 2 * t) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  rw [← htwo]
  field_simp

lemma mgf_sum_sq_standardGaussian (k : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (fun z : Fin k → ℝ => ∑ i, z i ^ 2) (standardGaussian k) t =
      ((Real.sqrt (1 - 2 * t))⁻¹) ^ k := by
  simp only [mgf, standardGaussian, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin k) (x : ℝ) => Real.exp (t * x ^ 2))]
  simp [integral_exp_mul_sq_gaussian t ht]

lemma integrable_exp_sum_sq_standardGaussian (k : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun z : Fin k → ℝ => Real.exp (t * ∑ i, z i ^ 2))
      (standardGaussian k) := by
  apply by_contradiction
  intro h
  have hz := integral_undef h
  have hn : (∫ z : Fin k → ℝ, Real.exp (t * ∑ i, z i ^ 2)
      ∂standardGaussian k) ≠ 0 := by
    change mgf _ _ _ ≠ 0
    rw [mgf_sum_sq_standardGaussian k t ht]
    have : 0 < 1 - 2 * t := by linarith
    positivity
  exact hn hz

lemma mgf_sum_sq_standardGaussian_exp (k : ℕ) (t : ℝ) (ht : t < 1 / 2) :
    mgf (fun z : Fin k → ℝ => ∑ i, z i ^ 2) (standardGaussian k) t =
      Real.exp (-(k : ℝ) * Real.log (1 - 2 * t) / 2) := by
  rw [mgf_sum_sq_standardGaussian k t ht]
  have hp : 0 < 1 - 2 * t := by linarith
  have he : (Real.sqrt (1 - 2 * t))⁻¹ = Real.exp (-Real.log (1 - 2 * t) / 2) := by
    rw [neg_div, ← Real.log_sqrt hp.le, Real.exp_neg, Real.exp_log (Real.sqrt_pos.2 hp)]
  rw [he, ← Real.exp_nat_mul]
  congr 1; ring

private lemma log_two_le : Real.log 2 ≤ (7 / 8 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  have hb : Real.sqrt 2 ≤ (23 / 16 : ℝ) := by nlinarith
  linarith

/-- A concrete version of the paper's chi-square tail prerequisite: `c = 1/32`. -/
theorem chiSquare_tail (k : ℕ) (hk : 0 < k) :
    prob (standardGaussian k)
      {z | (∑ i, z i ^ 2) / k ∉ Set.Icc (1 / 2 : ℝ) 2} ≤
        2 * Real.exp (-(k : ℝ) / 32) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlo := measure_le_le_exp_mul_mgf (μ := standardGaussian k)
    (X := fun z : Fin k → ℝ => ∑ i, z i ^ 2) ((k : ℝ) / 2)
    (show (-1 / 4 : ℝ) ≤ 0 by norm_num)
    (integrable_exp_sum_sq_standardGaussian k (-1 / 4) (by norm_num))
  have hhi := measure_ge_le_exp_mul_mgf (μ := standardGaussian k)
    (X := fun z : Fin k → ℝ => ∑ i, z i ^ 2) (2 * (k : ℝ))
    (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    (integrable_exp_sum_sq_standardGaussian k (1 / 4) (by norm_num))
  rw [mgf_sum_sq_standardGaussian_exp k _ (by norm_num), ← Real.exp_add] at hlo hhi
  have hloglo : (1 / 3 : ℝ) ≤ Real.log (3 / 2) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
    norm_num at h ⊢; exact h
  have hloghi : -(7 / 8 : ℝ) ≤ Real.log (1 / 2) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    linarith [log_two_le]
  have hlo' : (standardGaussian k).real {z | (∑ i, z i ^ 2) ≤ (k : ℝ) / 2} ≤
      Real.exp (-(k : ℝ) / 32) := by
    refine hlo.trans (Real.exp_le_exp.2 ?_)
    norm_num at hloglo ⊢
    nlinarith
  have hhi' : (standardGaussian k).real {z | 2 * (k : ℝ) ≤ (∑ i, z i ^ 2)} ≤
      Real.exp (-(k : ℝ) / 32) := by
    refine hhi.trans (Real.exp_le_exp.2 ?_)
    norm_num at hloghi ⊢
    nlinarith
  have hs : {z : Fin k → ℝ | (∑ i, z i ^ 2) / k ∉ Set.Icc (1 / 2 : ℝ) 2} ⊆
      {z | (∑ i, z i ^ 2) ≤ (k : ℝ) / 2} ∪
      {z | 2 * (k : ℝ) ≤ (∑ i, z i ^ 2)} := by
    intro z hz
    simp only [Set.mem_setOf_eq, Set.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · apply Or.inl
      change (∑ i, z i ^ 2) ≤ (k : ℝ) / 2
      linarith [(div_lt_iff₀ hkR).1 hz]
    · apply Or.inr
      change 2 * (k : ℝ) ≤ (∑ i, z i ^ 2)
      exact ((lt_div_iff₀ hkR).1 hz).le
  exact (measureReal_mono hs).trans ((measureReal_union_le _ _).trans (by linarith))

end DPCut
