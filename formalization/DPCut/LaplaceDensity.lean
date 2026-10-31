import DPCut.Definitions
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Normalization and pointwise likelihood bounds for the noisy score in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace DPCut

@[fun_prop] lemma continuous_laplaceDensity (b : ℝ) : Continuous (laplaceDensity b) := by
  unfold laplaceDensity
  fun_prop

lemma laplaceDensity_pos {b : ℝ} (hb : 0 < b) (x : ℝ) : 0 < laplaceDensity b x := by
  unfold laplaceDensity
  positivity

lemma laplace_exp_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-|x| / b)) := by
  have hi : IntegrableOn (fun x : ℝ => Real.exp (-|x| / b)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic (inv_pos.mpr hb) 0).congr_fun
    · intro x hx
      dsimp
      rw [abs_of_nonpos (mem_Iic.mp hx)]
      congr 1
      ring
    · exact measurableSet_Iic
  have ho : IntegrableOn (fun x : ℝ => Real.exp (-|x| / b)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos (inv_pos.mpr hb)) 0).congr_fun
    · intro x hx
      dsimp
      rw [abs_of_pos (mem_Ioi.mp hx)]
      congr 1
      ring
    · exact measurableSet_Ioi
  have hu := hi.union ho
  simpa only [Iic_union_Ioi, integrableOn_univ] using hu

lemma integral_laplaceDensity {b : ℝ} (hb : 0 < b) :
    ∫ x, laplaceDensity b x = 1 := by
  have hi : (∫ x : ℝ in Iic 0, Real.exp (-|x| / b)) = b := by
    calc
      _ = ∫ x : ℝ in Iic 0, Real.exp (b⁻¹ * x) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro x hx
        dsimp
        rw [abs_of_nonpos (mem_Iic.mp hx)]
        congr 1
        ring
      _ = b := by rw [integral_exp_mul_Iic (inv_pos.mpr hb)]; simp
  have ho : (∫ x : ℝ in Ioi 0, Real.exp (-|x| / b)) = b := by
    calc
      _ = ∫ x : ℝ in Ioi 0, Real.exp (-(b⁻¹) * x) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp
        rw [abs_of_pos (mem_Ioi.mp hx)]
        congr 1
        ring
      _ = b := by rw [integral_exp_mul_Ioi (neg_neg_of_pos (inv_pos.mpr hb))]; simp
  have he : (∫ x : ℝ, Real.exp (-|x| / b)) = 2 * b := by
    rw [← integral_add_compl measurableSet_Iic (laplace_exp_integrable hb), compl_Iic, hi, ho]
    ring
  simp only [laplaceDensity, integral_const_mul, he]
  exact inv_mul_cancel₀ (by positivity)

theorem laplace_isProbabilityMeasure {b : ℝ} (hb : 0 < b) :
    IsProbabilityMeasure (laplace b) := by
  have hint : Integrable (laplaceDensity b) :=
    (laplace_exp_integrable hb).const_mul (2 * b)⁻¹
  constructor
  rw [laplace, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (laplaceDensity_pos hb x).le),
    integral_laplaceDensity hb, ENNReal.ofReal_one]

/-- The translated Laplace densities obey the exact sensitivity bound. -/
lemma laplaceDensity_shift_le {b : ℝ} (hb : 0 < b) (a c y : ℝ) :
    laplaceDensity b (y - a) ≤
      Real.exp (|a - c| / b) * laplaceDensity b (y - c) := by
  have h : -|y - a| / b ≤ |a - c| / b + -|y - c| / b := by
    have ht := abs_sub_le (y : ℝ) a c
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hb).mpr
    linarith
  have he := Real.exp_le_exp.mpr h
  rw [Real.exp_add] at he
  dsimp [laplaceDensity]
  nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ (2 * b)⁻¹ by positivity)]

end DPCut
