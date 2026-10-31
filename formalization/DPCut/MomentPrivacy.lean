import DPCut.KernelLikelihood

/-! Turning the charged exponential moment into an eventwise privacy inequality. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {Y : Type*} [MeasurableSpace Y]

lemma withDensity_exp_neg {μ ν : Measure Y} {z : Y → ℝ} (hz : Measurable z)
    (hd : ν.withDensity (fun y => ENNReal.ofReal (Real.exp (z y))) = μ) :
    μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-z y))) = ν := by
  rw [← hd, ← withDensity_mul _ hz.exp.ennreal_ofReal hz.neg.exp.ennreal_ofReal]
  have heq : ((fun y => ENNReal.ofReal (Real.exp (z y))) *
      (fun y => ENNReal.ofReal (Real.exp (-z y)))) = (1 : Y → ℝ≥0∞) := by
    funext y
    simp [Pi.mul_apply, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  rw [heq, withDensity_one]

/-- The exponential-moment argument, with a deterministic charge bound holding almost surely. -/
theorem privacy_of_charged_moment {μ ν : Measure Y} {z C : Y → ℝ}
    (hz : Measurable z) (hC : Measurable C)
    (hd : ν.withDensity (fun y => ENNReal.ofReal (Real.exp (z y))) = μ)
    {a L ε δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hε : Real.log (1 / δ) ≤ a * (ε - 4 * L))
    (hbudget : ∀ᵐ y ∂μ, C y ≤ L)
    (hmoment : ∫⁻ y, ENNReal.ofReal (Real.exp (a * (z y - 4 * C y))) ∂μ ≤ 1)
    (s : Set Y) (hs : MeasurableSet s) :
    μ s ≤ ENNReal.ofReal (Real.exp ε) * ν s + ENNReal.ofReal δ := by
  let W : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (a * (z y - 4 * C y)))
  have hW : Measurable W := (measurable_const.mul (hz.sub (measurable_const.mul hC))).exp.ennreal_ofReal
  have hr : Measurable (fun y => ENNReal.ofReal (Real.exp (-z y)) * s.indicator 1 y) :=
    hz.neg.exp.ennreal_ofReal.mul (measurable_const.indicator hs)
  have hinverse : (∫⁻ y, ENNReal.ofReal (Real.exp (-z y)) * s.indicator 1 y ∂μ) = ν s := by
    calc
      _ = ∫⁻ y, s.indicator 1 y ∂μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-z y))) :=
        (lintegral_withDensity_eq_lintegral_mul _ hz.neg.exp.ennreal_ofReal
          (measurable_const.indicator hs)).symm
      _ = ν s := by rw [withDensity_exp_neg hz hd, lintegral_indicator_one hs]
  calc
    μ s = ∫⁻ y, s.indicator (fun _ => (1 : ℝ≥0∞)) y ∂μ := (lintegral_indicator_one hs).symm
    _ ≤ ∫⁻ y, (ENNReal.ofReal (Real.exp ε) *
        (ENNReal.ofReal (Real.exp (-z y)) * s.indicator 1 y) + ENNReal.ofReal δ * W y) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbudget] with y hy
      by_cases hys : y ∈ s
      · simp only [Set.indicator_of_mem hys, Pi.one_apply, mul_one]
        by_cases hyz : z y ≤ ε
        · apply le_trans _ (le_add_right le_rfl)
          rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
            ENNReal.one_le_ofReal]
          exact Real.one_le_exp (by linarith)
        · apply le_trans _ (le_add_left le_rfl)
          change 1 ≤ ENNReal.ofReal δ * ENNReal.ofReal (Real.exp (a * (z y - 4 * C y)))
          rw [← ENNReal.ofReal_mul hδ.le, ENNReal.one_le_ofReal]
          have hex : 1 / δ ≤ Real.exp (a * (z y - 4 * C y)) := by
            rw [← Real.exp_log (by positivity : 0 < 1 / δ)]
            apply Real.exp_le_exp.mpr
            calc
              Real.log (1 / δ) ≤ a * (ε - 4 * L) := hε
              _ ≤ a * (z y - 4 * C y) := by gcongr; linarith
          have hm := mul_le_mul_of_nonneg_left hex hδ.le
          rw [mul_one_div_cancel hδ.ne'] at hm
          exact hm
      · simp [Set.indicator_of_notMem hys]
    _ = ENNReal.ofReal (Real.exp ε) * ν s + ENNReal.ofReal δ * (∫⁻ y, W y ∂μ) := by
      rw [lintegral_add_left (measurable_const.mul hr), lintegral_const_mul _ hr,
        lintegral_const_mul _ hW, hinverse]
    _ ≤ _ := by
      have hm := mul_le_mul_left' hmoment (ENNReal.ofReal δ)
      simpa only [mul_one] using add_le_add_left hm (ENNReal.ofReal (Real.exp ε) * ν s)

end DPCut
