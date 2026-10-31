import DPCut.Definitions
import Mathlib.MeasureTheory.Integral.Pi

/-! Density identities used for the Gaussian batches and noisy scores in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DPCut

lemma map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map ((show Measurable (fun y => f (e.symm y)) from
      hf.comp e.symm.measurable).indicator hs) e.measurable,
    ← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [hx]

lemma pi_withDensity_ofReal {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] (f : ι → α → ℝ)
    (hf : ∀ i, Integrable (f i) (μ i)) (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (f i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hf).integrableOn
      (Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hn i (x i)),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (hf i).integrableOn
      (Filter.Eventually.of_forall (hn i))]

end DPCut
