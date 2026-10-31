import DPCut.TotalVariation
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! An internal KL-to-total-variation bound. The deliberately non-optimal
constant two suffices for numerical-error budgeting. The proof uses scalar
logarithm inequalities and Jensen's inequality on each measurable event. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace DPCut

lemma sqrt_gap_le_klFun {r : ℝ} (hr : 0 ≤ r) :
    (Real.sqrt r - 1) ^ 2 ≤ klFun r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · norm_num [klFun]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hs := Real.sq_sqrt hr.le
  have hl := Real.one_sub_inv_le_log_of_pos hs0
  rw [Real.log_sqrt hr.le] at hl
  have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * r by positivity)
  have he : r * (Real.sqrt r)⁻¹ = Real.sqrt r := by
    conv_lhs => arg 1; rw [← hs]
    field_simp
  dsimp [klFun]
  nlinarith [he]

lemma probability_square_le_klFun {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (p - q) ^ 2 ≤ 4 * (q * klFun (p / q)) := by
  let t := Real.sqrt (p / q)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht : t ^ 2 = p / q := Real.sq_sqrt (div_nonneg hp hq.le)
  have htp : q * t ^ 2 = p := by rw [ht]; field_simp
  have hnonneg : 0 ≤ q * (t - 1) ^ 2 := mul_nonneg hq.le (sq_nonneg _)
  have htbound : q * (t + 1) ^ 2 ≤ 4 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left htbound hnonneg
  have he : (p - q) ^ 2 = (q * (t - 1) ^ 2) * (q * (t + 1) ^ 2) := by
    calc
      (p - q) ^ 2 = (q * t ^ 2 - q) ^ 2 := by rw [htp]
      _ = _ := by ring
  have hs := sqrt_gap_le_klFun (div_nonneg hp hq.le)
  have hsq := mul_le_mul_of_nonneg_left hs hq.le
  change q * (t - 1) ^ 2 ≤ q * klFun (p / q) at hsq
  rw [he]
  nlinarith

lemma event_klFun_le_klDiv {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hac : μ ≪ ν) (hi : Integrable (llr μ ν) μ)
    (s : Set α) (hs0 : ν s ≠ 0) :
    ν.real s * klFun (μ.real s / ν.real s) ≤ (klDiv μ ν).toReal := by
  let f : α → ℝ := fun x => (μ.rnDeriv ν x).toReal
  have hfi : Integrable f ν := Measure.integrable_toReal_rnDeriv
  have hgi : Integrable (fun x => klFun (f x)) ν := (integrable_klFun_rnDeriv_iff hac).mpr hi
  have hj := convexOn_klFun.map_set_average_le continuous_klFun.continuousOn
    isClosed_Ici hs0 (measure_ne_top ν s)
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg (a := μ.rnDeriv ν x)))
    hfi.integrableOn hgi.integrableOn
  have hq : 0 < ν.real s := ENNReal.toReal_pos hs0 (measure_ne_top ν s)
  rw [setAverage_eq, setAverage_eq, Measure.setIntegral_toReal_rnDeriv hac] at hj
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hj
  have hm := (le_div_iff₀ hq).mp hj
  calc
    ν.real s * klFun (μ.real s / ν.real s) ≤ ∫ x in s, klFun (f x) ∂ν := by
      simpa only [mul_comm] using hm
    _ ≤ ∫ x, klFun (f x) ∂ν :=
      setIntegral_le_integral hgi (Filter.Eventually.of_forall fun x =>
        klFun_nonneg ENNReal.toReal_nonneg)
    _ = (klDiv μ ν).toReal := (toReal_klDiv_eq_integral_klFun hac).symm

/-- A fully proved (non-sharp) Pinsker-type bound, including absolute
continuity and integrability consequences of finite KL divergence. -/
theorem tvClose_of_klDiv_bound {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (hδ : 0 ≤ δ) (hkl : klDiv μ ν ≤ ENNReal.ofReal δ) :
    TVClose μ ν (2 * Real.sqrt δ) := by
  have hfin : klDiv μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  obtain ⟨hac, hi⟩ := klDiv_ne_top_iff.mp hfin
  have hk : (klDiv μ ν).toReal ≤ δ := by
    simpa only [ENNReal.toReal_ofReal hδ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hkl
  intro s _hs
  by_cases hs0 : ν s = 0
  · have hm0 := hac hs0
    simp [prob, hs0, hm0, Real.sqrt_nonneg]
  · have hq : 0 < ν.real s := ENNReal.toReal_pos hs0 (measure_ne_top ν s)
    have hs := probability_square_le_klFun (p := μ.real s) (q := ν.real s)
      measureReal_nonneg (measureReal_le_one) hq measureReal_le_one
    have he := (event_klFun_le_klDiv hac hi s hs0).trans hk
    change |μ.real s - ν.real s| ≤ _
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt hδ]
    nlinarith

end DPCut
