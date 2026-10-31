import DPCut.Utility
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Finite normalized KL: support, finiteness, and the exact weighted-log formula. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory InformationTheory Set
open scoped BigOperators ENNReal
namespace DPCut
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

instance discreteMeasure_finite (p : ι → ℝ) : IsFiniteMeasure (discreteMeasure p) := by
  letI (i : ι) : IsFiniteMeasure (ENNReal.ofReal (p i) • Measure.dirac i) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  unfold discreteMeasure
  infer_instance

@[simp] lemma discreteMeasure_singleton (p : ι → ℝ) (i : ι) :
    discreteMeasure p {i} = ENNReal.ofReal (p i) := by
  classical
  simp [discreteMeasure, Measure.finset_sum_apply, Measure.smul_apply, Set.indicator_apply]

omit [MeasurableSingletonClass ι] in
lemma discreteMeasure_univ (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    discreteMeasure p univ = ENNReal.ofReal (∑ i, p i) := by
  classical
  simp [discreteMeasure, Measure.finset_sum_apply, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i)]

omit [MeasurableSingletonClass ι] in
lemma discreteMeasure_probability {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    IsProbabilityMeasure (discreteMeasure p) :=
  ⟨by rw [discreteMeasure_univ p hp, hs, ENNReal.ofReal_one]⟩

lemma discreteMeasure_ac {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hs : ∀ i, 0 < p i → 0 < q i) : discreteMeasure p ≪ discreteMeasure q := by
  have he : (discreteMeasure q).withDensity (fun i => ENNReal.ofReal (p i / q i)) =
      discreteMeasure p := by
    apply Measure.ext_of_singleton
    intro i
    rw [withDensity_apply _ (measurableSet_singleton i), lintegral_singleton,
      discreteMeasure_singleton, discreteMeasure_singleton, ← ENNReal.ofReal_mul (div_nonneg (hp i) (hq i))]
    by_cases hi : p i = 0
    · simp [hi]
    · rw [div_mul_cancel₀ _ (hs i (lt_of_le_of_ne (hp i) (Ne.symm hi))).ne']
  rw [← he]
  exact withDensity_absolutelyContinuous _ _

theorem finite_kl_formula {p q : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1) (hs : ∀ i, 0 < p i → 0 < q i) :
    klDiv (discreteMeasure p) (discreteMeasure q) ≠ ∞ ∧
      (klDiv (discreteMeasure p) (discreteMeasure q)).toReal = ∑ i, p i * Real.log (p i / q i) := by
  have hac := discreteMeasure_ac hp hq hs
  letI := discreteMeasure_probability hp hp1
  letI := discreteMeasure_probability hq hq1
  refine ⟨klDiv_ne_top_iff.mpr ⟨hac, Integrable.of_finite⟩, ?_⟩
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype _ Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro i _
  simp only [measureReal_def, discreteMeasure_singleton, ENNReal.toReal_ofReal (hp i), smul_eq_mul]
  by_cases hi : p i = 0
  · simp [hi]
  · have hqi := hs i (lt_of_le_of_ne (hp i) (Ne.symm hi))
    have hr := Measure.setIntegral_toReal_rnDeriv hac ({i} : Set ι)
    rw [integral_singleton] at hr
    simp only [measureReal_def, discreteMeasure_singleton,
      ENNReal.toReal_ofReal (hp i), ENNReal.toReal_ofReal (hq i), smul_eq_mul] at hr
    have he : ((discreteMeasure p).rnDeriv (discreteMeasure q) i).toReal = p i / q i := by
      apply (eq_div_iff hqi.ne').mpr
      simpa [mul_comm] using hr
    simp [llr, he]

theorem normalizedKL_finite_formula {n : ℕ} {w h : Weights n} {M H : ℝ}
    (hw : Nonnegative w) (hh : Nonnegative h) (hM : 0 < M) (hH : 0 < H)
    (hmw : mass w = M) (hmh : mass h = H) (hs : ∀ e, 0 < w e → 0 < h e) :
    normalizedKL w h M H ≠ ∞ ∧
      potential w h M H = ∑ e, w e * Real.log ((w e / M) / (h e / H)) := by
  have hf := finite_kl_formula (p := fun e => w e / M) (q := fun e => h e / H)
    (fun e => div_nonneg (hw e) hM.le) (fun e => div_nonneg (hh e) hH.le)
    (by rw [← Finset.sum_div]; change mass w / M = 1; rw [hmw]; exact div_self hM.ne')
    (by rw [← Finset.sum_div]; change mass h / H = 1; rw [hmh]; exact div_self hH.ne')
    (fun e he => div_pos (hs e ((div_pos_iff_of_pos_right hM).mp he)) hH)
  refine ⟨hf.1, ?_⟩
  rw [potential, normalizedKL, hf.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  field_simp

lemma potential_nonneg {n : ℕ} (w h : Weights n) {M H : ℝ} (hM : 0 ≤ M) :
    0 ≤ potential w h M H := mul_nonneg hM ENNReal.toReal_nonneg

end DPCut
