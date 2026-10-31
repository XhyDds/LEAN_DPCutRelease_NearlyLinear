import DPCut.BalancedPrivacy

/-! Every approximately private kernel pair contains equally weighted pure-private parts. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut

variable {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]

def normalizedMeasure (μ : Measure Y) : Measure Y :=
  ENNReal.ofReal (1 / prob μ univ) • μ

lemma normalizedMeasure_probability (μ : Measure Y) [IsFiniteMeasure μ]
    (hμ : 0 < prob μ univ) : IsProbabilityMeasure (normalizedMeasure μ) := by
  constructor
  change ENNReal.ofReal (1 / prob μ univ) * μ univ = 1
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ univ),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / prob μ univ)]
  change ENNReal.ofReal (1 / prob μ univ * prob μ univ) = 1
  rw [one_div_mul_cancel hμ.ne', ENNReal.ofReal_one]

lemma measurable_normalizedMeasure {μ : A → Measure Y} (hm : Measurable μ) :
    Measurable (fun a => normalizedMeasure (μ a)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  exact (measurable_const.div (((Measure.measurable_coe MeasurableSet.univ).comp hm).ennreal_toReal)).ennreal_ofReal.mul
    ((Measure.measurable_coe hs).comp hm)

lemma Indistinguishable.smul_pure {μ ν : Measure Y} {ε : ℝ}
    (hp : Indistinguishable μ ν ε 0) (c : ℝ≥0∞) :
    Indistinguishable (c • μ) (c • ν) ε 0 := by
  constructor <;> intro s hs
  · simpa [Measure.smul_apply, mul_left_comm, mul_assoc] using mul_le_mul_left' (hp.1 s hs) c
  · simpa [Measure.smul_apply, mul_left_comm, mul_assoc] using mul_le_mul_left' (hp.2 s hs) c

lemma normalizedMeasure_private {μ ν : Measure Y} {ε : ℝ}
    (hm : prob μ univ = prob ν univ) (hp : Indistinguishable μ ν ε 0) :
    Indistinguishable (normalizedMeasure μ) (normalizedMeasure ν) ε 0 := by
  unfold normalizedMeasure
  rw [hm]
  exact hp.smul_pure _

lemma normalizedMeasure_subpart {μ ν : Measure Y} [IsFiniteMeasure μ] {δ : ℝ}
    (hμ : 0 < prob μ univ) (hm : 1 - δ ≤ prob μ univ) (hl : μ ≤ ν) :
    ENNReal.ofReal (1 - δ) • normalizedMeasure μ ≤ ν := by
  apply le_trans _ hl
  apply Measure.le_iff.mpr
  intro s hs
  change ENNReal.ofReal (1 - δ) * (ENNReal.ofReal (1 / prob μ univ) * μ s) ≤ μ s
  have hc : ENNReal.ofReal (1 - δ) * ENNReal.ofReal (1 / prob μ univ) ≤ 1 := by
    by_cases hd : 0 ≤ 1 - δ
    · rw [← ENNReal.ofReal_mul hd, ENNReal.ofReal_le_one]
      simpa only [mul_one_div] using (div_le_one hμ).mpr hm
    · simp [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hd)]
  simpa only [mul_assoc, one_mul] using mul_le_mul_right' hc (μ s)

variable [StandardBorelSpace Y]

def purePartKernel (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (ε : ℝ) : Kernel A Y :=
  ⟨fun h => normalizedMeasure (balancedMeasure (privacyTrim K H ε h) (privacyTrim H K ε h) ε),
    measurable_normalizedMeasure (measurable_balancedMeasure (privacyTrim K H ε).measurable
      (privacyTrim H K ε).measurable ε)⟩

lemma privacyTrim_mass_real (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    (h : A) {ε δ : ℝ} (hδ : 0 ≤ δ) (hp : Indistinguishable (K h) (H h) ε δ) :
    1 - δ ≤ prob (privacyTrim K H ε h) univ := by
  have hh := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)
    (privacyTrim_mass K H h hp)
  rw [ENNReal.toReal_one, ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hδ] at hh
  exact sub_le_iff_le_add.mpr hh

lemma purePartKernel_properties (K H : Kernel A Y) [IsMarkovKernel K] [IsMarkovKernel H]
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hp : ∀ h, Indistinguishable (K h) (H h) ε δ) :
    IsMarkovKernel (purePartKernel K H ε) ∧ IsMarkovKernel (purePartKernel H K ε) ∧
    ∀ h, Indistinguishable (purePartKernel K H ε h) (purePartKernel H K ε h) ε 0 ∧
      ENNReal.ofReal (1 - δ) • purePartKernel K H ε h ≤ K h ∧
      ENNReal.ofReal (1 - δ) • purePartKernel H K ε h ≤ H h := by
  have props (P Q : Kernel A Y) [IsMarkovKernel P] [IsMarkovKernel Q]
      (hpq : ∀ h, Indistinguishable (P h) (Q h) ε δ) (h : A) :
      IsProbabilityMeasure (purePartKernel P Q ε h) ∧
      ENNReal.ofReal (1 - δ) • purePartKernel P Q ε h ≤ P h ∧
      Indistinguishable (purePartKernel P Q ε h) (purePartKernel Q P ε h) ε 0 := by
    have hm := privacyTrim_mass_real P Q h hδ (hpq h)
    have hn := privacyTrim_mass_real Q P h hδ (hpq h).symm
    have hm0 : 0 < prob (privacyTrim P Q ε h) univ := by linarith
    have hn0 : 0 < prob (privacyTrim Q P ε h) univ := by linarith
    obtain ⟨hbm, hbl, hbp⟩ := balancedMeasure_properties
      (privacyTrim P Q ε h) (privacyTrim Q P ε h) hε hm0 hn0 (privacyTrim_private P Q hε h)
    obtain ⟨hbn, _, _⟩ := balancedMeasure_properties
      (privacyTrim Q P ε h) (privacyTrim P Q ε h) hε hn0 hm0 (privacyTrim_private Q P hε h)
    have hb0 : 0 < prob (balancedMeasure (privacyTrim P Q ε h) (privacyTrim Q P ε h) ε) univ := by
      rw [hbm]
      exact lt_min hm0 hn0
    refine ⟨normalizedMeasure_probability _ hb0, normalizedMeasure_subpart hb0 ?_
      (hbl.trans (privacyTrim_le P Q ε h)), normalizedMeasure_private ?_ hbp⟩
    · rw [hbm]
      exact le_min hm hn
    · rw [hbm, hbn, min_comm]
  exact ⟨⟨fun h => (props K H hp h).1⟩,
    ⟨fun h => (props H K (fun h => (hp h).symm) h).1⟩,
    fun h => ⟨(props K H hp h).2.2, (props K H hp h).2.1,
      (props H K (fun h => (hp h).symm) h).2.1⟩⟩

end DPCut
