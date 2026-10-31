import DPCut.PrivacyTrimming

/-! Balancing the two clipped laws preserves their pure privacy parameter. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {Y A : Type*} [MeasurableSpace Y] [MeasurableSpace A]

def balanceCoefficient (a b ε : ℝ) : ℝ :=
  (b - b / Real.exp ε) / (a - b / Real.exp ε)

def shrinkMeasure (μ ν : Measure Y) (ε : ℝ) : Measure Y :=
  let t := balanceCoefficient (prob μ univ) (prob ν univ) ε
  ENNReal.ofReal t • μ + ENNReal.ofReal ((1 - t) / Real.exp ε) • ν

lemma balanceCoefficient_bounds {a b ε : ℝ} (hb : 0 < b) (hab : b ≤ a) (hε : 0 < ε) :
    0 ≤ balanceCoefficient a b ε ∧ balanceCoefficient a b ε ≤ 1 ∧
    balanceCoefficient a b ε * a + (1 - balanceCoefficient a b ε) / Real.exp ε * b = b := by
  have he : 1 < Real.exp ε := Real.one_lt_exp_iff.mpr hε
  have he0 := Real.exp_pos ε
  have hba : b / Real.exp ε < b := (div_lt_self hb he)
  have hd : 0 < a - b / Real.exp ε := by linarith
  refine ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith), ?_⟩
  dsimp [balanceCoefficient]
  have hd' : Real.exp ε * a - b ≠ 0 := by
    have := (div_lt_iff₀ he0).mp (show b / Real.exp ε < a by linarith)
    nlinarith
  field_simp [hd', he0.ne']; ring

lemma shrinkMeasure_prob (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (hε : 0 < ε) (hν : 0 < prob ν univ) (hμν : prob ν univ ≤ prob μ univ)
    (s : Set Y) :
    prob (shrinkMeasure μ ν ε) s =
      balanceCoefficient (prob μ univ) (prob ν univ) ε * prob μ s +
      (1 - balanceCoefficient (prob μ univ) (prob ν univ) ε) / Real.exp ε * prob ν s := by
  obtain ⟨ht, ht1, _⟩ := balanceCoefficient_bounds hν hμν hε
  change 0 ≤ balanceCoefficient (μ univ).toReal (ν univ).toReal ε at ht
  change balanceCoefficient (μ univ).toReal (ν univ).toReal ε ≤ 1 at ht1
  simp only [shrinkMeasure, prob, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ht,
    ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr ht1) (Real.exp_nonneg ε))]

/-- The larger clipped law is moved towards a scaled copy of the smaller one. -/
lemma shrinkMeasure_properties (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (hε : 0 < ε) (hν : 0 < prob ν univ) (hμν : prob ν univ ≤ prob μ univ)
    (hp : Indistinguishable μ ν ε 0) :
    prob (shrinkMeasure μ ν ε) univ = prob ν univ ∧
      shrinkMeasure μ ν ε ≤ μ ∧ Indistinguishable (shrinkMeasure μ ν ε) ν ε 0 := by
  let t := balanceCoefficient (prob μ univ) (prob ν univ) ε
  obtain ⟨ht, ht1, hmass⟩ := balanceCoefficient_bounds hν hμν hε
  have ht' : 0 ≤ (1 - t) / Real.exp ε := div_nonneg (by dsimp [t]; linarith) (Real.exp_nonneg _)
  have he := Real.exp_pos ε
  have he1 : 1 ≤ Real.exp ε := Real.one_le_exp hε.le
  have hf (s : Set Y) := shrinkMeasure_prob μ ν hε hν hμν s
  letI : IsFiniteMeasure (shrinkMeasure μ ν ε) := by
    refine ⟨?_⟩
    simp only [shrinkMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  have hevent (s : Set Y) (hs : MeasurableSet s) :
      prob μ s ≤ Real.exp ε * prob ν s ∧ prob ν s ≤ Real.exp ε * prob μ s := by
    have h1 := (privacy_event_iff_real μ ν s ε (le_refl 0)).mp (hp.1 s hs)
    have h2 := (privacy_event_iff_real ν μ s ε (le_refl 0)).mp (hp.2 s hs)
    simpa using And.intro h1 h2
  refine ⟨(hf univ).trans hmass, ?_, ?_⟩
  · apply Measure.le_iff.mpr
    intro s hs
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change prob (shrinkMeasure μ ν ε) s ≤ prob μ s
    rw [hf]
    have hb := mul_le_mul_of_nonneg_left (hevent s hs).2 ht'
    have hid : (1 - t) / Real.exp ε * (Real.exp ε * prob μ s) = (1 - t) * prob μ s := by
      field_simp
    dsimp only [t] at hb hid
    rw [hid] at hb
    nlinarith only [hb]
  · constructor <;> intro s hs
    · apply (privacy_event_iff_real _ _ s ε (le_refl 0)).mpr
      rw [hf]
      simp only [add_zero]
      have hb := mul_le_mul_of_nonneg_left (hevent s hs).1 ht
      have hc : (1 - t) / Real.exp ε * prob ν s ≤ (1 - t) * Real.exp ε * prob ν s := by
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        apply (div_le_iff₀ he).mpr
        nlinarith only [sq_nonneg (Real.exp ε - 1), he1,
          mul_nonneg (show 0 ≤ 1 - t by dsimp [t]; linarith) (show 0 ≤ Real.exp ε - 1 by linarith)]
      dsimp only [t] at hc
      nlinarith only [hb, hc]
    · apply (privacy_event_iff_real _ _ s ε (le_refl 0)).mpr
      rw [hf]
      simp only [add_zero]
      have hb := mul_le_mul_of_nonneg_left (hevent s hs).2 ht
      have hid : Real.exp ε * ((1 - t) / Real.exp ε * prob ν s) = (1 - t) * prob ν s := by
        field_simp
      dsimp only [t] at hid
      nlinarith only [hb, hid]

def balancedMeasure (μ ν : Measure Y) (ε : ℝ) : Measure Y :=
  if prob μ univ ≤ prob ν univ then μ else shrinkMeasure μ ν ε

instance shrinkMeasure_finite (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ε : ℝ) : IsFiniteMeasure (shrinkMeasure μ ν ε) := by
  dsimp [shrinkMeasure]
  letI := μ.smul_finite (c := ENNReal.ofReal
    (balanceCoefficient (prob μ univ) (prob ν univ) ε)) ENNReal.ofReal_ne_top
  letI := ν.smul_finite (c := ENNReal.ofReal
    ((1 - balanceCoefficient (prob μ univ) (prob ν univ) ε) / Real.exp ε)) ENNReal.ofReal_ne_top
  infer_instance

instance balancedMeasure_finite (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (ε : ℝ) : IsFiniteMeasure (balancedMeasure μ ν ε) := by
  unfold balancedMeasure
  split <;> infer_instance

lemma balancedMeasure_properties (μ ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {ε : ℝ} (hε : 0 ≤ ε) (hμ : 0 < prob μ univ) (hν : 0 < prob ν univ)
    (hp : Indistinguishable μ ν ε 0) :
    prob (balancedMeasure μ ν ε) univ = min (prob μ univ) (prob ν univ) ∧
    balancedMeasure μ ν ε ≤ μ ∧
    Indistinguishable (balancedMeasure μ ν ε) (balancedMeasure ν μ ε) ε 0 := by
  rcases eq_or_lt_of_le hε with hzero | hε
  · subst ε
    have heq := hp.zero_eq
    subst ν
    simpa [balancedMeasure] using hp
  by_cases hab : prob μ univ ≤ prob ν univ
  · rw [balancedMeasure, if_pos hab, min_eq_left hab]
    refine ⟨rfl, le_rfl, ?_⟩
    by_cases hba : prob ν univ ≤ prob μ univ
    · simpa [balancedMeasure, hba] using hp
    · simpa [balancedMeasure, hba] using (shrinkMeasure_properties ν μ hε hμ hab hp.symm).2.2.symm
  · have hba : prob ν univ ≤ prob μ univ := (lt_of_not_ge hab).le
    obtain ⟨hm, hl, hp'⟩ := shrinkMeasure_properties μ ν hε hν hba hp
    simpa only [balancedMeasure, if_neg hab, if_pos hba, min_eq_right hba] using ⟨hm, hl, hp'⟩

lemma measurable_shrinkMeasure {μ ν : A → Measure Y} (hμ : Measurable μ) (hν : Measurable ν)
    (ε : ℝ) : Measurable (fun a => shrinkMeasure (μ a) (ν a) ε) := by
  have hm : Measurable (fun a => prob (μ a) univ) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp hμ).ennreal_toReal
  have hn : Measurable (fun a => prob (ν a) univ) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp hν).ennreal_toReal
  have ht : Measurable (fun a => balanceCoefficient (prob (μ a) univ) (prob (ν a) univ) ε) :=
    (hn.sub (hn.div_const _)).div (hm.sub (hn.div_const _))
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [shrinkMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact (ht.ennreal_ofReal.mul ((Measure.measurable_coe hs).comp hμ)).add
    (((measurable_const.sub ht).div_const _).ennreal_ofReal.mul ((Measure.measurable_coe hs).comp hν))

lemma measurable_balancedMeasure {μ ν : A → Measure Y} (hμ : Measurable μ) (hν : Measurable ν)
    (ε : ℝ) : Measurable (fun a => balancedMeasure (μ a) (ν a) ε) := by
  have hm : Measurable (fun a => prob (μ a) univ) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp hμ).ennreal_toReal
  have hn : Measurable (fun a => prob (ν a) univ) :=
    ((Measure.measurable_coe MeasurableSet.univ).comp hν).ennreal_toReal
  exact Measurable.ite (measurableSet_le hm hn) hμ (measurable_shrinkMeasure hμ hν ε)

end DPCut
