import DPCut.PurePartKernel
import DPCut.Sequential

/-! Equal-weight subprobability parts compose without amplifying the discarded mass. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut

variable {Y : Type*} [MeasurableSpace Y]

lemma sequential_subpart [Inhabited Y] (P N : Sequential Y)
    [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (N t)]
    (k : ℕ) (c : ℝ≥0∞)
    (hp : ∀ t < k, ∀ h, c • N t h ≤ P t h) :
    c ^ k • sequentialLaw N k ≤ sequentialLaw P k := by
  induction k with
  | zero => simp [sequentialLaw]
  | succ k ih =>
    have hi := ih (fun t ht => hp t (by omega))
    have hm (K : Sequential Y) [∀ t, IsMarkovKernel (K t)] :
        Measurable (fun h => (K k h).map (fun y => h ++ [y])) :=
      measurable_map_kernel (K k).measurable (measurable_list_append_one default)
    apply Measure.le_iff.mpr
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul, sequentialLaw,
      Measure.bind_apply hs (hm N).aemeasurable, Measure.bind_apply hs (hm P).aemeasurable]
    calc
      _ = ∫⁻ h, c * ((N k h).map (fun y => h ++ [y])) s ∂c ^ k • sequentialLaw N k := by
        rw [lintegral_smul_measure, lintegral_const_mul c
          (show Measurable (fun h => ((N k h).map (fun y => h ++ [y])) s) from
            (Measure.measurable_coe hs).comp (hm N))]
        simp only [smul_eq_mul, pow_succ, mul_assoc]
      _ ≤ _ := lintegral_mono' hi (fun h => by
        have hf : Measurable (fun y : Y => h ++ [y]) :=
          (measurable_list_append_one default).comp measurable_prodMk_left
        simp only [Measure.map_apply hf hs]
        exact hp k (by omega) h ((fun y => h ++ [y]) ⁻¹' s))

lemma subpart_event_upper {μ ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 ≤ c) (hdom : ENNReal.ofReal c • ν ≤ μ)
    (s : Set Y) (hs : MeasurableSet s) :
    prob μ s ≤ c * prob ν s + (1 - c) := by
  have hl := ENNReal.toReal_mono (measure_ne_top _ _) (hdom sᶜ)
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hl
  have hm : prob μ s + prob μ sᶜ = 1 := by
    rw [prob, prob, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hs, measure_univ, ENNReal.toReal_one]
  have hn : prob ν s + prob ν sᶜ = 1 := by
    rw [prob, prob, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hs, measure_univ, ENNReal.toReal_one]
  change c * prob ν sᶜ ≤ prob μ sᶜ at hl
  nlinarith only [hl, hm, congrArg (fun x : ℝ => c * x) hn]

lemma Indistinguishable.subpart_transfer {μ ν P Q : Measure Y}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ε δ c : ℝ} (hp : Indistinguishable P Q ε δ)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hP : ENNReal.ofReal c • P ≤ μ) (hQ : ENNReal.ofReal c • Q ≤ ν) :
    Indistinguishable μ ν ε (δ + (1 - c)) := by
  have bound (μ ν P Q : Measure Y)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (hp : Indistinguishable P Q ε δ)
      (hP : ENNReal.ofReal c • P ≤ μ) (hQ : ENNReal.ofReal c • Q ≤ ν)
      (s : Set Y) (hs : MeasurableSet s) :
      μ s ≤ ENNReal.ofReal (Real.exp ε) * ν s + ENNReal.ofReal (δ + (1 - c)) := by
    apply (privacy_event_iff_real _ _ _ _ (by linarith : 0 ≤ δ + (1 - c))).mpr
    have hu := subpart_event_upper hc hP s hs
    have hv := ENNReal.toReal_mono (measure_ne_top _ _) (hQ s)
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hv
    change c * prob Q s ≤ prob ν s at hv
    have hh := (privacy_event_iff_real P Q s ε hδ).mp (hp.1 s hs)
    have h1 := mul_le_mul_of_nonneg_left hh hc
    have h2 := mul_le_mul_of_nonneg_left hv (Real.exp_nonneg ε)
    have h3 := mul_le_mul_of_nonneg_right hc1 hδ
    nlinarith only [hu, h1, h2, h3]
  exact ⟨bound μ ν P Q hp hP hQ, bound ν μ Q P hp.symm hQ hP⟩

end DPCut
