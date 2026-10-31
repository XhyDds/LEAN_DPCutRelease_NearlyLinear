import DPCut.TotalVariation
import Mathlib.Probability.ConditionalProbability

/-! Conditioning a common high-probability event doubles its pure likelihood bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DPCut
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma Indistinguishable.map {μ ν : Measure α} {ε δ : ℝ}
    (h : Indistinguishable μ ν ε δ) {f : α → β} (hf : Measurable f) :
    Indistinguishable (μ.map f) (ν.map f) ε δ := by
  constructor <;> intro s hs
  · simpa only [Measure.map_apply hf hs] using h.1 (f ⁻¹' s) (hf hs)
  · simpa only [Measure.map_apply hf hs] using h.2 (f ⁻¹' s) (hf hs)

lemma prob_cond (μ : Measure α) (G s : Set α) (hs : MeasurableSet s) :
    prob (μ[|G]) s = prob μ (G ∩ s) / prob μ G := by
  simp only [prob, cond_apply' hs, ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

lemma restricted_density_private (ρ : Measure α) (p q : α → ℝ) {G : Set α}
    (hG : MeasurableSet G) (a : ℝ)
    (h : ∀ x ∈ G, p x ≤ Real.exp a * q x ∧ q x ≤ Real.exp a * p x) :
    Indistinguishable
      ((ρ.withDensity (fun x => ENNReal.ofReal (p x))).restrict G)
      ((ρ.withDensity (fun x => ENNReal.ofReal (q x))).restrict G) a 0 := by
  have hb (f g : α → ℝ) (hf : ∀ x ∈ G, f x ≤ Real.exp a * g x) :
      (ρ.withDensity (fun x => ENNReal.ofReal (f x))).restrict G ≤
        ENNReal.ofReal (Real.exp a) • (ρ.withDensity (fun x => ENNReal.ofReal (g x))).restrict G := by
    rw [restrict_withDensity hG, restrict_withDensity hG,
      ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hG] with x hx
    simpa only [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul (Real.exp_nonneg a)] using
      ENNReal.ofReal_le_ofReal (hf x hx)
  constructor <;> intro s hs
  · simpa using (Measure.le_iff.mp (hb p q (fun x hx => (h x hx).1))) s hs
  · simpa using (Measure.le_iff.mp (hb q p (fun x hx => (h x hx).2))) s hs

lemma conditioning_tv (μ : Measure α) [IsProbabilityMeasure μ]
    {G : Set α} (hG : MeasurableSet G) (_hpos : μ G ≠ 0) :
    TVClose μ (μ[|G]) (1 - prob μ G) := by
  letI := cond_isProbabilityMeasure _hpos
  intro s hs
  have hp : 0 ≤ prob (μ[|G]) s := ENNReal.toReal_nonneg
  have hp1 : prob (μ[|G]) s ≤ 1 := by exact measureReal_le_one
  have hg : 0 ≤ prob μ G := ENNReal.toReal_nonneg
  have hg1 : prob μ G ≤ 1 := by exact measureReal_le_one
  have hd : prob μ (s \ G) ≤ 1 - prob μ G := by
    have h := measureReal_mono (μ := μ) (diff_subset_compl s G)
    simpa only [measureReal_compl hG, measureReal_univ_eq_one] using h
  have hd0 : 0 ≤ prob μ (s \ G) := ENNReal.toReal_nonneg
  have hm : prob (μ[|G]) s * prob μ G = prob μ (G ∩ s) := by
    have h := congrArg ENNReal.toReal (cond_mul_eq_inter hG s μ)
    simpa only [ENNReal.toReal_mul, prob] using h
  have ha : prob μ (G ∩ s) + prob μ (s \ G) = prob μ s := by
    simpa only [Set.inter_comm, prob, measureReal_def] using
      (measureReal_inter_add_diff (μ := μ) (s := s) hG)
  apply abs_le.mpr
  constructor <;> nlinarith

lemma conditioning_private {μ ν : Measure α} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {G : Set α} (_hG : MeasurableSet G)
    (hμ : μ G ≠ 0) (hν : ν G ≠ 0) {a : ℝ}
    (h : Indistinguishable (μ.restrict G) (ν.restrict G) a 0) :
    Indistinguishable (μ[|G]) (ν[|G]) (2 * a) 0 := by
  letI := cond_isProbabilityMeasure hμ
  letI := cond_isProbabilityMeasure hν
  have bound (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
      (hP : P G ≠ 0) (hQ : Q G ≠ 0)
      (hp : Indistinguishable (P.restrict G) (Q.restrict G) a 0)
      (s : Set α) (hs : MeasurableSet s) :
      prob (P[|G]) s ≤ Real.exp (2 * a) * prob (Q[|G]) s := by
    have hPg : 0 < prob P G := ENNReal.toReal_pos hP (measure_ne_top _ _)
    have hQg : 0 < prob Q G := ENNReal.toReal_pos hQ (measure_ne_top _ _)
    have hmass := (privacy_event_iff_real (Q.restrict G) (P.restrict G) univ a
      (le_refl (0 : ℝ))).mp (hp.2 univ MeasurableSet.univ)
    have hevent := (privacy_event_iff_real (P.restrict G) (Q.restrict G) s a
      (le_refl (0 : ℝ))).mp (hp.1 s hs)
    simp only [prob, Measure.restrict_apply MeasurableSet.univ, univ_inter, add_zero] at hmass
    simp only [prob, Measure.restrict_apply hs, Set.inter_comm s G, add_zero] at hevent
    have hr : prob Q G / prob P G ≤ Real.exp a := (div_le_iff₀ hPg).mpr hmass
    rw [prob_cond _ _ _ hs, prob_cond _ _ _ hs]
    calc
      prob P (G ∩ s) / prob P G ≤
          (Real.exp a * prob Q (G ∩ s)) / prob P G :=
        div_le_div_of_nonneg_right hevent hPg.le
      _ = Real.exp a * (prob Q (G ∩ s) / prob Q G) * (prob Q G / prob P G) := by
        field_simp
      _ ≤ Real.exp a * (prob Q (G ∩ s) / prob Q G) * Real.exp a := by
        exact mul_le_mul_of_nonneg_left hr
          (mul_nonneg (Real.exp_nonneg _) (div_nonneg ENNReal.toReal_nonneg hQg.le))
      _ = Real.exp (2 * a) * (prob Q (G ∩ s) / prob Q G) := by
        rw [show 2 * a = a + a by ring, Real.exp_add]
        ring
  constructor <;> intro s hs
  · apply (privacy_event_iff_real _ _ s _ (le_refl (0 : ℝ))).mpr
    simpa using bound μ ν hμ hν h s hs
  · apply (privacy_event_iff_real _ _ s _ (le_refl (0 : ℝ))).mpr
    simpa using bound ν μ hν hμ h.symm s hs

end DPCut
