import DPCut.FiniteReconstruction

/-! Applying finite reconstruction to the compatibility decoder for all graph cuts. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut

lemma sum_prob_singletons {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → Prop) [DecidablePred P] :
    (∑ y, if P y then prob μ {y} else 0) = prob μ {y | P y} := by
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Set.sep_univ, Finset.mem_univ, true_and, prob, ← measureReal_def] using
      (sum_measureReal_singleton (μ := μ) (Finset.univ.filter P))

/-- On some two Hamming-separated inputs, the same output is compatible with
both. Measurability of the decoder is proved, including its empty-set fallback. -/
theorem private_cut_reconstruction {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {ε δ β γ A : ℝ} {M : Kernel (Weights n) (Weights n)}
    [IsMarkovKernel M] (hδ : 0 ≤ δ) (hβ : β ≤ 1 / 40) (hDP : EdgeDP M ε δ)
    (hacc : ∀ w : Weights n, Nonnegative w → HighProbability (M w) β
      (fun h => AllCuts w h γ A))
    (g : (ι → Bool) → Weights n) (hg : ∀ x, Nonnegative (g x))
    {t : ℕ} (ht : 0 < t) (he : Real.exp ((t : ℝ) * ε) ≤ 3)
    (hd : δ * (∑ j ∈ Finset.range t, Real.exp ((j : ℝ) * ε)) ≤ 3 / 100)
    (hstep : ∀ x i, l1 (g x - g (bitFlip i x)) ≤ t) :
    ∃ x y h, AllCuts (g x) h γ A ∧ AllCuts (g y) h γ A ∧
      (Fintype.card ι : ℝ) / 5 ≤ hamming x y := by
  classical
  obtain ⟨f, hf, hselect⟩ := exists_measurable_finite_decoder
    (fun x h => AllCuts (g x) h γ A)
    (fun x => measurableSet_allCuts measurable_const measurable_id γ A)
  let μ : (ι → Bool) → Measure (ι → Bool) := fun x => (M (g x)).map f
  haveI (x : ι → Bool) : IsProbabilityMeasure (μ x) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let p : (ι → Bool) → (ι → Bool) → ℝ := fun x y => prob (μ x) {y}
  let R : (ι → Bool) → (ι → Bool) → Prop := fun x y =>
    ∃ h, AllCuts (g x) h γ A ∧ AllCuts (g y) h γ A
  have hsum (x : ι → Bool) : ∑ y, p x y = 1 := by
    simp [p, prob, ← measureReal_def]
  have hpDP (x : ι → Bool) (i : ι) : (∑ y, if y i = x i then p x y else 0) ≤
      3 * (∑ y, if y i = x i then p (bitFlip i x) y else 0) + 3 / 100 := by
    simp only [p, sum_prob_singletons]
    have hmeas : MeasurableSet {y : ι → Bool | y i = x i} := Set.toFinite _ |>.measurableSet
    have hgdp := hDP.group hδ (hg x) (hg (bitFlip i x)) ht (hstep x i)
      (f ⁻¹' {y | y i = x i}) (hf hmeas)
    have hmap (z : ι → Bool) : prob (μ z) {y | y i = x i} =
        prob (M (g z)) (f ⁻¹' {y | y i = x i}) := by
      simp [μ, prob, Measure.map_apply hf hmeas]
    rw [hmap, hmap]
    have hh := mul_le_mul_of_nonneg_right he
      (show 0 ≤ prob (M (g (bitFlip i x))) (f ⁻¹' {y | y i = x i}) from ENNReal.toReal_nonneg)
    linarith
  have hgood (x : ι → Bool) : (∑ y, if R x y then 0 else p x y) ≤ 1 / 40 := by
    have heq : (∑ y, if R x y then 0 else p x y) = prob (μ x) {y | ¬R x y} := by
      simpa only [ite_not] using sum_prob_singletons (μ x) (fun y => ¬R x y)
    rw [heq]
    have hms : MeasurableSet {y | R x y} := Set.toFinite _ |>.measurableSet
    have hcompat : {h | AllCuts (g x) h γ A} ⊆ f ⁻¹' {y | R x y} := by
      intro h hh
      exact ⟨h, hh, hselect h ⟨x, hh⟩⟩
    have hmono : prob (M (g x)) {h | AllCuts (g x) h γ A} ≤ prob (μ x) {y | R x y} := by
      simp only [μ, prob, Measure.map_apply hf hms]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcompat)
    have hcomp : prob (μ x) {y | ¬R x y} = 1 - prob (μ x) {y | R x y} := by
      simpa only [measureReal_univ_eq_one] using (measureReal_compl (μ := μ x) hms)
    rw [hcomp]
    have hh := (hacc (g x) (hg x)).2
    linarith
  obtain ⟨x, y, ⟨h, hx, hy⟩, hdist⟩ := finite_reconstruction p
    (fun _ _ => ENNReal.toReal_nonneg) hsum hpDP R hgood
  exact ⟨x, y, h, hx, hy, hdist⟩

end DPCut
