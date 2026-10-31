import DPCut.ApplicationPostprocessing

/-! Independent repetition followed by selecting the largest public objective.
The selection never computes the unknown optimum or an acceptance threshold. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
variable {α Θ : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]
  [MeasurableSpace Θ]

def bestChoice (score : α → ℝ) (x y : α) : α := if score x ≤ score y then y else x

omit [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] in
lemma score_bestChoice (score : α → ℝ) (x y : α) :
    score (bestChoice score x y) = max (score x) (score y) := by
  simp only [bestChoice, max_def]; split <;> rfl

def bestOf (μ : Measure α) (score : α → ℝ) : ℕ → α → Measure α
  | 0, seed => Measure.dirac seed
  | t + 1, seed => μ.bind fun x => bestOf μ score t (bestChoice score seed x)

instance bestOf_probability (μ : Measure α) [IsProbabilityMeasure μ]
    (score : α → ℝ) (t : ℕ) (seed : α) : IsProbabilityMeasure (bestOf μ score t seed) := by
  induction t generalizing seed with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac seed))
  | succ t ih =>
    letI (x : α) := ih (bestChoice score seed x)
    exact probability_bind μ _ (measurable_of_countable _)

lemma measurable_bestOf {μ : Θ → Measure α} (hμ : Measurable μ)
    [∀ θ, IsProbabilityMeasure (μ θ)] {score : Θ → α → ℝ}
    (hs : ∀ x, Measurable (fun θ => score θ x)) (t : ℕ) (seed : α) :
    Measurable (fun θ => bestOf (μ θ) (score θ) t seed) := by
  induction t generalizing seed with
  | zero => exact measurable_const
  | succ t ih =>
    apply measurable_bind_kernel hμ
    apply measurable_from_prod_countable_left
    intro x
    have hr : Measurable (fun p : Θ × α => bestOf (μ p.1) (score p.1) t p.2) :=
      measurable_from_prod_countable_left ih
    exact hr.comp (measurable_id.prodMk
      (Measurable.ite (measurableSet_le (hs seed) (hs x)) measurable_const measurable_const))

def bestOfKernel (K : Kernel Θ α) [IsMarkovKernel K] (score : Θ → α → ℝ)
    (hs : ∀ x, Measurable (fun θ => score θ x)) (t : ℕ) (seed : α) : Kernel Θ α :=
  ⟨fun θ => bestOf (K θ) (score θ) t seed, measurable_bestOf K.measurable hs t seed⟩

instance bestOfKernel_markov (K : Kernel Θ α) [IsMarkovKernel K] (score : Θ → α → ℝ)
    (hs : ∀ x, Measurable (fun θ => score θ x)) (t : ℕ) (seed : α) :
    IsMarkovKernel (bestOfKernel K score hs t seed) := ⟨fun _ => bestOf_probability _ _ _ _⟩

lemma bestOf_failure (μ : Measure α) [IsProbabilityMeasure μ]
    (score : α → ℝ) (b : ℝ) (t : ℕ) (seed : α) :
    bestOf μ score t seed {x | score x < b} =
      if score seed < b then (μ {x | score x < b}) ^ t else 0 := by
  have hB : MeasurableSet {x | score x < b} := Set.to_countable _ |>.measurableSet
  induction t generalizing seed with
  | zero => simp [bestOf, Measure.dirac_apply' _ hB, Set.indicator_apply]
  | succ t ih =>
    rw [bestOf, Measure.bind_apply hB (measurable_of_countable _).aemeasurable]
    simp_rw [ih, score_bestChoice, max_lt_iff]
    by_cases hb : score seed < b
    · simp only [hb, true_and]
      change (∫⁻ x, {x | score x < b}.indicator (fun _ => (μ {x | score x < b}) ^ t) x ∂μ) = _
      rw [lintegral_indicator hB]
      simp [pow_succ]
    · simp [hb]

lemma bestOf_ae (μ : Measure α) (score : α → ℝ) (t : ℕ) (seed : α)
    {P : α → Prop} (hseed : P seed) (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂bestOf μ score t seed, P x := by
  have hm : MeasurableSet {x | P x} := Set.to_countable _ |>.measurableSet
  induction t generalizing seed with
  | zero => exact (ae_dirac_iff hm).mpr hseed
  | succ t ih =>
    apply ae_bind_of_ae_ae (measurable_of_countable _) hm
    filter_upwards [hP] with x hx
    apply ih
    unfold bestChoice
    split <;> assumption

end DPCut
