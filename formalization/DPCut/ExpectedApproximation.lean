import DPCut.BestOf

/-! Converting bounded expected approximation to success probability, and then
amplifying by independent repetition and public objective comparison. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
variable {α : Type*} [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α]

lemma expected_approximation_success {μ : Measure α} [IsProbabilityMeasure μ]
    {score : α → ℝ} {V ρ s : ℝ} (hV : 0 ≤ V) (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hscore : ∀ᵐ x ∂μ, 0 ≤ score x ∧ score x ≤ V)
    (hmean : ρ * V ≤ ∫ x, score x ∂μ) :
    s ≤ prob μ {x | (ρ - s) * V ≤ score x} := by
  let G : Set α := {x | (ρ - s) * V ≤ score x}
  have hG : MeasurableSet G := Set.to_countable _ |>.measurableSet
  by_cases htriv : (ρ - s) * V ≤ 0
  · have ha : ∀ᵐ x ∂μ, x ∈ G := hscore.mono fun x hx => htriv.trans hx.1
    have he : μ G = 1 := (ae_iff_measure_eq hG.nullMeasurableSet).mp ha |>.trans (measure_univ (μ := μ))
    change s ≤ prob μ G
    simpa [prob, he] using hs1
  · have hVpos : 0 < V := lt_of_le_of_ne hV (by intro h; simp [← h] at htriv)
    have hρs : 0 ≤ ρ - s := by nlinarith
    have hbound : ∀ᵐ x ∂μ, score x ≤ (ρ - s) * V + G.indicator (fun _ => V) x := by
      filter_upwards [hscore] with x hx
      by_cases hxG : x ∈ G
      · simp only [Set.indicator_of_mem hxG]
        nlinarith
      · simp only [Set.indicator_of_notMem hxG, add_zero]
        exact le_of_lt (lt_of_not_ge hxG)
    have hi := integral_mono_ae (Integrable.of_finite : Integrable score μ)
      (Integrable.of_finite : Integrable (fun x => (ρ - s) * V + G.indicator (fun _ => V) x) μ) hbound
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const,
      integral_indicator_const V hG] at hi
    simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hi
    change (∫ x, score x ∂μ) ≤ (ρ - s) * V + prob μ G * V at hi
    nlinarith

lemma bestOf_success {μ : Measure α} [IsProbabilityMeasure μ]
    (score : α → ℝ) (b : ℝ) {s : ℝ} (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hgood : s ≤ prob μ {x | b ≤ score x}) (t : ℕ) (seed : α) :
    HighProbability (bestOf μ score t seed) ((1 - s) ^ t) (fun x => b ≤ score x) := by
  have hG : MeasurableSet {x | b ≤ score x} := Set.to_countable _ |>.measurableSet
  have hfail : μ {x | score x < b} ≤ ENNReal.ofReal (1 - s) := by
    apply (prob_le_iff_measure_le (sub_nonneg.mpr hs1)).mp
    have hh := measureReal_add_measureReal_compl (μ := μ) hG
    rw [measureReal_univ_eq_one] at hh
    have he : {x | b ≤ score x}ᶜ = {x | score x < b} := by ext x; simp
    rw [he] at hh
    change prob μ {x | b ≤ score x} + prob μ {x | score x < b} = 1 at hh
    linarith
  apply highProbability_of_failure hG (pow_nonneg (sub_nonneg.mpr hs1) _)
  simp only [not_le]
  rw [bestOf_failure]
  split_ifs
  · exact (pow_le_pow_left' hfail t).trans_eq (ENNReal.ofReal_pow (sub_nonneg.mpr hs1) t).symm
  · exact zero_le _

omit [MeasurableSpace α] [Fintype α] [MeasurableSingletonClass α] in
lemma repetition_failure_bound {s τ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hτ : 0 < τ) (t : ℕ) (ht : Real.log (1 / τ) / s ≤ t) :
    (1 - s) ^ t ≤ τ := by
  have hexp : 1 - s ≤ Real.exp (-s) := by linarith [Real.add_one_le_exp (-s)]
  calc
    (1 - s) ^ t ≤ Real.exp (-s) ^ t := pow_le_pow_left₀ (sub_nonneg.mpr hs1) hexp _
    _ = Real.exp (-(s * t)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (Real.log τ) := by
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ hs).mp ht
      rw [one_div, Real.log_inv] at hh
      nlinarith
    _ = τ := Real.exp_log hτ

end DPCut
