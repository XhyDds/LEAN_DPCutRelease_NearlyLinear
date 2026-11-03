import DPCut.FullReleasePrivacy
import DPCut.FullReleaseUtility

/-!
The complete statistical conclusion of Theorem 1 for `fullReleaseLaw`, which uses
exact SDP optimizers. `Theorem1Machine` adds an implementation with a running-time bound.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- Theorem 1 for the specified full release law: measurability, normalization,
nonnegative output, privacy, and simultaneous all-cut accuracy. The numerical
constant is uniform in the graph size, public parameters, and input weights.
This statistical theorem has no computational-model or solver hypothesis. -/
theorem theorem1_statistical {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    Measurable (fullReleaseLaw (n := n) p outerUtilityConstants) ∧
      (∀ w : Weights n, IsProbabilityMeasure (fullReleaseLaw p outerUtilityConstants w) ∧
        ∀ᵐ h ∂fullReleaseLaw p outerUtilityConstants w, Nonnegative h) ∧
      EdgeDP (fullReleaseLaw (n := n) p outerUtilityConstants) p.epsilon p.delta ∧
      ∀ w : Weights n, Nonnegative w →
        HighProbability (fullReleaseLaw p outerUtilityConstants w) p.beta
          (fun h => AllCuts w h p.gamma ((2 : ℝ) ^ 166 * mainError n p)) := by
  exact ⟨measurable_fullReleaseLaw hn hp,
    fun w => ⟨fullReleaseLaw_probability hn hp w, fullReleaseLaw_nonnegative hn hp w⟩,
    fullRelease_private hn hp, fun w hw => fullRelease_utility hn hp w hw⟩

/-- Existential corollary for reductions that only need some private release. -/
theorem theorem1_statistical_exists : MainStatisticalStatement := by
  refine ⟨(2 : ℝ) ^ 166, by positivity, ?_⟩
  intro n hn p hp
  obtain ⟨_, hlaw, hprivate, haccuracy⟩ := theorem1_statistical hn hp
  refine ⟨fullReleaseKernel hn p hp, inferInstance, ?_, hprivate, haccuracy⟩
  · intro w _
    exact (hlaw w).2

end DPCut
