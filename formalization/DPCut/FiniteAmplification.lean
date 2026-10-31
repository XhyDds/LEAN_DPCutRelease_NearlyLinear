import DPCut.ExpectedApproximation

/-! Amplification with a public feasibility test and a feasible fallback. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable
variable {α Θ : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [MeasurableSpace Θ]

def safeFinite (P : α → Prop) (seed x : α) : α := if P x then x else seed

omit [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α] in
lemma safeFinite_property (P : α → Prop) {seed : α} (hs : P seed) (x : α) :
    P (safeFinite P seed x) := by unfold safeFinite; split <;> assumption

def safeFiniteKernel (K : Kernel Θ α) (P : α → Prop) (seed : α) : Kernel Θ α :=
  ⟨fun θ => (K θ).map (safeFinite P seed),
    (Measure.measurable_map _ (measurable_of_finite _)).comp K.measurable⟩

instance safeFiniteKernel_markov (K : Kernel Θ α) [IsMarkovKernel K] (P : α → Prop) (seed : α) :
    IsMarkovKernel (safeFiniteKernel K P seed) :=
  ⟨fun _ => Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩

def amplifiedFinite (K : Kernel Θ α) [IsMarkovKernel K] (P : α → Prop)
    (score : Θ → α → ℝ) (hscore : ∀ x, Measurable (fun θ => score θ x)) (t : ℕ) (seed : α) :
    Kernel Θ α := bestOfKernel (safeFiniteKernel K P seed) score hscore t seed

instance amplifiedFinite_markov (K : Kernel Θ α) [IsMarkovKernel K] (P : α → Prop)
    (score : Θ → α → ℝ) (hscore : ∀ x, Measurable (fun θ => score θ x)) (t : ℕ) (seed : α) :
    IsMarkovKernel (amplifiedFinite K P score hscore t seed) := bestOfKernel_markov _ _ _ _ _

lemma amplifiedFinite_success (K : Kernel Θ α) [IsMarkovKernel K] (P : α → Prop)
    (score : Θ → α → ℝ) (hscore : ∀ x, Measurable (fun θ => score θ x)) (seed : α)
    (hseed : P seed) (θ : Θ) {B s τ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ)
    (hgood : HighProbability (K θ) (1 - s) (fun x => P x ∧ B ≤ score θ x))
    (t : ℕ) (ht : Real.log (1 / τ) / s ≤ t) :
    HighProbability (amplifiedFinite K P score hscore t seed θ) τ (fun x => P x ∧ B ≤ score θ x) := by
  have hsafe : s ≤ prob (safeFiniteKernel K P seed θ) {x | B ≤ score θ x} := by
    change s ≤ ((K θ).map (safeFinite P seed) _).toReal
    rw [Measure.map_apply (measurable_of_finite _) (Set.toFinite _ |>.measurableSet)]
    have hsub : {x | P x ∧ B ≤ score θ x} ⊆ (safeFinite P seed) ⁻¹' {x | B ≤ score θ x} := by
      intro x hx
      simpa only [Set.mem_preimage, Set.mem_setOf_eq, safeFinite, if_pos hx.1] using hx.2
    have hmass : s ≤ prob (K θ) {x | P x ∧ B ≤ score θ x} := by
      have hh := hgood.2
      linarith
    exact hmass.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub))
  have hsuccess := (bestOf_success (score θ) B hs.le hs1 hsafe t seed).weaken
    (repetition_failure_bound hs hs1 hτ t ht)
  have hfeasible : ∀ᵐ x ∂safeFiniteKernel K P seed θ, P x := by
    apply (ae_map_iff (measurable_of_finite _).aemeasurable (Set.toFinite _ |>.measurableSet)).mpr
    exact Filter.Eventually.of_forall (safeFinite_property P hseed)
  have ha := bestOf_ae (safeFiniteKernel K P seed θ) (score θ) t seed hseed hfeasible
  exact (hsuccess.and_ae (Set.toFinite _ |>.measurableSet) ha).mono _
    (Set.toFinite _ |>.measurableSet) (fun x hx => ⟨hx.2, hx.1⟩)

end DPCut
