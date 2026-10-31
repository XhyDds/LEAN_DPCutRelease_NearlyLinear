import DPCut.CappedCosted
import DPCut.FiniteAmplification
import DPCut.CCOptimization

/-! Costed independent repetition, with law equality to the public-score amplifier. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut
variable {α : Type} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def costedBestOf (sample : CostedLaw α) (score : α → ℝ) (compareCost : ℝ≥0∞) : ℕ → α → CostedLaw α
  | 0, seed => .pure seed
  | t + 1, seed => sample.bind fun x =>
      .charge compareCost (costedBestOf sample score compareCost t (bestChoice score seed x))

omit [Fintype α] [MeasurableSingletonClass α] in
lemma costedBestOf_law (sample : CostedLaw α) (score : α → ℝ) (c : ℝ≥0∞) (t : ℕ) (seed : α) :
    (costedBestOf sample score c t seed).law = bestOf sample.law score t seed := by
  induction t generalizing seed with
  | zero => rfl
  | succ t ih =>
    simp only [costedBestOf, bestOf, CostedLaw.bind_law, CostedLaw.charge_law, ih]

omit [Fintype α] [MeasurableSingletonClass α] in
lemma costedBestOf_cost (sample : CostedLaw α) (score : α → ℝ) (c : ℝ≥0∞)
    (t : ℕ) (seed : α) {B : ℝ≥0∞} (hB : sample.cost ≤ B) :
    (costedBestOf sample score c t seed).cost ≤ t * (B + c) := by
  induction t generalizing seed with
  | zero => simp [costedBestOf, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ B + (c + t * (B + c)) := CostedLaw.bind_cost_le _ _ hB
        (fun x => CostedLaw.charge_cost_le _ _ (ih _))
      _ = _ := by push_cast; ring

def costedAmplifiedFinite (sample : CostedLaw α) (P : α → Prop) (score : α → ℝ)
    (c : ℝ≥0∞) (t : ℕ) (seed : α) : CostedLaw α :=
  costedBestOf (sample.map (safeFinite P seed) c) score c t seed

lemma costedAmplifiedFinite_law {Θ : Type*} [MeasurableSpace Θ]
    (K : Kernel Θ α) [IsMarkovKernel K] (P : α → Prop) (score : Θ → α → ℝ)
    (hs : ∀ x, Measurable (fun θ => score θ x)) (θ : Θ) (sample : CostedLaw α)
    (hreal : sample.law = K θ) (c : ℝ≥0∞) (t : ℕ) (seed : α) :
    (costedAmplifiedFinite sample P (score θ) c t seed).law = amplifiedFinite K P score hs t seed θ := by
  rw [costedAmplifiedFinite, costedBestOf_law, CostedLaw.map_law, hreal]
  rfl

lemma costedAmplifiedFinite_cost (sample : CostedLaw α) (P : α → Prop) (score : α → ℝ)
    (c : ℝ≥0∞) (t : ℕ) (seed : α) {B : ℝ≥0∞} (hB : sample.cost ≤ B) :
    (costedAmplifiedFinite sample P score c t seed).cost ≤ t * (B + 2 * c) := by
  have hh := costedBestOf_cost (sample.map (safeFinite P seed) c) score c t seed
    (add_le_add_right hB c)
  convert hh using 1
  ring

end DPCut
