import DPCut.BasicPrivacyComposition
import DPCut.InnerLoopUtility
import DPCut.Applications

/-! Probability and privacy transfer for Appendix C's postprocessing reductions. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

instance {α : Type*} [Fintype α] : MeasurableSingletonClass (Finset α) :=
  ⟨fun _ => trivial⟩

lemma DP.mono {X Y : Type*} [MeasurableSpace Y] {adj : X → X → Prop}
    {M : X → Measure Y} {ε δ ε' δ' : ℝ} (h : DP adj M ε δ)
    (he : ε ≤ ε') (hd : δ ≤ δ') : DP adj M ε' δ' := by
  intro x x' hx s hs
  exact (h x x' hx s hs).trans (add_le_add
    (mul_le_mul_right' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)) _)
    (ENNReal.ofReal_le_ofReal hd))

lemma HighProbability.weaken {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {P : X → Prop} {β β' : ℝ}
    (h : HighProbability μ β P) (hβ : β ≤ β') : HighProbability μ β' P :=
  ⟨h.1, (sub_le_sub_left hβ 1).trans h.2⟩

lemma DP.postprocess {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [StandardBorelSpace Y] [StandardBorelSpace Z]
    {adj : X → X → Prop} (hsymm : Symmetric adj)
    {M : Kernel X Y} [IsMarkovKernel M] {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hDP : DP adj M ε δ) (K : Kernel Y Z) [IsMarkovKernel K] :
    DP adj (fun x => (M x).bind K) ε δ := by
  intro x x' hx
  have hh : Indistinguishable (M x) (M x') ε δ := ⟨hDP x x' hx, hDP x' x (hsymm hx)⟩
  have hb := hh.bind_approx hε (le_refl 0) hδ (le_refl 0) K.measurable K.measurable
    (fun y => Indistinguishable.of_eq (μ := K y) rfl (le_refl 0) (le_refl 0))
  simpa using hb.1

lemma EdgeDP.postprocess {n : ℕ} {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y]
    {M : Kernel (Weights n) (Weights n)} [IsMarkovKernel M]
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hDP : EdgeDP M ε δ)
    (K : Kernel (Weights n) Y) [IsMarkovKernel K] :
    EdgeDP (fun w => (M w).bind K) ε δ := by
  apply DP.postprocess ?_ hε hδ hDP K
  intro w w' hw
  refine ⟨hw.2.1, hw.1, ?_⟩
  simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2

lemma HighProbability.and_ae {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {P Q : X → Prop} {β : ℝ}
    (hP : HighProbability μ β P) (hQ : MeasurableSet {x | Q x}) (hQa : ∀ᵐ x ∂μ, Q x) :
    HighProbability μ β (fun x => P x ∧ Q x) := by
  refine ⟨hP.1.inter hQ, ?_⟩
  have he : {x | P x ∧ Q x} =ᵐ[μ] {x | P x} := by
    filter_upwards [hQa] with x hx
    change (P x ∧ Q x) = P x
    simp [hx]
  simpa only [prob, measure_congr he] using hP.2

lemma HighProbability.bind {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} [IsProbabilityMeasure μ] (K : Kernel X Y) [IsMarkovKernel K]
    {P : X → Prop} {Q : Y → Prop} {β τ : ℝ} (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hP : HighProbability μ β P) (hQ : MeasurableSet {y | Q y})
    (hK : ∀ x, P x → HighProbability (K x) τ Q) : HighProbability (μ.bind K) (β + τ) Q := by
  letI := probability_bind μ K K.measurable
  apply highProbability_of_failure hQ (add_nonneg hβ hτ)
  exact measure_bind_le_of_good K.measurable hP.1 hQ.compl hβ hτ
    (hP.failure_bound hβ) (fun x hx => (hK x hx).failure_bound hτ)

end DPCut
