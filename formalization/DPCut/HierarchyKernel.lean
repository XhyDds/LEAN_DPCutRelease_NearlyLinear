import DPCut.HierarchyQuality
import DPCut.ApplicationPostprocessing

/-! The finite-fuel recursive hierarchy algorithm. The public split guard makes
both recursive subproblems strictly smaller, even when an oracle call fails. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (K : Finset (Fin n) → Kernel (Weights n) (Finset (Fin n)))
  [∀ A, IsMarkovKernel (K A)]

def hierarchyLaw (c : ℝ) : ℕ → Finset (Fin n) → Weights n → Measure (Hierarchy n)
  | 0, A, _ => Measure.dirac {A}
  | t + 1, A, w => if 2 ≤ A.card then
      (K A w).bind fun raw =>
        let S := safeHierarchySplit c A raw
        (hierarchyLaw c t S w).bind fun L =>
          (hierarchyLaw c t (A \ S) w).map (joinHierarchy A L)
    else Measure.dirac {A}

instance hierarchyLaw_probability (c : ℝ) (t : ℕ) (A : Finset (Fin n)) (w : Weights n) :
    IsProbabilityMeasure (hierarchyLaw K c t A w) := by
  induction t generalizing A with
  | zero =>
    change IsProbabilityMeasure (Measure.dirac ({A} : Hierarchy n))
    infer_instance
  | succ t ih =>
    simp only [hierarchyLaw]
    split_ifs
    · letI (B : Finset (Fin n)) := ih B
      letI (raw : Finset (Fin n)) (L : Hierarchy n) : IsProbabilityMeasure
          ((hierarchyLaw K c t (A \ safeHierarchySplit c A raw) w).map (joinHierarchy A L)) :=
        Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
      letI (raw : Finset (Fin n)) : IsProbabilityMeasure
          ((hierarchyLaw K c t (safeHierarchySplit c A raw) w).bind fun L =>
            (hierarchyLaw K c t (A \ safeHierarchySplit c A raw) w).map (joinHierarchy A L)) :=
        probability_bind _ _ (measurable_of_finite _)
      exact probability_bind _ _ (measurable_of_finite _)
    · infer_instance

lemma measurable_hierarchyLaw (c : ℝ) (t : ℕ) (A : Finset (Fin n)) :
    Measurable (hierarchyLaw K c t A) := by
  induction t generalizing A with
  | zero => exact measurable_const
  | succ t ih =>
    simp only [hierarchyLaw]
    split_ifs
    · apply measurable_bind_kernel (K A).measurable
      apply measurable_from_prod_countable_left
      intro raw
      apply measurable_bind_kernel (μ := hierarchyLaw K c t (safeHierarchySplit c A raw))
        (ih (safeHierarchySplit c A raw))
      apply measurable_from_prod_countable_left
      intro L
      exact (Measure.measurable_map (joinHierarchy A L) (measurable_of_finite _)).comp (ih (A \ safeHierarchySplit c A raw))
    · exact measurable_const

def hierarchyKernel (c : ℝ) (t : ℕ) (A : Finset (Fin n)) : Kernel (Weights n) (Hierarchy n) :=
  ⟨hierarchyLaw K c t A, measurable_hierarchyLaw K c t A⟩

instance hierarchyKernel_markov (c : ℝ) (t : ℕ) (A : Finset (Fin n)) :
    IsMarkovKernel (hierarchyKernel K c t A) := ⟨fun w => hierarchyLaw_probability K c t A w⟩

end DPCut
