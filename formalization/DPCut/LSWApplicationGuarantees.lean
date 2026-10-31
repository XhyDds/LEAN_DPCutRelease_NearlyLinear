import DPCut.LSWApplicationCosted
import DPCut.ConstrainedCut
import DPCut.HierarchyCalibration

/-! Privacy and application utility for the same approximate release laws used
in `AppendixRuntime`. These are concrete kernels, not existential ideal releases. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.LSWApplications

variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

lemma postprocess_private {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (K : Kernel (Weights n) α) [IsMarkovKernel K] :
    EdgeDP (fun w => (LSWRelease.kernel F hn p hp w).bind K) p.epsilon p.delta :=
  EdgeDP.postprocess hp.2.2.1.le hp.2.2.2.2.1.le (LSWRelease.run_private F hn p hp) K

/-- Any proved cut-based transfer applies to the actual program law. -/
lemma postprocess_utility {α : Type*} [MeasurableSpace α]
    (K : Kernel (Weights n) α) [IsMarkovKernel K] (w : Weights n) (hw : Nonnegative w)
    {τ : ℝ} (hτ : 0 ≤ τ) (P : α → Prop) (hP : MeasurableSet {a | P a})
    (hK : ∀ h, Nonnegative h → AllCuts w h p.gamma ((2:ℝ)^178 * mainError n p) →
      HighProbability (K h) τ P) :
    HighProbability ((LSWRelease.kernel F hn p hp w).bind K) (p.beta+τ) P := by
  have hgood := (LSWRelease.run_utility F hn p hp w hw).and_ae
    (measurableSet_nonnegative measurable_id) (LSWRelease.run_nonnegative F hn p hp w)
  exact hgood.bind K hp.2.2.2.2.2.2.1.le hτ hP (fun h hh => hK h hh.2 hh.1)

/-- Reference-law transfer also covers application properties proved separately. -/
lemma postprocess_tv {α : Type*} [MeasurableSpace α]
    (K : Kernel (Weights n) α) [IsMarkovKernel K] (w : Weights n) (hw : Nonnegative w) :
    TVClose ((LSWRelease.kernel F hn p hp w).bind K)
      ((fullReleaseLaw (precisionParameters p) outerUtilityConstants w).bind K) (implementationTV p) := by
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  simpa only [add_zero] using (LSWRelease.run_tv F hn p hp w hw).bind (le_refl 0)
    K.measurable K.measurable (fun h => TVClose.refl (K h) (le_refl 0))

lemma constrained_utility (K : Kernel (Weights n) (Finset (Fin n))) [IsMarkovKernel K]
    {S S' : Set (Finset (Fin n))} (hS : S.Nonempty) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hτ : 0 ≤ τ)
    (hK : ∀ h, Nonnegative h → HighProbability (K h) τ
      (fun T => T ∈ S' ∧ cut h T ≤ ρ * constrainedOptimum h S))
    (w : Weights n) (hw : Nonnegative w) :
    HighProbability ((LSWRelease.kernel F hn p hp w).bind K) (p.beta+τ)
      (fun T => T ∈ S' ∧ cut w T ≤ ρ*(1+p.gamma)/(1-p.gamma)*constrainedOptimum w S +
        (ρ+1)/(1-p.gamma)*((2:ℝ)^178*mainError n p)) := by
  apply postprocess_utility F hn p hp K w hw hτ _ (Set.toFinite _ |>.measurableSet)
  intro h hh hcuts
  exact (hK h hh).mono _ (Set.toFinite _ |>.measurableSet) (fun T hT =>
    ⟨hT.1, constrained_cut_transfer hS (by linarith [hp.2.1]) hρ hcuts hT.2⟩)

lemma max_k_utility (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {k : ℕ} (hk : 2 ≤ k) {ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (hτ : 0 ≤ τ)
    (hK : ∀ h, Nonnegative h → HighProbability (K h) τ
      (fun π => clusterCount π ≤ k ∧ ρ * maxKOptimum h k ≤ partitionCut h π))
    (w : Weights n) (hw : Nonnegative w) :
    HighProbability ((LSWRelease.kernel F hn p hp w).bind K) (p.beta+τ)
      (fun π => clusterCount π ≤ k ∧
        ρ*(1-p.gamma)/(1+p.gamma)*maxKOptimum w k -
          (2*(ρ+1)/(1+p.gamma))*((2:ℝ)^178*mainError n p) ≤ partitionCut w π) := by
  apply postprocess_utility F hn p hp K w hw hτ _ (Set.toFinite _ |>.measurableSet)
  intro h hh hcuts
  apply (hK h hh).mono _ (Set.toFinite _ |>.measurableSet)
  intro π hπ
  have he : 0 ≤ (2:ℝ)^178*mainError n p := by
    have := mainError_one_le hn hp; positivity
  exact ⟨hπ.1, max_k_transfer n k hn hk w h p.gamma _ ρ π hw hh hp.1.le
    (by linarith [hp.2.1]) he hρ hρ₁ hcuts hπ.1 hπ.2⟩

lemma hierarchy_utility (o : InducedARVContract) (w : Weights n) (hw : Nonnegative w) :
    HighProbability ((LSWRelease.kernel F hn p hp w).bind (nonprivateHierarchyKernel o n))
      (p.beta+(n:ℝ)⁻¹^10)
      (fun T => BalancedHierarchy o.balance T ∧ hcCost w T ≤
        (512*hierarchyRatioCoefficient o)*Real.sqrt (Real.log n)*hcOptimum w +
          hierarchyAddCoefficient o*((2:ℝ)^178*mainError n p)*n*(Real.log n)^(3/2:ℝ)) := by
  apply postprocess_utility F hn p hp (nonprivateHierarchyKernel o n) w hw (by positivity) _
    (Set.toFinite _ |>.measurableSet)
  intro h hh hcuts
  apply (nonprivateHierarchy_quality o hn hh).mono _ (Set.toFinite _ |>.measurableSet)
  intro T hT
  have he : 0 ≤ (2:ℝ)^178*mainError n p := by
    have := mainError_one_le hn hp; positivity
  exact ⟨hT.1, hierarchy_calibrated_transfer o hn hw hp.1.le hp.2.1 he hcuts hT.1 hT.2⟩

end DPCut.LSWApplications
