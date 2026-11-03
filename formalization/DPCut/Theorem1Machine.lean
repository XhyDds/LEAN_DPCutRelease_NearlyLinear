import DPCut.TypedImplementedResources

/-! Theorem 1 for the implemented release, including a derived instruction
bound. The numerical subroutine is the deterministic ellipsoid method, as in the
paper's running-time argument. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory

namespace DPCut

theorem theorem1_machine :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ n (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid),
      Measurable (TypedMachine.implementedLaw hn p hp) ∧
      (∀ w : Weights n, IsProbabilityMeasure (TypedMachine.implementedLaw hn p hp w) ∧
        ∀ᵐ h ∂TypedMachine.implementedLaw hn p hp w, Nonnegative h) ∧
      EdgeDP (TypedMachine.implementedLaw hn p hp) p.epsilon p.delta ∧
      (∀ w : Weights n, Nonnegative w →
        HighProbability (TypedMachine.implementedLaw hn p hp w) p.beta
          (fun h => AllCuts w h p.gamma ((2:ℝ)^178*mainError n p))) ∧
      (∀ w : Weights n,
        (∀ r, TypedMachine.ImplementedExecution hn p hp w r → TypedMachine.ResourceBound n p C d r) ∧
          ∀ᵐ r ∂TypedMachine.implementedRun hn p hp w, TypedMachine.ResourceBound n p C d r) := by
  obtain ⟨C,hC,d,hresource⟩ := TypedMachine.implemented_resources
  exact ⟨C,hC,d,fun n hn p hp =>
    ⟨TypedMachine.measurable_implementedLaw hn p hp,
      fun w => ⟨TypedMachine.implemented_probability hn p hp w,
        TypedMachine.implemented_nonnegative hn p hp w⟩,
      TypedMachine.implemented_private hn p hp,
      TypedMachine.implemented_utility hn p hp,hresource n hn p hp⟩⟩

end DPCut
