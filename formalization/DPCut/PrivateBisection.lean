import DPCut.BisectionPadding
import DPCut.HierarchyProbability

/-! Private minimum bisection, including the odd-size isolated-vertex reduction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

@[fun_prop] lemma measurable_addIsolatedVertex (n : ℕ) :
    Measurable (addIsolatedVertex (n := n)) := by
  apply measurable_pi_lambda
  intro e
  unfold addIsolatedVertex embedWeights
  apply Finset.measurable_sum
  intro f hf
  split_ifs <;> fun_prop

def paddedBisectionKernel {n : ℕ} (K : Kernel (Weights (n + 1)) (Finset (Fin (n + 1)))) :
    Kernel (Weights n) (Finset (Fin n)) :=
  ⟨fun w => (K (addIsolatedVertex w)).map restrictCut,
    ((Measure.measurable_map restrictCut (measurable_of_finite _)).comp K.measurable).comp (measurable_addIsolatedVertex n)⟩

instance paddedBisectionKernel_markov {n : ℕ}
    (K : Kernel (Weights (n + 1)) (Finset (Fin (n + 1)))) [IsMarkovKernel K] :
    IsMarkovKernel (paddedBisectionKernel K) :=
  ⟨fun _ => Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩

lemma odd_bisection_solver {n : ℕ} (hn : n % 2 = 1)
    (K : Kernel (Weights (n + 1)) (Finset (Fin (n + 1)))) [IsMarkovKernel K]
    {ρ τ : ℝ} (hAlg : ∀ h, Nonnegative h → HighProbability (K h) τ
      (fun S => ExactBisection S ∧ cut h S ≤ ρ * constrainedOptimum h {R | ExactBisection R}))
    {w : Weights n} (hw : Nonnegative w) :
    HighProbability (paddedBisectionKernel K w) τ
      (fun S => NearBisection S ∧ cut w S ≤ ρ * constrainedOptimum w {R | NearBisection R}) := by
  apply (hAlg (addIsolatedVertex w) (addIsolatedVertex_nonnegative hw)).map_finite restrictCut
  intro S hS
  exact ⟨restrict_exact_bisection hS.1, by
    simpa only [cut_addIsolatedVertex, odd_bisection_optimum hn] using hS.2⟩

/-- With a nonprivate O(log n) bisection contract, this is the stated private
O(log n) approximation with near-linear additive error. The exact formula also
retains arbitrary valid release budgets and external solver failure. -/
theorem private_bisection : ∃ CA : ℝ, 0 < CA ∧ ∀ n, 2 ≤ n →
    ∀ p : Parameters, p.Valid → ∀ ρ τ : ℝ, 1 ≤ ρ → 0 ≤ τ → τ < 1 →
    ∀ K : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel K →
      (∀ h, Nonnegative h → HighProbability (K h) τ
        (fun S => NearBisection S ∧ cut h S ≤ ρ * constrainedOptimum h {R | NearBisection R})) →
      ∃ M : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel M ∧ EdgeDP M p.epsilon p.delta ∧
        ∀ w, Nonnegative w → HighProbability (M w) (p.beta + τ)
          (fun S => NearBisection S ∧ cut w S ≤
            ρ * (1 + p.gamma) / (1 - p.gamma) * constrainedOptimum w {R | NearBisection R} +
            (ρ + 1) / (1 - p.gamma) * (CA * mainError n p)) := by
  obtain ⟨CA, hCA, hmain⟩ := theorem34
  refine ⟨CA, hCA, ?_⟩
  intro n hn p hp ρ τ hρ hτ hτ₁ K hK hAlg
  exact hmain n hn p hp {S | NearBisection S} {S | NearBisection S}
    (bisection_family_nonempty n) (bisection_family_nonempty n) ρ τ hρ hτ hτ₁ K hK hAlg

end DPCut
