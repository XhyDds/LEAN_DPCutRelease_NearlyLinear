import DPCut.CostedProgram
import DPCut.ApplicationPostprocessing

/-!
Explicit contracts for the external algorithms cited in Appendix C.
These structures are theorem inputs, not axioms or asserted implementations.
Costs use the previously selected real-arithmetic model. Parameters such as
approximation slack, privacy budgets, and fixed k are fixed before choosing the
polynomial coefficient and degree. The reductions must still prove their own
privacy, accuracy, amplification, and additional operation counts.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- A uniform family of external algorithms with an explicit polynomial charge. -/
structure PolynomialGraphAlgorithm (Output : ℕ → Type) [∀ n, MeasurableSpace (Output n)] where
  kernel : (n : ℕ) → Kernel (Weights n) (Output n)
  markov : ∀ n, IsMarkovKernel (kernel n)
  run : (n : ℕ) → Weights n → CostedLaw (Output n)
  realizes : ∀ n w, (run n w).law = kernel n w
  coefficient : ℝ
  degree : ℕ
  coefficient_pos : 0 < coefficient
  cost_le : ∀ n w, (run n w).cost ≤ ENNReal.ofReal (coefficient * (1 + (n : ℝ)) ^ degree)

/-- Unweighted complete-graph min-disagree approximation, with constant success. -/
structure CCApproximationContract (ρ p₀ : ℝ) extends PolynomialGraphAlgorithm Partition where
  approximation : ∀ n, 2 ≤ n → ∀ w, IsUnweighted w →
    HighProbability (kernel n w) (1 - p₀) (fun π => ccCost w π ≤ ρ * ccOptimum w)

/-- The fixed-k PTAS used in Corollary 31; k and the slack are external parameters. -/
structure FixedKCCContract (k : ℕ) (slack p₀ : ℝ) extends PolynomialGraphAlgorithm Partition where
  approximation : ∀ n, 2 ≤ n → ∀ w, IsUnweighted w →
    HighProbability (kernel n w) (1 - p₀) (fun π => clusterCount π ≤ k ∧
      ccCost w π ≤ (1 + slack) * ccOptimumK w k)

/-- Weighted Max-k-Cut algorithms supply an expected-value guarantee, not a
high-probability guarantee. The latter is a responsibility of the reduction. -/
structure MaxKCutContract (k : ℕ) (ρ : ℝ) extends PolynomialGraphAlgorithm Partition where
  feasible : ∀ n, 2 ≤ n → ∀ w, Nonnegative w →
    ∀ᵐ π ∂kernel n w, clusterCount π ≤ k
  approximation : ∀ n, 2 ≤ n → ∀ w, Nonnegative w →
    ρ * maxKOptimum w k ≤ ∫ π, partitionCut w π ∂kernel n w

/-- The private constant-factor baseline cited in the CC proof. Its near-linear
additive guarantee is an external dependency separate from capped release. -/
structure PrivateCCBaselineContract (ε : ℝ) (δ : ℕ → ℝ) extends PolynomialGraphAlgorithm Partition where
  ratio : ℝ
  additiveCoefficient : ℝ
  logDegree : ℕ
  ratio_ge_one : 1 ≤ ratio
  additiveCoefficient_pos : 0 < additiveCoefficient
  privacy : ∀ n, DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w')
    (kernel n) ε (δ n)
  approximation : ∀ n, 2 ≤ n → ∀ w, IsUnweighted w →
    HighProbability (kernel n w) ((n : ℝ)⁻¹ ^ 2) (fun π =>
      ccCost w π ≤ ratio * ccOptimum w + additiveCoefficient * n * Real.log n ^ logDegree)

/-- Bicriteria weighted balanced-cut oracle. Both balance constants and the
failure probability are explicit, including the nonempty comparison-family
condition needed for small recursive subproblems. -/
structure BalancedCutContract (b b' : ℝ) (factor failure : ℕ → ℝ)
    extends PolynomialGraphAlgorithm (fun n => Finset (Fin n)) where
  approximation : ∀ n, 2 ≤ n → ∀ w, Nonnegative w →
    ({S : Finset (Fin n) | Balanced b S}).Nonempty →
    HighProbability (kernel n w) (failure n) (fun S => Balanced b' S ∧
      expansion w S ≤ factor n * sInf (expansion w '' {R | Balanced b R}))

end DPCut
