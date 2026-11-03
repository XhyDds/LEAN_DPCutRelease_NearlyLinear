import DPCut.TimedAlgorithm
import DPCut.Arithmetic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Abstract solver specification inspired by Lee--Sidford--Wong (2015),
arXiv:1508.04874v2, Theorem 42 (Section 10.1). It is a proposition parameter,
not an added axiom. The exact-oracle, bounded-domain concave-maximization
specialization retains oracle charges and logarithmic geometry/accuracy terms.

The `TimedAlgorithm` interface supplies completion-time labels and
compatible timeout laws, but does not derive them from execution steps or
oracle calls. Arbitrary measurable functions can be represented at time zero.
Consequently this specification does not certify an operational LSW runtime,
even though the concrete SDP oracle's counter and refinement are proved.
Its use supports the release's statistical and assigned-cost conclusions only.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Metric
open scoped RealInnerProductSpace ENNReal
namespace DPCut.LSW

abbrev Space (ι : Type) [Fintype ι] := EuclideanSpace ℝ ι

/-- A fixed full-dimensional domain and a measurable family of concave objectives.
All radii, range bounds and oracle charges are public and uniform in the input. -/
structure Problem (ι : Type) [Fintype ι] (Θ : Type) [MeasurableSpace Θ] where
  body : Set (Space ι)
  value : Θ → Space ι → ℝ
  measurable_value : Measurable (Function.uncurry value)
  convex : Convex ℝ body
  compact : IsCompact body
  concave : ∀ θ, ConcaveOn ℝ body (value θ)
  innerRadius : ℝ
  outerRadius : ℝ
  inner_pos : 0 < innerRadius
  radii_order : innerRadius ≤ outerRadius
  inner_ball : closedBall 0 innerRadius ⊆ body
  outer_ball : body ⊆ closedBall 0 outerRadius
  rangeBound : ℝ
  range_one_le : 1 ≤ rangeBound
  range_le : ∀ θ x, x ∈ body → ∀ y, y ∈ body → value θ x - value θ y ≤ rangeBound

/-- Left: domain-separating normal. Right: objective value and supergradient.
There is no requirement to compute the unknown optimum. -/
abbrev Reply (ι : Type) [Fintype ι] := Space ι ⊕ (ℝ × Space ι)

def CorrectReply {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ)
    (θ : Θ) (x : Space ι) : Reply ι → Prop
  | .inl g => x ∉ P.body ∧ g ≠ 0 ∧ ∀ y ∈ P.body, ⟪g, y - x⟫ ≤ 0
  | .inr (v, g) => x ∈ P.body ∧ v = P.value θ x ∧
      ∀ y ∈ P.body, P.value θ y ≤ v + ⟪g, y - x⟫

/-- The caller supplies a counted oracle and proves its uniform cost bound.
LSW does not establish the cost of a problem-specific separation routine. -/
structure Oracle {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ) where
  answer : Θ × Space ι → Arithmetic (Reply ι)
  measurable_answer : Measurable (fun q => (answer q).value)
  correct : ∀ θ x, CorrectReply P θ x (answer (θ, x)).value
  charge : ℕ
  cost_le : ∀ q, (answer q).steps ≤ charge

def Accurate {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ)
    (ε : ℝ) (θ : Θ) (x : Space ι) : Prop :=
  x ∈ P.body ∧ ∀ y ∈ P.body, P.value θ y - P.value θ x ≤ ε

/-- Deliberately polynomial rather than the sharper LSW cubic-overhead bound.
The charge for the supplied oracle is explicit, and accuracy enters through a log. -/
def scale {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ)
    (O : Oracle P) (ε : ℝ) : ℝ :=
  1 + Fintype.card ι + O.charge + Real.log (P.outerRadius / P.innerRadius) +
    Real.log (P.rangeBound / ε)

/-- The abstract solver proposition is an explicit hypothesis at every use. Its constants
are uniform over dimensions, domains, objectives, oracles and accuracies. -/
def Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ,
    ∀ (ι : Type) (_ : Fintype ι), 1 ≤ Fintype.card ι → ∀ (Θ : Type) (_ : MeasurableSpace Θ)
      (P : Problem ι Θ) (O : Oracle P) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ∃ A : TimedAlgorithm Θ (Space ι),
        (∀ θ, ∀ᵐ z ∂A.completed θ, Accurate P ε θ z.2) ∧
        ∀ θ, A.expectedCost θ ≤ ENNReal.ofReal (C * scale P O ε ^ degree)

end DPCut.LSW

/-- Named solver proposition for Theorem 1 in the assigned-cost model. -/
def DPCut.LSWStatement : Prop := DPCut.LSW.Statement
