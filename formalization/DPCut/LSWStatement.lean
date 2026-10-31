import DPCut.TimedAlgorithm
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
External dependency: a polynomial consequence of Lee--Sidford--Wong (2015),
arXiv:1508.04874v2, Theorem 42 (Section 10.1), in the costed real model.

This is a proposition, not an axiom and not an inhabited solver contract.
It is the exact-oracle, bounded-domain concave-maximization specialization of
their convex-minimization result. The objective range converts their relative
accuracy to absolute accuracy. We retain the oracle charge and logarithmic
geometry/accuracy dependence, and weaken the precise asymptotic bound to a
uniform polynomial. The timed-program interface makes measurability and the
operational meaning of timeout explicit; these are part of the external
algorithm interpretation, not consequences of a bare optimizer-existence claim.
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

/-- The caller supplies this oracle and its uniform charge. LSW does not
establish the implementation cost of a problem-specific separation routine. -/
structure Oracle {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ) where
  answer : Θ × Space ι → Reply ι
  measurable_answer : Measurable answer
  correct : ∀ θ x, CorrectReply P θ x (answer (θ, x))
  charge : ℕ

def Accurate {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ)
    (ε : ℝ) (θ : Θ) (x : Space ι) : Prop :=
  x ∈ P.body ∧ ∀ y ∈ P.body, P.value θ y - P.value θ x ≤ ε

/-- Deliberately polynomial rather than the sharper LSW cubic-overhead bound.
The charge for the supplied oracle is explicit, and accuracy enters through a log. -/
def scale {ι : Type} [Fintype ι] {Θ : Type} [MeasurableSpace Θ] (P : Problem ι Θ)
    (O : Oracle P) (ε : ℝ) : ℝ :=
  1 + Fintype.card ι + O.charge + Real.log (P.outerRadius / P.innerRadius) +
    Real.log (P.rangeBound / ε)

/-- The external result is an explicit hypothesis at every use. Its constants
are uniform over dimensions, domains, objectives, oracles and accuracies. -/
def Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ degree : ℕ,
    ∀ (ι : Type) (_ : Fintype ι), 1 ≤ Fintype.card ι → ∀ (Θ : Type) (_ : MeasurableSpace Θ)
      (P : Problem ι Θ) (O : Oracle P) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      ∃ A : TimedAlgorithm Θ (Space ι),
        (∀ θ, ∀ᵐ z ∂A.completed θ, Accurate P ε θ z.2) ∧
        ∀ θ, A.expectedCost θ ≤ ENNReal.ofReal (C * scale P O ε ^ degree)

end DPCut.LSW

/-- Named external proposition for the conditional Theorem 1 development. -/
def DPCut.LSWStatement : Prop := DPCut.LSW.Statement
