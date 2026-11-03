import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.List.OfFn

/-!
Basic definitions: weighted graphs and cuts, probability and privacy predicates,
SDP geometry, Gaussian and Laplace laws, clipping, witnesses, KL divergence,
parameters, and the lower-bound scale. Each `...Statement` in this project is a
definition of a proposition, not an axiom; most are proved in other modules.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MatrixOrder

namespace DPCut
attribute [local instance] Classical.propDecidable

/-- Standard sum and disjoint-union product sigma algebras; absent as global
Option/List instances in mathlib v4.24.0. They are not discrete on real coordinates. -/
instance {α : Type*} [MeasurableSpace α] : MeasurableSpace (Option α) :=
  MeasurableSpace.comap (fun o => (o.elim (Sum.inr ()) Sum.inl : α ⊕ Unit)) inferInstance
instance {α : Type*} [MeasurableSpace α] : MeasurableSpace (List α) :=
  MeasurableSpace.comap List.equivSigmaTuple inferInstance

/-- One representative of each unordered, loopless pair; zero-weight edges remain coordinates. -/
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Weights (n : ℕ) := Edge n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def Nonnegative {n : ℕ} (w : Weights n) : Prop := ∀ e, 0 ≤ w e
def Bounded {n : ℕ} (U : ℝ) (w : Weights n) : Prop := ∀ e, 0 ≤ w e ∧ w e ≤ U
def IsMask {n : ℕ} (r : Weights n) : Prop := Bounded 1 r
def l1 {n : ℕ} (w : Weights n) : ℝ := ∑ e, |w e|
def mass {n : ℕ} (w : Weights n) : ℝ := ∑ e, w e
def pairing {n : ℕ} (w f : Weights n) : ℝ := ∑ e, w e * f e
def hadamard {n : ℕ} (w f : Weights n) : Weights n := fun e => w e * f e
def Adjacent {n : ℕ} (w w' : Weights n) : Prop := l1 (w - w') ≤ 1

def cutQuery {n : ℕ} (S : Finset (Fin n)) : Weights n :=
  fun e => if (e.val.1 ∈ S) ↔ (e.val.2 ∈ S) then 0 else 1
def cut {n : ℕ} (w : Weights n) (S : Finset (Fin n)) : ℝ := pairing w (cutQuery S)
def between {n : ℕ} (w : Weights n) (S T : Finset (Fin n)) : ℝ :=
  ∑ e, if (e.val.1 ∈ S ∧ e.val.2 ∈ T) ∨ (e.val.2 ∈ S ∧ e.val.1 ∈ T)
    then w e else 0
def AllCuts {n : ℕ} (w h : Weights n) (γ A : ℝ) : Prop :=
  ∀ S : Finset (Fin n), |cut w S - cut h S| ≤ γ * cut w S + A

/-- Real probabilities are used only for finite/probability laws in the statements. -/
def prob {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α) : ℝ := (μ s).toReal
def HighProbability {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (β : ℝ) (P : α → Prop) : Prop :=
  MeasurableSet {x | P x} ∧ 1 - β ≤ prob μ {x | P x}
def DP {α β : Type*} [MeasurableSpace β] (adj : α → α → Prop)
    (M : α → Measure β) (ε δ : ℝ) : Prop :=
  ∀ x x', adj x x' → ∀ s, MeasurableSet s →
    M x s ≤ ENNReal.ofReal (Real.exp ε) * M x' s + ENNReal.ofReal δ
def EdgeDP {n : ℕ} {α : Type*} [MeasurableSpace α]
    (M : Weights n → Measure α) (ε δ : ℝ) : Prop :=
  DP (fun w w' => Nonnegative w ∧ Nonnegative w' ∧ Adjacent w w') M ε δ
def TVClose {α : Type*} [MeasurableSpace α] (μ ν : Measure α) (η : ℝ) : Prop :=
  ∀ s, MeasurableSet s → |prob μ s - prob ν s| ≤ η
def GraphValued {n : ℕ} (M : Weights n → Measure (Weights n)) : Prop :=
  ∀ w, Nonnegative w → ∀ᵐ h ∂M w, Nonnegative h

structure Parameters where
  gamma : ℝ
  epsilon : ℝ
  delta : ℝ
  beta : ℝ

def Parameters.Valid (p : Parameters) : Prop :=
  0 < p.gamma ∧ p.gamma ≤ 1 / 4 ∧ 0 < p.epsilon ∧ p.epsilon ≤ 1 ∧
  0 < p.delta ∧ p.delta < 1 / 10 ∧ 0 < p.beta ∧ p.beta < 1 / 10
def Parameters.PrivacyValid (p : Parameters) : Prop :=
  0 < p.gamma ∧ p.gamma < 1 ∧ 0 < p.epsilon ∧ p.epsilon ≤ 1 ∧
  0 < p.delta ∧ p.delta < 1 ∧ 0 < p.beta ∧ p.beta < 1
def logFactor (n : ℕ) (U : ℝ) (p : Parameters) : ℝ :=
  Real.log (n * U / (p.delta * p.beta * p.gamma * p.epsilon))
def mainError (n : ℕ) (p : Parameters) : ℝ :=
  n / (p.gamma * p.epsilon) * logFactor n 1 p ^ 7
def boundedError (n : ℕ) (U : ℝ) (p : Parameters) : ℝ :=
  n * U * logFactor n U p + n / (p.gamma * p.epsilon) * logFactor n U p ^ 7

/-- The paper's `𝓧`: symmetric matrices with unit diagonal and `X ≽ I/n`.
`Matrix.PosSemidef` is mathlib's PSD notion. -/
def feasible (n : ℕ) : Set (Mat n) :=
  {X | X.IsHermitian ∧ (∀ i, X i i = 1) ∧ (X - (1 / (n : ℝ)) • 1).PosSemidef}
/-- The paper's `q_e(X)`. On `feasible n`, `fractionalQuery_eq_quadratic`
identifies this with `b_eᵀ X b_e / 4`. -/
def fractionalQuery {n : ℕ} (X : Mat n) : Weights n := fun e => (1 - X e.val.1 e.val.2) / 2
def edgeVector {n : ℕ} (e : Edge n) : Fin n → ℝ :=
  fun i => (if i = e.val.1 then 1 else 0) - (if i = e.val.2 then 1 else 0)
/-- The paper's `A_D`, for arbitrary signed edge weights. -/
def objectiveMatrix {n : ℕ} (D : Weights n) : Mat n :=
  ∑ e, (D e / 4) • Matrix.vecMulVec (edgeVector e) (edgeVector e)
def matrixPairing {n : ℕ} (A X : Mat n) : ℝ := ∑ i, ∑ j, A i j * X i j
def objective {n : ℕ} (lam : ℝ) (D : Weights n) (X : Mat n) : ℝ :=
  pairing D (fractionalQuery X) + lam * Real.log X.det
def IsOptimizer {n : ℕ} (lam : ℝ) (D : Weights n) (X : Mat n) : Prop :=
  X ∈ feasible n ∧ ∀ Y ∈ feasible n, objective lam D Y ≤ objective lam D X
/-- The paper's `F(D)`, with its public regularization parameter explicit.
`optimum_eq_objective_optimizer` proves that the supremum is attained. -/
def optimum {n : ℕ} (lam : ℝ) (D : Weights n) : ℝ :=
  sSup (objective lam D '' feasible n)
/-- The paper's `X_D`, defined by total classical choice.
`optimizer_foundations` proves uniqueness and makes the fallback unreachable
when `n ≥ 2` and `lam > 0`. -/
def optimizer {n : ℕ} (lam : ℝ) (D : Weights n) : Mat n :=
  if h : ∃ X, IsOptimizer lam D X then Classical.choose h else 1
def cutSign {n : ℕ} (S : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ S then 1 else -1
def shrunkenCut {n : ℕ} (S : Finset (Fin n)) : Mat n :=
  (1 - 1 / (n : ℝ)) • Matrix.vecMulVec (cutSign S) (cutSign S) + (1 / (n : ℝ)) • 1

/-- Freeze the Frobenius norm locally; the default Pi norm is not Frobenius. -/
def frobenius {n : ℕ} (X : Mat n) : ℝ :=
  @norm (Mat n) Matrix.frobeniusNormedAddCommGroup.toNorm X
def relativeDifference {n : ℕ} (X Y : Mat n) : Mat n :=
  (CFC.sqrt X)⁻¹ * (Y - X) * (CFC.sqrt Y)⁻¹
def covarianceDistance {n : ℕ} (X Y : Mat n) : ℝ := frobenius (relativeDifference X Y)

/-- Gaussian covariance law constructed from mathlib's scalar Gaussian and product measure. -/
def standardGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)
def gaussian {n : ℕ} (X : Mat n) : Measure (Fin n → ℝ) :=
  (standardGaussian n).map (fun z => (CFC.sqrt X).mulVec z)
def gaussianBatch {n : ℕ} (X : Mat n) (k : ℕ) : Measure (Fin k → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussian X)
def gaussianLogDensity {n : ℕ} (X : Mat n) (z : Fin n → ℝ) : ℝ :=
  -(n : ℝ) / 2 * Real.log (2 * Real.pi) - Real.log X.det / 2 -
    (∑ i, z i * (X⁻¹.mulVec z) i) / 2
def batchLogRatio {n k : ℕ} (X Y : Mat n) (z : Fin k → Fin n → ℝ) : ℝ :=
  ∑ j, (gaussianLogDensity X (z j) - gaussianLogDensity Y (z j))
def rawWitness {n k : ℕ} (z : Fin k → Fin n → ℝ) : Weights n :=
  fun e => (∑ j, (z j e.val.1 - z j e.val.2) ^ 2 / 4) / k
def clippedWitness {n k : ℕ} (z : Fin k → Fin n → ℝ) : Weights n :=
  fun e => min (rawWitness z e / 2) 1
def ChiGood {n k : ℕ} (X : Mat n) (z : Fin k → Fin n → ℝ) : Prop :=
  ∀ e, fractionalQuery X e / 4 ≤ clippedWitness z e ∧
    clippedWitness z e ≤ fractionalQuery X e
def UnclippedGood {n k : ℕ} (X : Mat n) (z : Fin k → Fin n → ℝ) : Prop :=
  ∀ e, fractionalQuery X e / 2 ≤ rawWitness z e ∧
    rawWitness z e ≤ 2 * fractionalQuery X e

/-- No Laplace distribution is provided in the pinned mathlib version. -/
def laplaceDensity (b x : ℝ) : ℝ := (2 * b)⁻¹ * Real.exp (-|x| / b)
def laplace (b : ℝ) : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (laplaceDensity b x))
def clipWeights {n : ℕ} (U : ℝ) (w : Weights n) : Weights n := fun e => min (w e) U
def excess {n : ℕ} (U : ℝ) (w : Weights n) : Weights n := fun e => max (w e - U) 0
def clipThreshold (n : ℕ) (ε₀ β₀ γ : ℝ) : ℝ := 8 / (ε₀ * γ) * Real.log (n / β₀)
def noiseShift (n : ℕ) (ε₀ β₀ : ℝ) : ℝ := 2 / ε₀ * Real.log (n / β₀)
def noisyExcess {n : ℕ} (U V : ℝ) (w noise : Weights n) : Weights n :=
  fun e => max 0 (excess U w e + noise e - V)
def preprocessLaw {n : ℕ} (ε₀ β₀ γ : ℝ) (w : Weights n) : Measure (Weights n) :=
  (Measure.pi (fun _ : Edge n => laplace (1 / ε₀))).map
    (noisyExcess (clipThreshold n ε₀ β₀ γ) (noiseShift n ε₀ β₀) w)

structure Aggregate (n : ℕ) where
  plus : Weights n
  minus : Weights n
  residual : Weights n
  deriving Inhabited

def Aggregate.Partition {n : ℕ} (a : Aggregate n) : Prop :=
  IsMask a.plus ∧ IsMask a.minus ∧ IsMask a.residual ∧
  ∀ e, a.plus e + a.minus e + a.residual e = 1
def Aggregate.Accurate {n : ℕ} (a : Aggregate n) (w h : Weights n) (γ B : ℝ) : Prop :=
  pairing h a.plus ≥ (1 + γ) * pairing w a.plus ∧
  pairing h a.minus ≤ (1 - γ) * pairing w a.minus ∧
  AllCuts (hadamard w a.residual) (hadamard h a.residual) γ B
def Aggregate.Accepts {n : ℕ} (a : Aggregate n) (h : Weights n) : Prop :=
  max (pairing h a.plus) (pairing h a.minus) ≤ pairing h a.residual
def mwUpdate {n : ℕ} (M θ η : ℝ) (h g : Weights n) : Weights n :=
  fun e => M * (h e * Real.exp (-θ * η * g e)) /
    (∑ f, h f * Real.exp (-θ * η * g f))
def initialEstimate {n : ℕ} (M : ℝ) (a : Weights n) : Weights n := fun e => M * a e / mass a
def residualUpdate {n : ℕ} (a r : Weights n) : Weights n := fun e => a e * (1 - r e)
def discreteMeasure {ι : Type*} [Fintype ι] [MeasurableSpace ι] (p : ι → ℝ) : Measure ι :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac i
def normalizedKL {n : ℕ} (w h : Weights n) (M Mtilde : ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (discreteMeasure (fun e => w e / M))
    (discreteMeasure (fun e => h e / Mtilde))

def innerHorizon (n : ℕ) (γ : ℝ) : ℕ :=
  1 + ⌈64 * (1 + γ) ^ 2 * Real.log n / γ ^ 2⌉₊
def outerHorizon (n : ℕ) (U C : ℝ) : ℕ := ⌈C * Real.log (n * U)⌉₊
def stepSize (γ : ℝ) : ℝ := γ / (8 * (1 + γ))
def stoppingThreshold (n : ℕ) (U C : ℝ) (p : Parameters) : ℝ :=
  C * (n * U * logFactor n U p + n / (p.gamma * p.epsilon) * logFactor n U p ^ 6)

/-- Lower bound's γ=0 convention must be explicit: real division by zero is zero in Lean. -/
def lowerScale (n : ℕ) (ε γ : ℝ) : ℝ :=
  (1 - γ) * if γ = 0 then n * Real.sqrt n / ε
    else min (n * Real.sqrt n / ε) (n / (ε * γ))

end DPCut
