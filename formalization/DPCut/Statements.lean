import DPCut.Algorithms
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees

/-! Lean statements of the paper's results, with their source labels. These are
definitions of propositions, not assertions. Most are proved in other modules; the
README lists the background lemmas that are only stated. -/
set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MatrixOrder
namespace DPCut

def OptimizerStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (lam : ℝ), 0 < lam → ∀ D : Weights n,
    (∃! X, IsOptimizer lam D X) ∧
    IsOptimizer lam D (optimizer lam D) ∧
    optimum lam D = objective lam D (optimizer lam D)

def IsMatrixOptimizer {n : ℕ} (lam : ℝ) (A X : Mat n) : Prop :=
  X ∈ feasible n ∧ ∀ Y ∈ feasible n,
    matrixPairing A Y + lam * Real.log Y.det ≤ matrixPairing A X + lam * Real.log X.det

/-- `lem:stability_of_optimizer`; the implicit `lam > 0` is explicit. -/
def OptimizerStabilityStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (lam : ℝ), 0 < lam →
  ∀ (A₀ A₁ X₀ X₁ : Mat n) (ξ : Weights n),
    A₁ = A₀ + objectiveMatrix ξ →
    IsMatrixOptimizer lam A₀ X₀ → IsMatrixOptimizer lam A₁ X₁ →
    covarianceDistance X₀ X₁ ≤
      (∑ e, |ξ e| * Real.sqrt (fractionalQuery X₀ e * fractionalQuery X₁ e)) / lam ∧
    (covarianceDistance X₀ X₁ ≤ 1 / 2 → ∀ e,
      fractionalQuery X₁ e / 2 ≤ fractionalQuery X₀ e ∧
      fractionalQuery X₀ e ≤ 2 * fractionalQuery X₁ e)

/-- `lem:sdp_error`: one universal multiplicative constant, outside all inputs. -/
def SDPCertificateStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (lam : ℝ), 0 < lam →
  ∀ (D : Weights n),
    (∀ S, cut D S ≤ 2 * max (optimum lam D) 0 +
      C * (lam * n * Real.log n + l1 D / n)) ∧ mass D ≤ 2 * optimum lam D

/-- Explicit precursor to the preceding asymptotic statement; no O-notation. -/
def ShrunkenCutCertificateStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (lam : ℝ), 0 < lam → ∀ (D : Weights n) S,
    shrunkenCut S ∈ feasible n ∧
    (1 - 1 / (n : ℝ)) * cut D S ≤ optimum lam D +
      lam * ((n - 1 : ℝ) * Real.log n - Real.log (n - 1 + 1 / (n : ℝ))) - mass D / (2 * n)

/-- `prop:unbiased_estimator`; k must be positive. -/
def UnbiasedWitnessStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ X ∈ feasible n, ∀ (k : ℕ), 0 < k → ∀ e : Edge n,
    (∫ z, (z e.val.1 - z e.val.2) ^ 2 / 4 ∂gaussian X) = fractionalQuery X e ∧
    (∫ z, rawWitness z e ∂gaussianBatch X k) = fractionalQuery X e

/-- `lem:chi`, with the intended log(n/(betaChi*delta1)) parenthesization. -/
def ChiStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ X ∈ feasible n,
  ∀ (βχ δ₁ : ℝ), 0 < βχ → βχ < 1 → 0 < δ₁ → δ₁ < 1 →
  ∀ (k : ℕ), 0 < k → C * Real.log (n / (βχ * δ₁)) ≤ k →
    HighProbability (gaussianBatch X k) (min βχ δ₁) (ChiGood X)

/-- `lem:chaos`, literally the conditional conclusion. The positive denominator is explicit. -/
def ChaosStatement : Prop :=
  ∃ C c₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ ∀ (n : ℕ), 2 ≤ n →
  ∀ (D : Weights n) X, X ∈ feasible n →
  ∀ (βχ δ₁ : ℝ), 0 < βχ → βχ < 1 → 0 < δ₁ → δ₁ < 1 →
  ∀ (k : ℕ), 0 < k → C * Real.log (n / (βχ * δ₁)) ≤ k →
    0 < prob (gaussianBatch X k) {z | ChiGood X z} ∧
    c₀ ≤ prob (gaussianBatch X k)
      {z | ChiGood X z ∧ pairing D (clippedWitness z) ≥ pairing D (fractionalQuery X) / 2} /
      prob (gaussianBatch X k) {z | ChiGood X z}

/-- `lem:gaussian-privacy`, equivalent log-density-ratio formulation. -/
def GaussianPrivacyStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n k : ℕ), 0 < n → 0 < k →
  ∀ (X₀ X₁ : Mat n), X₀.PosDef → X₁.PosDef →
  ∀ (δ₁ : ℝ), 0 < δ₁ → δ₁ < 1 / 2 → covarianceDistance X₀ X₁ < 1 / 2 →
    let d := covarianceDistance X₀ X₁
    let ε₁ := C * (k * d ^ 2 + Real.sqrt (k * Real.log (1 / δ₁)) * d + Real.log (1 / δ₁) * d)
    HighProbability (gaussianBatch X₀ k) δ₁ (fun z => |batchLogRatio X₀ X₁ z| ≤ ε₁)

/-- `lem:concentration_chi-squares`: signed coefficients are allowed. -/
def WeightedChiSquareStatement : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (t : ℝ), 0 < t →
    prob (standardGaussian n)
      {z | |∑ i, a i * (z i ^ 2 - 1)| >
        2 * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt t + ‖a‖ * t)} ≤ 2 * Real.exp (-t)

/-- `lem:chi_square_tail`. -/
def ChiSquareTailStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 0 < k →
    prob (standardGaussian k)
      {z | (∑ i, z i ^ 2) / k ∉ Set.Icc (1 / 2 : ℝ) 2} ≤ 2 * Real.exp (-c * k)

/-- `lem:hypercontractivity`, using mathlib's extended Lp seminorm `eLpNorm`. -/
def HypercontractivityStatement : Prop :=
  ∀ (m : ℕ) (P : MvPolynomial (Fin m) ℝ), P.totalDegree ≤ 2 →
    eLpNorm (fun z => MvPolynomial.eval z P) 4 (standardGaussian m) ≤
      3 * eLpNorm (fun z => MvPolynomial.eval z P) 2 (standardGaussian m)

/-- The p=1,r=2,q=4 instance of `lem:holder_interpolation` used in the core proof. -/
def HolderInterpolationStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → ℝ),
    AEStronglyMeasurable W μ →
    eLpNorm W 2 μ ≤ (eLpNorm W 1 μ) ^ (1 / 3 : ℝ) * (eLpNorm W 4 μ) ^ (2 / 3 : ℝ)

/-- Full exponent range of `lem:holder_interpolation`, including q = infinity. -/
def GeneralHolderInterpolationStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → ℝ),
  ∀ (p r q : ℝ≥0∞) (θ : ℝ), AEStronglyMeasurable W μ →
    1 ≤ p → p < r → r < q → 0 < θ → θ < 1 →
    r⁻¹ = ENNReal.ofReal θ * p⁻¹ + ENNReal.ofReal (1 - θ) * q⁻¹ →
    eLpNorm W r μ ≤ (eLpNorm W p μ) ^ θ * (eLpNorm W q μ) ^ (1 - θ)

/-- `def:laplace-dist`, including normalization and the tail identity. -/
def LaplaceStatement : Prop :=
  ∀ b : ℝ, 0 < b → IsProbabilityMeasure (laplace b) ∧
    ∀ t : ℝ, 0 ≤ t → prob (laplace b) {x | t ≤ |x|} = Real.exp (-t / b)

/-- `lem:preprocess`: only Y is released, not the private clipped input. -/
def PreprocessStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (ε₀ β₀ γ : ℝ),
  0 < ε₀ → ε₀ < 1 → 0 < β₀ → β₀ < 1 → 0 < γ → γ < 1 →
    EdgeDP (preprocessLaw (n := n) ε₀ β₀ γ) ε₀ 0 ∧
    ∀ w : Weights n, Nonnegative w →
      HighProbability (preprocessLaw ε₀ β₀ γ w) β₀
        (fun y => AllCuts w (y + clipWeights (clipThreshold n ε₀ β₀ γ) w) (γ / 2) 0)

/-- `lem:gradient_privacy`, uniformly for each fixed public candidate. -/
def AggregatePrivacyStatement (c : Constants) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (ε δ β γ : ℝ),
  0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 < β → β < 1 → 0 < γ → γ < 1 →
  ∀ h : Weights n, Nonnegative h →
    EdgeDP (fun w => aggregateLaw (oracleConfig n c ε δ β) γ w h) ε δ

/-- `lem:gradient_estimation`; same constants and ideal algorithm as privacy. -/
def AggregateUtilityStatement (c : Constants) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (U ε δ β γ : ℝ),
  0 ≤ U → 0 < ε → ε < 1 → 0 < δ → δ < 1 → 0 < β → β < 1 → 0 < γ → γ < 1 →
  ∀ (w h : Weights n), Bounded U w → Nonnegative h →
    let o := oracleConfig n c ε δ β
    let B := c.certificate * (o.tau1 + o.lam * n * Real.log n + n * U)
    HighProbability (aggregateLaw o γ w h) β (fun a => a.Partition ∧ a.Accurate w h γ B)

/-- `lem:main-privacy`, stated for the same CutRelease law used in the utility goal. -/
def MainPrivacyStatement (c : Constants) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (U : ℝ), 1 ≤ U → ∀ p : Parameters, p.PrivacyValid →
    EdgeDP (cutReleaseLaw (n := n) U p c) p.epsilon p.delta

/-- `lem:utility`; the O-constant is uniform, not input dependent. -/
def BoundedUtilityStatement (c : Constants) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (U : ℝ), 1 ≤ U →
  ∀ p : Parameters, p.Valid → ∀ w : Weights n, Bounded U w →
    HighProbability (cutReleaseLaw U p c w) p.beta
      (fun h => Nonnegative h ∧ AllCuts w h p.gamma (C * boundedError n U p))

/-- Quantifiers force all algorithmic constants to work together. -/
def ParameterChoiceStatement : Prop :=
  ∃ c : Constants, c.Positive ∧ AggregatePrivacyStatement c ∧ AggregateUtilityStatement c ∧
    MainPrivacyStatement c ∧ BoundedUtilityStatement c

/-- `thm:main`, statistical content, including nonnegative outputs on every input a.s. -/
def MainStatisticalStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ p : Parameters, p.Valid →
    ∃ M : Kernel (Weights n) (Weights n), IsMarkovKernel M ∧
      GraphValued M ∧ EdgeDP M p.epsilon p.delta ∧
      ∀ w : Weights n, Nonnegative w →
        HighProbability (M w) p.beta (fun h => AllCuts w h p.gamma (C * mainError n p))

/-- Interface specifying programs, output laws and assigned costs.
`realArithmeticLSWModel` supplies the approximate release and its cost accounting
under the formal `LSWStatement` parameter. This interface does not derive costs
from execution steps; it certifies neither operational real-arithmetic nor
finite-bit running time. -/
structure ComputationalModel where
  Program : Type
  realizes : ∀ n : ℕ, Program → Parameters → Kernel (Weights n) (Weights n) → Prop
  cost : ∀ n : ℕ, Program → Parameters → Weights n → ℝ≥0∞

def runtimeScale (n : ℕ) (p : Parameters) : ℝ :=
  1 + n + 1 / p.gamma + 1 / p.epsilon + Real.log (1 / p.delta) + Real.log (1 / p.beta)

/-- Statistical guarantees plus a polynomial bound on the supplied model's cost.
Universal degree and coefficient precede n, parameters and the input graph.
Interpreting this as `thm:main`'s runtime requires an adequate execution semantics;
the interface alone does not enforce one. -/
def MainTheoremStatement (model : ComputationalModel) : Prop :=
  ∃ C Ctime : ℝ, ∃ degree : ℕ, ∃ program : model.Program, 0 < C ∧ 0 < Ctime ∧
  ∀ (n : ℕ), 2 ≤ n → ∀ p : Parameters, p.Valid →
    ∃ M : Kernel (Weights n) (Weights n),
      model.realizes n program p M ∧ IsMarkovKernel M ∧ GraphValued M ∧
      EdgeDP M p.epsilon p.delta ∧ ∀ w : Weights n, Nonnegative w →
        model.cost n program p w ≤ ENNReal.ofReal (Ctime * runtimeScale n p ^ degree) ∧
        HighProbability (M w) p.beta (fun h => AllCuts w h p.gamma (C * mainError n p))

/-- `thm:lower_bound`. -/
def LowerBoundStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 33 ≤ n → ∀ (ε δ β γ A : ℝ),
  0 < ε → ε < 1 → 0 ≤ δ → δ ≤ ε / 100 → 0 < β → β ≤ 1 / 40 →
  0 ≤ γ → γ < 1 → 0 ≤ A →
  ∀ M : Kernel (Weights n) (Weights n), IsMarkovKernel M → GraphValued M → EdgeDP M ε δ →
    (∀ w : Weights n, Nonnegative w → HighProbability (M w) β (fun h => AllCuts w h γ A)) →
    c * lowerScale n ε γ ≤ A

/-- `lem:ekkl-discrepancy`: binary weights are a convenient encoding of simple graphs. -/
def IsUnweighted {n : ℕ} (w : Weights n) : Prop := ∀ e, w e = 0 ∨ w e = 1
def vertexDegree {n : ℕ} (w : Weights n) (v : Fin n) : ℝ :=
  ∑ e, if e.val.1 = v ∨ e.val.2 = v then w e else 0
def EKKLDiscrepancyStatement : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ (n : ℕ), 2 ≤ n →
  ∀ (d σ : ℝ), 1 ≤ d → d ≤ n / 2 → 0 ≤ σ → σ ≤ 1 →
  ∀ (w w' : Weights n), IsUnweighted w → IsUnweighted w' →
    (∀ v, d / 2 ≤ vertexDegree w v ∧ vertexDegree w v ≤ 2 * d) →
    (∀ v, d / 2 ≤ vertexDegree w' v ∧ vertexDegree w' v ≤ 2 * d) →
    σ * n * d ≤ l1 (w - w') →
    ∃ S T : Finset (Fin n), Disjoint S T ∧
      κ * σ * n * Real.sqrt d ≤ |between w S T - between w' S T|

end DPCut
