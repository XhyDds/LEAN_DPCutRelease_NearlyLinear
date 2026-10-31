import DPCut.Definitions
import Mathlib.Probability.Kernel.Composition.Comp

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def Indistinguishable {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (ε δ : ℝ) : Prop :=
  (∀ s, MeasurableSet s → μ s ≤ ENNReal.ofReal (Real.exp ε) * ν s + ENNReal.ofReal δ) ∧
  (∀ s, MeasurableSet s → ν s ≤ ENNReal.ofReal (Real.exp ε) * μ s + ENNReal.ofReal δ)

/-- `lem:post-processing`: the same Markov kernel is applied on both inputs. -/
def PostProcessingStatement : Prop :=
  ∀ (X Y Z : Type) [MeasurableSpace Y] [MeasurableSpace Z],
  ∀ (adj : X → X → Prop) (M : X → Measure Y) (K : Kernel Y Z) (ε δ : ℝ),
    (∀ x, IsProbabilityMeasure (M x)) → IsMarkovKernel K → 0 ≤ ε → 0 ≤ δ →
    DP adj M ε δ → DP adj (fun x => (M x).bind K) ε δ

def laplaceMechanism {X : Type*} (k : ℕ) (f : X → Fin k → ℝ) (Δ ε : ℝ)
    (x : X) : Measure (Fin k → ℝ) :=
  if Δ = 0 then Measure.dirac (f x)
  else (Measure.pi (fun _ : Fin k => laplace (Δ / ε))).map (fun z => f x + z)

/-- `lem:laplace-mech`: use any sensitivity upper bound; a maximum need not exist.
The zero-sensitivity case is handled without a scale-zero Laplace law. -/
def LaplaceMechanismStatement : Prop :=
  ∀ (X : Type) (adj : X → X → Prop) (k : ℕ) (f : X → Fin k → ℝ) (Δ ε : ℝ),
    0 ≤ Δ → 0 < ε →
    (∀ x x', adj x x' → (∑ i, |f x i - f x' i|) ≤ Δ) →
    DP adj (laplaceMechanism k f Δ ε) ε 0

abbrev Sequential (Y : Type*) [MeasurableSpace Y] := ℕ → Kernel (List Y) Y
def sequentialLaw {Y : Type*} [MeasurableSpace Y] (P : Sequential Y) : ℕ → Measure (List Y)
  | 0 => Measure.dirac []
  | t + 1 => (sequentialLaw P t).bind fun h => (P t h).map (fun y => h ++ [y])

/-- `lem:basic-composition`: conditional guarantees hold for every fixed history. -/
def BasicCompositionStatement : Prop :=
  ∀ (X Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y],
  ∀ (adj : X → X → Prop) (P : X → Sequential Y) (k : ℕ) (ε δ : Fin k → ℝ),
    (∀ x t, IsMarkovKernel (P x t)) →
    (∀ t, 0 ≤ ε t ∧ 0 ≤ δ t) →
    (∀ t : Fin k, ∀ h, DP adj (fun x => P x t h) (ε t) (δ t)) →
    DP adj (fun x => sequentialLaw (P x) k) (∑ t, ε t) (∑ t, δ t)

def advancedEpsilon (k : ℕ) (ε₀ δ' : ℝ) : ℝ :=
  ε₀ * Real.sqrt (2 * k * Real.log (1 / δ')) + k * ε₀ * (Real.exp ε₀ - 1)

/-- `lem:advanced-composition`; symmetric adjacency supplies both privacy directions. -/
def AdvancedCompositionStatement : Prop :=
  ∀ (X Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y],
  ∀ (adj : X → X → Prop) (P : X → Sequential Y) (k : ℕ) (ε₀ δ₀ δ' : ℝ),
    Symmetric adj →
    (∀ x t, IsMarkovKernel (P x t)) →
    0 < ε₀ → 0 ≤ δ₀ → 0 < δ' → δ' < 1 →
    (∀ t < k, ∀ h, DP adj (fun x => P x t h) ε₀ δ₀) →
    DP adj (fun x => sequentialLaw (P x) k) (advancedEpsilon k ε₀ δ') (k * δ₀ + δ')

def CommonPrefix {Y : Type*} [MeasurableSpace Y] (P₀ P₁ : Sequential Y)
    (t : ℕ) (h : List Y) : Prop :=
  let μ₀ := sequentialLaw P₀ t
  let μ₁ := sequentialLaw P₁ t
  0 < μ₀.rnDeriv (μ₀ + μ₁) h ∧ 0 < μ₁.rnDeriv (μ₀ + μ₁) h

def successCharge {Y : Type*} (bottom : Y) (ell : ℕ → List Y → ℝ) (h : List Y) : ℝ :=
  ∑ t ∈ Finset.range h.length, if h[t]?.getD bottom = bottom then 0 else ell t (h.take t)

/-- `lem:pay-what-you-get`, for one neighboring pair. N must be measurable kernels.
The budget holds under the auxiliary process (not just under the actual process).
Applying this pairwise for every adjacent input gives the manuscript's DP conclusion. -/
def SuccessChargedStatement : Prop :=
  ∀ (Y : Type) [MeasurableSpace Y] [StandardBorelSpace Y] [Inhabited Y],
  ∀ (bottom : Y) (P₀ P₁ N₀ N₁ : Sequential Y) (k : ℕ)
    (ell : ℕ → List Y → ℝ) (ellStar L δ' δ'' : ℝ),
    (∀ t, IsMarkovKernel (P₀ t) ∧ IsMarkovKernel (P₁ t) ∧
      IsMarkovKernel (N₀ t) ∧ IsMarkovKernel (N₁ t)) →
    (∀ t, Measurable (ell t)) →
    0 ≤ ellStar → ellStar < 1 / 10 → 0 ≤ L → 0 ≤ δ' → 0 < δ'' → δ'' < 1 →
    (∀ t < k, ∀ h, CommonPrefix P₀ P₁ t h →
      0 ≤ ell t h ∧ ell t h ≤ ellStar ∧
      N₀ t h ≪ P₀ t h ∧ N₁ t h ≪ P₁ t h ∧
      TVClose (P₀ t h) (N₀ t h) δ' ∧ TVClose (P₁ t h) (N₁ t h) δ' ∧
      Indistinguishable (N₀ t h) (N₁ t h) (ell t h) 0) →
    (∀ᵐ h ∂sequentialLaw N₀ k, successCharge bottom ell h ≤ L) →
    (∀ᵐ h ∂sequentialLaw N₁ k, successCharge bottom ell h ≤ L) →
    let ε := 4 * L + 4 * ellStar * Real.log (1 / δ'')
    Indistinguishable (sequentialLaw P₀ k) (sequentialLaw P₁ k)
      ε (δ'' + (1 + Real.exp ε) * k * δ')

/-- Unnumbered finite-implementation bridge at the end of the main proof. -/
def TVPrivacyTransferStatement : Prop :=
  ∀ (X Y : Type) [MeasurableSpace Y],
  ∀ (adj : X → X → Prop) (M M' : X → Measure Y) (ε δ ν : ℝ),
    (∀ x, IsProbabilityMeasure (M x) ∧ IsProbabilityMeasure (M' x)) →
    0 ≤ ε → 0 ≤ δ → 0 ≤ ν → DP adj M ε δ →
    (∀ x, TVClose (M x) (M' x) ν) →
    DP adj M' ε (δ + (1 + Real.exp ε) * ν)

end DPCut
