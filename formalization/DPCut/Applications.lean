import DPCut.Statements
import DPCut.Privacy

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

instance {α : Type*} [Fintype α] : MeasurableSpace (Finset α) := ⊤

/-- Finite labelings encode partitions; empty labels and repeated encodings are harmless
because all objectives depend only on equality of labels. -/
abbrev Partition (n : ℕ) := Fin n → Fin n
def partitionQuery {n : ℕ} (π : Partition n) : Weights n :=
  fun e => if π e.val.1 = π e.val.2 then 0 else 1
def partitionCut {n : ℕ} (w : Weights n) (π : Partition n) : ℝ := pairing w (partitionQuery π)
def clusterCount {n : ℕ} (π : Partition n) : ℕ := (Finset.univ.image π).card
def ccCost {n : ℕ} (positive : Weights n) (π : Partition n) : ℝ :=
  ∑ e, if π e.val.1 = π e.val.2 then 1 - positive e else positive e
def ccOptimum {n : ℕ} (positive : Weights n) : ℝ := sInf (Set.range (ccCost positive))
def ccOptimumK {n : ℕ} (positive : Weights n) (k : ℕ) : ℝ :=
  sInf (ccCost positive '' {π | clusterCount π ≤ k})
def maxKOptimum {n : ℕ} (w : Weights n) (k : ℕ) : ℝ :=
  sSup (partitionCut w '' {π | clusterCount π ≤ k})
def constrainedOptimum {n : ℕ} (w : Weights n) (F : Set (Finset (Fin n))) : ℝ :=
  sInf (cut w '' F)
def Balanced {n : ℕ} (b : ℝ) (S : Finset (Fin n)) : Prop :=
  b * n ≤ S.card ∧ b * n ≤ n - (S.card : ℝ)
def expansion {n : ℕ} (w : Weights n) (S : Finset (Fin n)) : ℝ :=
  cut w S / min (S.card : ℝ) (n - (S.card : ℝ))
def uniformSparsity {n : ℕ} (w : Weights n) (S : Finset (Fin n)) : ℝ :=
  cut w S / ((S.card : ℝ) * (n - (S.card : ℝ)))
def CappedOn {n : ℕ} (D : Finset (Edge n)) (w : Weights n) : Prop :=
  Bounded 1 w ∧ ∀ e, e ∉ D → w e = 0

/-- A rooted binary hierarchy as a finite laminar family of leaf sets. -/
abbrev Hierarchy (n : ℕ) := Finset (Finset (Fin n))
def IsSplit {n : ℕ} (T : Hierarchy n) (A B C : Finset (Fin n)) : Prop :=
  A ∈ T ∧ B ∈ T ∧ C ∈ T ∧ B.Nonempty ∧ C.Nonempty ∧ Disjoint B C ∧ A = B ∪ C
def IsHierarchy {n : ℕ} (T : Hierarchy n) : Prop :=
  Finset.univ ∈ T ∧ ∅ ∉ T ∧ (∀ v, {v} ∈ T) ∧
  (∀ A ∈ T, ∀ B ∈ T, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A) ∧
  ∀ A ∈ T, 2 ≤ A.card → ∃ B C, IsSplit T A B C
def BalancedHierarchy {n : ℕ} (b : ℝ) (T : Hierarchy n) : Prop :=
  IsHierarchy T ∧ ∀ A B C, IsSplit T A B C →
    b * A.card ≤ B.card ∧ b * A.card ≤ C.card
def lcaSize {n : ℕ} (T : Hierarchy n) (e : Edge n) : ℕ :=
  sInf ((fun A : Finset (Fin n) => A.card) '' {A | A ∈ T ∧ e.val.1 ∈ A ∧ e.val.2 ∈ A})
def hcCost {n : ℕ} (w : Weights n) (T : Hierarchy n) : ℝ := ∑ e, w e * lcaSize T e
def hcOptimum {n : ℕ} (w : Weights n) : ℝ := sInf (hcCost w '' {T | IsHierarchy T})
def inducedExpansion {n : ℕ} (w : Weights n) (A S : Finset (Fin n)) : ℝ :=
  between w S (A \ S) / min (S.card : ℝ) ((A \ S).card : ℝ)
def BalancedWithin {n : ℕ} (b : ℝ) (A S : Finset (Fin n)) : Prop :=
  S ⊆ A ∧ b * A.card ≤ S.card ∧ b * A.card ≤ (A \ S).card
def RecursiveApproximation {n : ℕ} (w : Weights n) (b a : ℝ) (T : Hierarchy n) : Prop :=
  ∀ A B C, IsSplit T A B C →
    if 1 / b ≤ (A.card : ℝ) then
      inducedExpansion w A B ≤ a * sInf (inducedExpansion w A '' {R | BalancedWithin b A R})
    else B.card ≤ C.card + 1 ∧ C.card ≤ B.card + 1

/-- `lem:hc-bicriteria-recursion`, deterministic semantic form of the recursive algorithm. -/
def HCRecursionStatement : Prop :=
  ∀ b : ℝ, 0 < b → b ≤ 1 / 3 → ∃ C : ℝ, 0 < C ∧
    ∀ (b' a : ℝ), 0 < b' → b' ≤ 1 / 3 → 1 ≤ a →
    ∀ (n : ℕ), 2 ≤ n → ∀ (w : Weights n) (T : Hierarchy n), Nonnegative w →
      BalancedHierarchy b' T → RecursiveApproximation w b a T → hcCost w T ≤ C * a * hcOptimum w

/-- Exact hierarchy transfer, eq. (hc-uniform-transfer), before its depth bound. -/
def HCTransferStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (w h : Weights n) (T : Hierarchy n) (η A : ℝ),
    Nonnegative w → Nonnegative h → IsHierarchy T → 0 ≤ η → 0 ≤ A → AllCuts w h η A →
    |hcCost h T - hcCost w T| ≤ η * hcCost w T +
      A / 2 * (n + ∑ cluster ∈ T.filter (fun cluster => 2 ≤ cluster.card), (cluster.card : ℝ))

/-- `lem:capped-unit-release`, statistical part, with logarithmic exponent seven
and a universal positive coefficient independent of all inputs and parameters. -/
def CappedReleaseStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (D : Finset (Edge n)) (p : Parameters), p.Valid →
  ∃ M : Kernel (Weights n) (Weights n), IsMarkovKernel M ∧
    DP (fun w w' => CappedOn D w ∧ CappedOn D w' ∧ Adjacent w w') M p.epsilon p.delta ∧
    ∀ w, CappedOn D w → (∀ᵐ h ∂M w, CappedOn D h) ∧
      HighProbability (M w) p.beta (fun h => AllCuts w h p.gamma
        (C * mainError n p))

def IsDistribution {m : ℕ} (p : Fin m → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1
def finiteKL {m : ℕ} (p q : Fin m → ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (discreteMeasure p) (discreteMeasure q)

/-- `lem:pythagorean`, on the finite simplex used by the capped-release proof.
Existence of the minimizer is not smuggled in: its membership and minimality are hypotheses. -/
def KLPythagoreanStatement : Prop :=
  ∀ (m : ℕ) (K : Set (Fin m → ℝ)), IsClosed K → Convex ℝ K →
    (∀ p ∈ K, IsDistribution p) →
    ∀ (pbar p' pstar : Fin m → ℝ), IsDistribution pbar → (∀ i, 0 < pbar i) →
      p' ∈ K → (∀ q ∈ K, finiteKL p' pbar ≤ finiteKL q pbar) → pstar ∈ K →
      finiteKL pstar p' + finiteKL p' pbar ≤ finiteKL pstar pbar

/-- Random block coloring: eqs. (cc-random-block-cut), (max-k-cut-transfer). -/
def PartitionTransferStatement : Prop :=
  ∀ (n : ℕ) (w h : Weights n) (γ A : ℝ), Nonnegative w → Nonnegative h →
    0 ≤ γ → 0 ≤ A → AllCuts w h γ A → ∀ π : Partition n,
    |partitionCut h π - partitionCut w π| ≤ γ * partitionCut w π + 2 * A

/-- Exact quantitative part of `thm:private-constrained-cut`, conditional on the
specified release. Instantiating M by the main theorem gives A = C_A * mainError. -/
def ConstrainedCutStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (F F' : Set (Finset (Fin n))), F.Nonempty → F'.Nonempty →
  ∀ (η ε δ β ρ τ A : ℝ), 0 < η → η ≤ 1 / 4 → 0 < ε → ε ≤ 1 →
    0 < δ → δ < 1 / 10 → 0 < β → β < 1 / 10 → 1 ≤ ρ → 0 ≤ τ → τ < 1 → 0 ≤ A →
  ∀ (M : Kernel (Weights n) (Weights n)) (K : Kernel (Weights n) (Finset (Fin n))),
    IsMarkovKernel M → IsMarkovKernel K → GraphValued M → EdgeDP M ε δ →
    (∀ w, Nonnegative w → HighProbability (M w) β (fun h => AllCuts w h η A)) →
    (∀ h, Nonnegative h → HighProbability (K h) τ
      (fun S => S ∈ F' ∧ cut h S ≤ ρ * constrainedOptimum h F)) →
    EdgeDP (fun w => (M w).bind K) ε δ ∧ ∀ w, Nonnegative w →
      HighProbability ((M w).bind K) (β + τ)
        (fun S => S ∈ F' ∧ cut w S ≤ ρ * (1 + η) / (1 - η) * constrainedOptimum w F +
          (ρ + 1) / (1 - η) * A)

/-- Deterministic transfer used by `thm:private-max-k-cut`. -/
def MaxKTransferStatement : Prop :=
  ∀ (n k : ℕ), 2 ≤ n → 2 ≤ k → ∀ (w h : Weights n) (η A ρ : ℝ) (π : Partition n),
    Nonnegative w → Nonnegative h → 0 ≤ η → η < 1 → 0 ≤ A → 0 ≤ ρ → ρ ≤ 1 →
    AllCuts w h η A → clusterCount π ≤ k → ρ * maxKOptimum h k ≤ partitionCut h π →
    ρ * (1 - η) / (1 + η) * maxKOptimum w k - 2 * (ρ + 1) / (1 + η) * A ≤ partitionCut w π

/-- Formal content of `rem:maxcut-tightness`, an additional theorem presented as a remark. -/
def MaxCutLowerBoundStatement : Prop :=
  ∀ (n : ℕ), 8 ≤ n → ∀ (ε δ β ρ B : ℝ),
    0 ≤ ε → ε ≤ 1 → 0 ≤ δ → δ ≤ 1 / 100 → 0 ≤ β → β ≤ 1 / 100 →
    (868 / 1000 : ℝ) ≤ ρ → ρ ≤ 1 → 0 ≤ B →
  ∀ M : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel M →
    DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') M ε δ →
    (∀ w, IsUnweighted w → HighProbability (M w) β
      (fun S => ρ * sSup (Set.range (cut w)) - B ≤ cut w S)) →
    ((n / 8 : ℕ) : ℝ) / 100 ≤ B

/-! The following targets make the paper's soft-O and "with high probability"
conventions explicit: C*n*(log n)^d and failure at most Cfail/n^2. These are
statistical statements; the external algorithms' efficiency remains a separate dependency. -/

/-- Error constants are explicit so each application can state their uniformity. -/
def PrivateCCGuarantee (C Cfail ε ratio : ℝ) (exponent : ℕ) (clusters : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ M : Kernel (Weights n) (Partition n), IsMarkovKernel M ∧
    DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') M ε ((n : ℝ)⁻¹ ^ 10) ∧
    ∀ w, IsUnweighted w → HighProbability (M w) (Cfail / (n : ℝ) ^ 2)
      (fun π => clusterCount π ≤ clusters n ∧
        ccCost w π ≤ ratio * ccOptimumK w (clusters n) + C * n * Real.log n ^ exponent)

/-- `cor:cc-intro`, statistical content with the convention just stated. -/
def CorrelationClusteringStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C Cfail : ℝ, ∃ exponent : ℕ,
    0 < C ∧ 0 < Cfail ∧ PrivateCCGuarantee C Cfail ε (1387 / 1000) exponent id

/-- `thm:cc-black-box-reduction`: error constants are independent of the source
algorithm and its success probability. -/
def CCBlackBoxStatement : Prop :=
  ∀ (ρ ξ ε : ℝ), 1 ≤ ρ → 0 < ξ → 0 < ε → ∃ C Cfail : ℝ, ∃ exponent : ℕ,
    0 < C ∧ 0 < Cfail ∧ ∀ p₀ : ℝ, 0 < p₀ →
  ∀ algorithm : (n : ℕ) → Kernel (Weights n) (Partition n),
    (∀ n, IsMarkovKernel (algorithm n)) →
    (∀ (n : ℕ), 2 ≤ n → ∀ w, IsUnweighted w →
      HighProbability (algorithm n w) (1 - p₀) (fun π => ccCost w π ≤ ρ * ccOptimum w)) →
    PrivateCCGuarantee C Cfail ε (ρ + ξ) exponent id

/-- `cor:cc-fixed-k`: error constants depend only on xi and epsilon, not on k. -/
def FixedKCorrelationClusteringStatement : Prop :=
  ∀ (ξ ε : ℝ), 0 < ξ → 0 < ε → ∃ C Cfail : ℝ, ∃ exponent : ℕ,
    0 < C ∧ 0 < Cfail ∧ ∀ k : ℕ, 2 ≤ k →
      PrivateCCGuarantee C Cfail ε (1 + ξ) exponent (fun _ => k)

def PrivateMaxKGuarantee (C Cfail ε ratio : ℝ) (exponent k : ℕ) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∃ M : Kernel (Weights n) (Partition n), IsMarkovKernel M ∧
    EdgeDP M ε ((n : ℝ)⁻¹ ^ 10) ∧ ∀ w, Nonnegative w →
      HighProbability (M w) (Cfail / (n : ℝ) ^ 2) (fun π => clusterCount π ≤ k ∧
        ratio * maxKOptimum w k - C * n * Real.log n ^ exponent ≤ partitionCut w π)

/-- `thm:private-max-k-cut`, statistical content. Constants precede k to record
the claimed independence of the additive term from the number of clusters. -/
def PrivateMaxKStatement : Prop :=
  ∀ (ξ ε : ℝ), 0 < ξ → 0 < ε → ∃ C Cfail : ℝ, ∃ exponent : ℕ,
    0 < C ∧ 0 < Cfail ∧ ∀ (k : ℕ), 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
    ∀ algorithm : (n : ℕ) → Kernel (Weights n) (Partition n),
      (∀ n, IsMarkovKernel (algorithm n)) →
      (∀ (n : ℕ), 2 ≤ n → ∀ w, Nonnegative w →
        (∀ᵐ π ∂algorithm n w, clusterCount π ≤ k) ∧
        ρ * maxKOptimum w k ≤ ∫ π, partitionCut w π ∂algorithm n w) →
      PrivateMaxKGuarantee C Cfail ε (ρ - ξ) exponent k

/-- `cor:maxcut-intro`, a specialization of the preceding target. -/
def PrivateMaxCutStatement : Prop :=
  ∀ (ξ ε : ℝ), 0 < ξ → 0 < ε → ∃ C Cfail : ℝ, ∃ exponent : ℕ,
    0 < C ∧ 0 < Cfail ∧ PrivateMaxKGuarantee C Cfail ε (878 / 1000 - ξ) exponent 2

/-- `thm:private-hierarchical-clustering`, statistical content. A_eta is evaluated
with delta=beta=n^-10 and 0 < epsilon ≤ 1, as in the paper.
Cadd may depend on eta; b' and the ratio constant are universal. -/
def PrivateHierarchyStatement : Prop :=
  ∃ b' Cratio CA Cfail : ℝ, 0 < b' ∧ b' ≤ 1 / 3 ∧ 0 < Cratio ∧ 0 < CA ∧ 0 < Cfail ∧
    ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∃ Cadd : ℝ, 0 < Cadd ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (n : ℕ), 2 ≤ n →
    ∃ M : Kernel (Weights n) (Hierarchy n), IsMarkovKernel M ∧ EdgeDP M ε ((n : ℝ)⁻¹ ^ 10) ∧
      ∀ w, Nonnegative w → HighProbability (M w) (Cfail / (n : ℝ) ^ 2)
        (fun T => BalancedHierarchy b' T ∧ hcCost w T ≤
          Cratio * Real.sqrt (Real.log n) * hcOptimum w +
          Cadd * (CA * mainError n ⟨η, ε, (n : ℝ)⁻¹ ^ 10, (n : ℝ)⁻¹ ^ 10⟩) *
            n * (Real.log n) ^ (3 / 2 : ℝ))

end DPCut
