import DPCut.Statements

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal MatrixOrder
namespace DPCut
attribute [local instance] Classical.propDecidable

/-- The algorithm's parameter range for the iteration bounds; unlike the main
utility theorem, these bounds do not require `delta, beta < 1/10`. -/
def Parameters.IterationValid (p : Parameters) : Prop :=
  0 < p.gamma ∧ p.gamma ≤ 1 / 4 ∧ 0 < p.epsilon ∧ p.epsilon ≤ 1 ∧
  0 < p.delta ∧ p.delta < 1 ∧ 0 < p.beta ∧ p.beta < 1

lemma Parameters.Valid.iterationValid {p : Parameters} (hp : p.Valid) :
    p.IterationValid := by
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  exact ⟨hg, hg1, he, he1, hd, by linarith, hb, by linarith⟩

def innerRoundLaw {n : ℕ} (p : Parameters) (cfg : RunConfig) (w a : Weights n) :
    Measure (ℝ × Option (Weights n × Weights n)) :=
  let wi := hadamard a w
  (laplace (1 / cfg.eps2)).bind fun noise =>
    let M := clipNoisyMass cfg.massCap (mass wi) noise cfg.tau2
    (innerLoop p cfg wi M cfg.T2 (initialEstimate M a)).map (fun result => (M, result))

/-- `lem:inner_round`: probability is joint over the mass estimate and inner trials;
it is not a conditional probability given the decision to continue. -/
def InnerRoundStatement (c : Constants) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (U : ℝ), 1 ≤ U → ∀ p : Parameters, p.IterationValid →
  ∀ (w a : Weights n), Bounded U w → IsMask a →
    let cfg := runConfig n U p c
    cfg.stop ≥ 10 * (cfg.B + cfg.tau2 / p.gamma) →
    HighProbability (innerRoundLaw p cfg w a) (cfg.T2 * cfg.betaGE + cfg.beta2)
      (fun result => cfg.stop < result.1 → result.2.isSome)

/-- Whether CutRelease reaches its stopping test within its allotted outer rounds. -/
def outerStopsLaw {n : ℕ} (p : Parameters) (cfg : RunConfig) (w : Weights n) :
    ℕ → Weights n → Measure Bool
  | 0, _ => Measure.dirac false
  | t + 1, a =>
    let wi := hadamard a w
    (laplace (1 / cfg.eps2)).bind fun noise =>
      let M := clipNoisyMass cfg.massCap (mass wi) noise cfg.tau2
      if a = 0 ∨ M ≤ cfg.stop then Measure.dirac true else
      (innerLoop p cfg wi M cfg.T2 (initialEstimate M a)).bind fun result =>
        match result with
        | none => outerStopsLaw p cfg w t a
        | some (_, r) => outerStopsLaw p cfg w t (residualUpdate a r)

/-- `lem:outer_round`, with the same horizon/parameter constants as Algorithm 1. -/
def OuterRoundStatement (c : Constants) : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (U : ℝ), 1 ≤ U → ∀ p : Parameters, p.IterationValid →
  ∀ w : Weights n, Bounded U w →
    let cfg := runConfig n U p c
    HighProbability (outerStopsLaw p cfg w cfg.T1 1)
      (cfg.T1 * cfg.T2 * cfg.betaGE + cfg.T1 * cfg.beta2) (fun stopped => stopped = true)

def potential {n : ℕ} (w h : Weights n) (M Mtilde : ℝ) : ℝ :=
  M * (normalizedKL w h M Mtilde).toReal

/-- Unnumbered potential decrease, eq. (diff_in_j_iterate) and the following calculation. -/
def MWProgressStatement : Prop :=
  ∀ (n : ℕ) (w h g : Weights n) (M Mtilde γ θ : ℝ),
    Nonnegative w → Nonnegative h → IsMask g → 0 < M → 0 < Mtilde →
    mass w = M → mass h = Mtilde → (∀ e, 0 < w e → 0 < h e) →
    0 < γ → γ ≤ 1 / 4 → (θ = 1 ∨ θ = -1) →
    θ * pairing (fun e => h e / Mtilde - w e / M) g ≥ γ / (4 * (1 + γ)) →
    potential w h M Mtilde - potential w (mwUpdate Mtilde θ (stepSize γ) h g) M Mtilde ≥
      γ ^ 2 * M / (64 * (1 + γ) ^ 2)

/-- The mass comparison requires averaging over all cuts; taking S=V gives zero. -/
def MassFromCutsStatement : Prop :=
  ∀ (n : ℕ) (w h : Weights n) (γ B : ℝ), Nonnegative w → Nonnegative h →
    0 ≤ γ → 0 ≤ B → AllCuts w h γ B → |mass w - mass h| ≤ γ * mass w + 2 * B

def ResidualContractionStatement : Prop :=
  ∀ (n : ℕ) (w h : Weights n) (a : Aggregate n) (γ B : ℝ),
    Nonnegative w → Nonnegative h → a.Partition → a.Accurate w h γ B → a.Accepts h →
    0 < γ → γ ≤ 1 / 4 → 0 ≤ B → 10 * B ≤ mass w → mass w ≤ mass h →
    mass (residualUpdate w a.residual) ≤ (19 / 20 : ℝ) * mass w

/-- Unnumbered numerical bridge in the main proof. Feasibility is indispensable. -/
def ObjectiveGapStatement : Prop :=
  ∀ (n : ℕ), 2 ≤ n → ∀ (lam μ : ℝ), 0 < lam → 0 < μ → μ ≤ 1 / 2 →
  ∀ (D : Weights n) (X : Mat n), X ∈ feasible n →
    optimum lam D - objective lam D X ≤ lam * μ ^ 2 / (2 * (n : ℝ) ^ 4) →
    let Xstar := optimizer lam D
    frobenius ((CFC.sqrt Xstar)⁻¹ * (Xstar - X) * (CFC.sqrt Xstar)⁻¹) ≤ μ

def ApproximateGaussianStatement : Prop :=
  ∀ (n k : ℕ), 0 < n → 0 < k → ∀ (X Xstar : Mat n), X.PosDef → Xstar.PosDef →
  ∀ μ : ℝ, 0 < μ → μ ≤ 1 / 2 →
    frobenius ((CFC.sqrt Xstar)⁻¹ * (X - Xstar) * (CFC.sqrt Xstar)⁻¹) ≤ μ →
    InformationTheory.klDiv (gaussianBatch X k) (gaussianBatch Xstar k) ≤
      ENNReal.ofReal (k * μ ^ 2 / 2)

end DPCut
