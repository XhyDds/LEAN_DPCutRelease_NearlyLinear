import DPCut.Theorem1

/-!
Cost semantics for the explicitly assumed real-arithmetic oracle model.
An exact log-det SDP solve is a primitive with a dimension-polynomial cost
contract. Finite vector blocks cost `100 (n+1)^2`, a Laplace draw costs 1,
and a dense Gaussian batch costs `100 (n+1)^3 (k+1)`. These are model
primitives, not a verified implementation of optimization or sampling.
Sequential cost takes a supremum over every possible intermediate value,
so the bound is a worst-case bound, not an expectation.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

/-- Explicit cost contract for the exact optimizer primitive. Its mathematical
semantics is `optimizer`; existence and uniqueness are already proved. -/
structure ExactSDPOracleCost where
  charge : ℕ → ℝ≥0∞
  coefficient : ℝ
  degree : ℕ
  coefficient_pos : 0 < coefficient
  charge_le : ∀ n, charge n ≤ ENNReal.ofReal (coefficient * (1 + (n : ℝ)) ^ degree)

structure CostedLaw (α : Type) [MeasurableSpace α] where
  law : Measure α
  cost : ℝ≥0∞

namespace CostedLaw
variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

def pure (x : α) : CostedLaw α := ⟨Measure.dirac x, 0⟩
def charge (c : ℝ≥0∞) (p : CostedLaw α) : CostedLaw α := ⟨p.law, c + p.cost⟩
def sample (μ : Measure α) (c : ℝ≥0∞) : CostedLaw α := ⟨μ, c⟩
def bind (p : CostedLaw α) (f : α → CostedLaw β) : CostedLaw β :=
  ⟨p.law.bind (fun x => (f x).law), p.cost + ⨆ x, (f x).cost⟩
def map (p : CostedLaw α) (f : α → β) (c : ℝ≥0∞) : CostedLaw β :=
  ⟨p.law.map f, p.cost + c⟩

@[simp] lemma pure_law (x : α) : (pure x).law = Measure.dirac x := rfl
@[simp] lemma charge_law (c : ℝ≥0∞) (p : CostedLaw α) : (charge c p).law = p.law := rfl
@[simp] lemma sample_law (μ : Measure α) (c : ℝ≥0∞) : (sample μ c).law = μ := rfl
@[simp] lemma bind_law (p : CostedLaw α) (f : α → CostedLaw β) :
    (p.bind f).law = p.law.bind (fun x => (f x).law) := rfl
@[simp] lemma map_law (p : CostedLaw α) (f : α → β) (c : ℝ≥0∞) :
    (p.map f c).law = p.law.map f := rfl

lemma bind_cost_le (p : CostedLaw α) (f : α → CostedLaw β) {a b : ℝ≥0∞}
    (hp : p.cost ≤ a) (hf : ∀ x, (f x).cost ≤ b) : (p.bind f).cost ≤ a + b :=
  add_le_add hp (iSup_le hf)

lemma charge_cost_le (c : ℝ≥0∞) (p : CostedLaw α) {b : ℝ≥0∞} (hp : p.cost ≤ b) :
    (charge c p).cost ≤ c + b := add_le_add_left hp c

end CostedLaw

def vectorBlockCost (n : ℕ) : ℝ≥0∞ := 100 * (n + 1) ^ 2
def gaussianBatchCost (n k : ℕ) : ℝ≥0∞ := vectorBlockCost n * (n + 1) * (k + 1)

def costedFindTrials {n : ℕ} (o : OracleConfig) (D r : Weights n) :
    ℕ → CostedLaw (Option (Weights n))
  | 0 => .pure none
  | t + 1 => (CostedLaw.sample (gaussianBatch (optimizer o.lam D) o.k) (gaussianBatchCost n o.k)).bind fun z =>
      (CostedLaw.sample (laplace (1 / o.eps1)) 1).bind fun noise =>
      .charge (vectorBlockCost n)
        (let g := clippedWitness z
         if o.tau1 ≤ pairing D g + noise ∧ 0 < activeMaximum r g
         then .pure (some (normalizeWitness r g)) else costedFindTrials o D r t)

def costedFindWitness {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (D r : Weights n) :
    CostedLaw (Option (Weights n)) :=
  .charge (vectorBlockCost n) (if r = 0 then .pure none
    else .charge (sdp.charge n) (costedFindTrials o D r o.K))

def costedAggregateLoop {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) : ℕ → Aggregate n → CostedLaw (Aggregate n)
  | 0, a => .pure a
  | t + 1, a => .charge (vectorBlockCost n) (if a.residual = 0 then .pure a else
      (costedFindWitness sdp o (plusDiscrepancy γ w h a.residual) a.residual).bind fun gp =>
      match gp with
      | some g => costedAggregateLoop sdp o γ w h t
          { a with plus := a.plus + g, residual := a.residual - g }
      | none =>
        (costedFindWitness sdp o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
        match gm with
        | some g => costedAggregateLoop sdp o γ w h t
            { a with minus := a.minus + g, residual := a.residual - g }
        | none => .pure a)

def costedAggregate {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) : CostedLaw (Aggregate n) :=
  costedAggregateLoop sdp o γ w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩

def costedInnerLoop {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) : ℕ → Weights n → CostedLaw (Option (Weights n × Weights n))
  | 0, _ => .pure none
  | t + 1, h => (costedAggregate sdp c.oracle p.gamma w h).bind fun a =>
      .charge (vectorBlockCost n) (if a.Accepts h then .pure (some (h, a.residual)) else
        let isOver := pairing h a.minus ≤ pairing h a.plus
        let θ : ℝ := if isOver then 1 else -1
        let g := if isOver then a.plus else a.minus
        costedInnerLoop sdp p c w M t (mwUpdate M θ c.eta h g))

def costedOuterLoop {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) : ℕ → Weights n → Weights n → CostedLaw (Weights n)
  | 0, _, out => .pure out
  | t + 1, a, out => (CostedLaw.sample (laplace (1 / c.eps2)) 1).bind fun noise =>
      .charge (vectorBlockCost n)
        (let wi := hadamard a w
         let M := clipNoisyMass c.massCap (mass wi) noise c.tau2
         if a = 0 ∨ M ≤ c.stop then .pure out else
         (costedInnerLoop sdp p c wi M c.T2 (initialEstimate M a)).bind fun r =>
         match r with
         | none => costedOuterLoop sdp p c w t a out
         | some (h, r) => costedOuterLoop sdp p c w t (residualUpdate a r) (out + hadamard h r))

def costedFullRelease {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (w : Weights n) :
    CostedLaw (Weights n) :=
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  let cfg := runConfig n U q outerUtilityConstants
  .charge (vectorBlockCost n)
    ((CostedLaw.sample (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w)
      (vectorBlockCost n + Fintype.card (Edge n))).bind fun y =>
      (costedOuterLoop sdp q cfg (clipWeights U w) cfg.T1 1 0).map (fun h => h + y) (vectorBlockCost n))

end DPCut
