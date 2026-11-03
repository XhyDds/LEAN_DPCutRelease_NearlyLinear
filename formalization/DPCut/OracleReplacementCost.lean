import DPCut.OracleReplacementLaw
import DPCut.CostedProgramBounds

/-! Assigned real-arithmetic block costs with a replaceable, costed witness implementation. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut.OracleReplacement
attribute [local instance] Classical.propDecidable

def costedAggregateLoop {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (γ : ℝ)
    (w h : Weights n) : ℕ → Aggregate n → CostedLaw (Aggregate n)
  | 0, a => .pure a
  | t + 1, a => .charge (vectorBlockCost n) (if a.residual = 0 then .pure a else
      (W (plusDiscrepancy γ w h a.residual) a.residual).bind fun gp =>
      match gp with
      | some g => costedAggregateLoop W γ w h t
          { a with plus := a.plus + g, residual := a.residual - g }
      | none =>
        (W (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
        match gm with
        | some g => costedAggregateLoop W γ w h t
            { a with minus := a.minus + g, residual := a.residual - g }
        | none => .pure a)

def costedAggregate {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (γ : ℝ)
    (w h : Weights n) : CostedLaw (Aggregate n) :=
  costedAggregateLoop W γ w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩

def costedInnerLoop {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) : ℕ → Weights n → CostedLaw (Option (Weights n × Weights n))
  | 0, _ => .pure none
  | t + 1, h => (costedAggregate W p.gamma w h).bind fun a =>
      .charge (vectorBlockCost n) (if a.Accepts h then .pure (some (h, a.residual)) else
        let isOver := pairing h a.minus ≤ pairing h a.plus
        let θ : ℝ := if isOver then 1 else -1
        let g := if isOver then a.plus else a.minus
        costedInnerLoop W p c w M t (mwUpdate M θ c.eta h g))

def costedOuterLoop {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (c : RunConfig)
    (w : Weights n) : ℕ → Weights n → Weights n → CostedLaw (Weights n)
  | 0, _, out => .pure out
  | t + 1, a, out => (CostedLaw.sample (laplace (1 / c.eps2)) 1).bind fun noise =>
      .charge (vectorBlockCost n)
        (let wi := hadamard a w
         let M := clipNoisyMass c.massCap (mass wi) noise c.tau2
         if a = 0 ∨ M ≤ c.stop then .pure out else
         (costedInnerLoop W p c wi M c.T2 (initialEstimate M a)).bind fun r =>
         match r with
         | none => costedOuterLoop W p c w t a out
         | some (h, r) => costedOuterLoop W p c w t (residualUpdate a r) (out + hadamard h r))

def costedFullRelease {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (w : Weights n) :
    CostedLaw (Weights n) :=
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  let cfg := runConfig n U q outerUtilityConstants
  .charge (vectorBlockCost n)
    ((CostedLaw.sample (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w)
      (vectorBlockCost n + Fintype.card (Edge n))).bind fun y =>
      (costedOuterLoop W q cfg (clipWeights U w) cfg.T1 1 0).map (fun h => h + y) (vectorBlockCost n))

lemma costedAggregateLoop_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D, r)) (γ : ℝ)
    (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    (costedAggregateLoop W γ w h t a).law = aggregateLoop K γ w h t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [costedAggregateLoop, aggregateLoop, CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, hW]
      congr 1
      funext gp
      cases gp with
      | some g => exact ih _
      | none =>
        simp only [CostedLaw.bind_law, hW]
        congr 1
        funext gm
        cases gm <;> simp [ih, aggregateMinusStep]

lemma costedAggregate_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D, r)) (γ : ℝ)
    (w h : Weights n) : (costedAggregate W γ w h).law = aggregateLaw K γ w h :=
  costedAggregateLoop_law W K hW γ w h _ _

lemma costedInnerLoop_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D, r)) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    (costedInnerLoop W p c w M t h).law = innerLoop K p c w M t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [costedInnerLoop, innerLoop, CostedLaw.bind_law, costedAggregate_law W K hW]
    congr 1
    funext a
    simp only [CostedLaw.charge_law]
    dsimp [innerNext]
    split_ifs <;> simp [ih]

lemma costedOuterLoop_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D, r)) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuterLoop W p c w t a out).law = outerLoop K p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    simp only [costedOuterLoop, outerLoop, CostedLaw.bind_law, CostedLaw.sample_law]
    congr 1
    funext z
    simp only [CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, costedInnerLoop_law W K hW]
      congr 1
      funext r
      cases r with
      | none => exact ih _ _
      | some pair => exact ih _ _

theorem costedFullRelease_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D, r)) (p : Parameters) (w : Weights n) :
    (costedFullRelease W p w).law = fullRelease K p w := by
  simp only [costedFullRelease, CostedLaw.charge_law, CostedLaw.bind_law,
    CostedLaw.sample_law, CostedLaw.map_law, costedOuterLoop_law W K hW]
  rfl

def aggregateCostBound (Wcost : ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  Fintype.card (Edge n) * (vectorBlockCost n + 2 * Wcost)
def innerCostBound (Wcost : ℝ≥0∞) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T2 * (aggregateCostBound Wcost n + vectorBlockCost n)
def outerCostBound (Wcost : ℝ≥0∞) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T1 * (1 + vectorBlockCost n + innerCostBound Wcost n c)
def fullCostBound (Wcost : ℝ≥0∞) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  3 * vectorBlockCost n + Fintype.card (Edge n) +
    outerCostBound Wcost n (runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants)

lemma costedAggregateLoop_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (γ : ℝ)
    (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    (costedAggregateLoop W γ w h t a).cost ≤
      t * (vectorBlockCost n + 2 * Wcost) := by
  let S := vectorBlockCost n + 2 * Wcost
  induction t generalizing a with
  | zero => simp [costedAggregateLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ vectorBlockCost n + (Wcost + (Wcost + t * S)) := by
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (hW _ _)
          intro gp
          cases gp with
          | some g => exact (ih _).trans (le_add_left le_rfl)
          | none =>
            apply CostedLaw.bind_cost_le _ _ (hW _ _)
            intro gm
            cases gm with
            | some g => exact ih _
            | none => exact zero_le _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedAggregate_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (γ : ℝ)
    (w h : Weights n) : (costedAggregate W γ w h).cost ≤ aggregateCostBound Wcost n :=
  costedAggregateLoop_cost W Wcost hW γ w h _ _

lemma costedInnerLoop_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    (costedInnerLoop W p c w M t h).cost ≤
      t * (aggregateCostBound Wcost n + vectorBlockCost n) := by
  let S := aggregateCostBound Wcost n + vectorBlockCost n
  induction t generalizing h with
  | zero => simp [costedInnerLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ aggregateCostBound Wcost n + (vectorBlockCost n + t * S) := by
        apply CostedLaw.bind_cost_le _ _ (costedAggregate_cost W Wcost hW p.gamma w h)
        intro a
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · exact ih _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedOuterLoop_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuterLoop W p c w t a out).cost ≤
      t * (1 + vectorBlockCost n + innerCostBound Wcost n c) := by
  let S := 1 + vectorBlockCost n + innerCostBound Wcost n c
  induction t generalizing a out with
  | zero => simp [costedOuterLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ 1 + (vectorBlockCost n + (innerCostBound Wcost n c + t * S)) := by
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (costedInnerLoop_cost W Wcost hW p c _ _ _ _)
          intro r
          cases r with
          | none => exact ih _ _
          | some pair => exact ih _ _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

theorem costedFullRelease_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (w : Weights n) :
    (costedFullRelease W p w).cost ≤ fullCostBound Wcost n p := by
  let cfg := runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants
  calc
    _ ≤ vectorBlockCost n + ((vectorBlockCost n + Fintype.card (Edge n)) +
        (outerCostBound Wcost n cfg + vectorBlockCost n)) := by
      apply CostedLaw.charge_cost_le
      apply CostedLaw.bind_cost_le _ _ (le_refl _)
      intro y
      exact add_le_add_right (costedOuterLoop_cost W Wcost hW _ _ _ _ _ _) _
    _ = _ := by dsimp [fullCostBound, cfg]; ring

end DPCut.OracleReplacement
