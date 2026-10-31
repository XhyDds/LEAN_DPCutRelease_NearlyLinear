import DPCut.CappedReplacement
import DPCut.OracleReplacementCost

/-! Costs and exact kernel refinement for the capped program with a costed
witness implementation. No SDP optimizer is a parameter of these loops. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut.CappedReplacement
attribute [local instance] Classical.propDecidable

def costedInner {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) : ℕ → Weights n → CostedLaw (Option (Weights n × Weights n))
  | 0, _ => .pure none
  | t + 1, h => (OracleReplacement.costedAggregate W p.gamma w h).bind fun b =>
      .charge (cappedBlockCost n) (if b.Accepts h then .pure (some (h, b.residual))
        else costedInner W p c w a H t (cappedNext c a H h b))

def costedOuter {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (c : RunConfig)
    (w : Weights n) : ℕ → Weights n → Weights n → CostedLaw (Weights n)
  | 0, _, out => .pure out
  | t + 1, a, out => (CostedLaw.sample (laplace (1 / c.eps2)) 1).bind fun noise =>
      .charge (cappedBlockCost n)
        (let wi := hadamard a w
         let M := lowerBiasedMass (mass a) (mass wi) noise c.tau2
         if a = 0 ∨ M ≤ c.stop then .pure out else
         (costedInner W p c wi a M c.T2 (initialEstimate M a)).bind fun result =>
         match result with
         | none => costedOuter W p c w t a out
         | some (h, r) => costedOuter W p c w t (residualUpdate a r) (out + hadamard h r))

def costedRelease {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n))) (p : Parameters) (a w : Weights n) :
    CostedLaw (Weights n) := costedOuter W p (cappedRunConfig n p) w (cappedRunConfig n p).T1 a 0

lemma costedInner_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : OracleReplacement.WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D,r)) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    (costedInner W p c w a H t h).law = innerLoop K p c w a H t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [costedInner, innerLoop, CostedLaw.bind_law, OracleReplacement.costedAggregate_law W K hW]
    congr 1
    funext b
    simp only [CostedLaw.charge_law]
    split_ifs <;> simp [ih]

lemma costedOuter_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : OracleReplacement.WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D,r)) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuter W p c w t a out).law = outerLoop K p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    simp only [costedOuter, outerLoop, CostedLaw.bind_law, CostedLaw.sample_law]
    congr 1
    funext noise
    simp only [CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, costedInner_law W K hW]
      congr 1
      funext result
      cases result <;> simp [ih]

lemma costedRelease_law {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (K : OracleReplacement.WitnessKernel n) (hW : ∀ D r, (W D r).law = K (D,r)) (p : Parameters) (a w : Weights n) :
    (costedRelease W p a w).law = outerLoop K p (cappedRunConfig n p) w (cappedRunConfig n p).T1 a 0 :=
  costedOuter_law W K hW p _ w _ a 0

def innerCostBound (Wcost : ℝ≥0∞) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T2 * (OracleReplacement.aggregateCostBound Wcost n + cappedBlockCost n)

def costBound (Wcost : ℝ≥0∞) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  (cappedRunConfig n p).T1 * (1 + cappedBlockCost n + innerCostBound Wcost n (cappedRunConfig n p))

lemma costedInner_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    (costedInner W p c w a H t h).cost ≤ t * (OracleReplacement.aggregateCostBound Wcost n + cappedBlockCost n) := by
  let S := OracleReplacement.aggregateCostBound Wcost n + cappedBlockCost n
  induction t generalizing h with
  | zero => simp [costedInner, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ OracleReplacement.aggregateCostBound Wcost n + (cappedBlockCost n + t * S) := by
        apply CostedLaw.bind_cost_le _ _ (OracleReplacement.costedAggregate_cost W Wcost hW p.gamma w h)
        intro b
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · exact ih _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedOuter_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuter W p c w t a out).cost ≤ t * (1 + cappedBlockCost n + innerCostBound Wcost n c) := by
  let S := 1 + cappedBlockCost n + innerCostBound Wcost n c
  induction t generalizing a out with
  | zero => simp [costedOuter, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ 1 + (cappedBlockCost n + (innerCostBound Wcost n c + t * S)) := by
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (costedInner_cost W Wcost hW p c _ _ _ _ _)
          intro result
          cases result <;> exact ih _ _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedRelease_cost {n : ℕ} (W : Weights n → Weights n → CostedLaw (Option (Weights n)))
    (Wcost : ℝ≥0∞) (hW : ∀ D r, (W D r).cost ≤ Wcost) (p : Parameters) (a w : Weights n) :
    (costedRelease W p a w).cost ≤ costBound Wcost n p :=
  costedOuter_cost W Wcost hW p _ w _ a 0


end DPCut.CappedReplacement
