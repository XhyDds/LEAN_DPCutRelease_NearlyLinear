import DPCut.CostedProgramLaw

/-! Worst-case costs, including all failure and fallback branches of the actual program. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace DPCut

def trialCostBound (n : ℕ) (o : OracleConfig) : ℝ≥0∞ :=
  gaussianBatchCost n o.k + 1 + vectorBlockCost n
def witnessCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (o : OracleConfig) : ℝ≥0∞ :=
  vectorBlockCost n + sdp.charge n + o.K * trialCostBound n o
def aggregateCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (o : OracleConfig) : ℝ≥0∞ :=
  Fintype.card (Edge n) * (vectorBlockCost n + 2 * witnessCostBound sdp n o)
def innerCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T2 * (aggregateCostBound sdp n c.oracle + vectorBlockCost n)
def outerCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (c : RunConfig) : ℝ≥0∞ :=
  c.T1 * (1 + vectorBlockCost n + innerCostBound sdp n c)
def fullCostBound (sdp : ExactSDPOracleCost) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  3 * vectorBlockCost n + Fintype.card (Edge n) +
    outerCostBound sdp n (runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants)

lemma costedFindTrials_cost {n : ℕ} (o : OracleConfig) (D r : Weights n) (t : ℕ) :
    (costedFindTrials o D r t).cost ≤ t * trialCostBound n o := by
  induction t with
  | zero => simp [costedFindTrials, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ gaussianBatchCost n o.k + (1 + (vectorBlockCost n + t * trialCostBound n o)) := by
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro z
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · exact ih
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, trialCostBound]; ring

lemma costedFindWitness_cost {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (D r : Weights n) :
    (costedFindWitness sdp o D r).cost ≤ witnessCostBound sdp n o := by
  unfold witnessCostBound
  rw [add_assoc]
  apply CostedLaw.charge_cost_le
  split_ifs
  · exact zero_le _
  · exact CostedLaw.charge_cost_le _ _ (costedFindTrials_cost o D r o.K)

lemma costedAggregateLoop_cost {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    (costedAggregateLoop sdp o γ w h t a).cost ≤
      t * (vectorBlockCost n + 2 * witnessCostBound sdp n o) := by
  let W := witnessCostBound sdp n o
  let S := vectorBlockCost n + 2 * W
  induction t generalizing a with
  | zero => simp [costedAggregateLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ vectorBlockCost n + (W + (W + t * S)) := by
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (costedFindWitness_cost sdp o _ _)
          intro gp
          cases gp with
          | some g => exact (ih _).trans (le_add_left le_rfl)
          | none =>
            apply CostedLaw.bind_cost_le _ _ (costedFindWitness_cost sdp o _ _)
            intro gm
            cases gm with
            | some g => exact ih _
            | none => exact zero_le _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S, W]; ring

lemma costedAggregate_cost {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) : (costedAggregate sdp o γ w h).cost ≤ aggregateCostBound sdp n o :=
  costedAggregateLoop_cost sdp o γ w h _ _

lemma costedInnerLoop_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    (costedInnerLoop sdp p c w M t h).cost ≤
      t * (aggregateCostBound sdp n c.oracle + vectorBlockCost n) := by
  let S := aggregateCostBound sdp n c.oracle + vectorBlockCost n
  induction t generalizing h with
  | zero => simp [costedInnerLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ aggregateCostBound sdp n c.oracle + (vectorBlockCost n + t * S) := by
        apply CostedLaw.bind_cost_le _ _ (costedAggregate_cost sdp c.oracle p.gamma w h)
        intro a
        apply CostedLaw.charge_cost_le
        split_ifs
        · exact zero_le _
        · exact ih _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

lemma costedOuterLoop_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuterLoop sdp p c w t a out).cost ≤
      t * (1 + vectorBlockCost n + innerCostBound sdp n c) := by
  let S := 1 + vectorBlockCost n + innerCostBound sdp n c
  induction t generalizing a out with
  | zero => simp [costedOuterLoop, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ 1 + (vectorBlockCost n + (innerCostBound sdp n c + t * S)) := by
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · apply CostedLaw.bind_cost_le _ _ (costedInnerLoop_cost sdp p c _ _ _ _)
          intro r
          cases r with
          | none => exact ih _ _
          | some pair => exact ih _ _
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one]; dsimp [S]; ring

theorem costedFullRelease_cost {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (w : Weights n) :
    (costedFullRelease sdp p w).cost ≤ fullCostBound sdp n p := by
  let cfg := runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants
  calc
    _ ≤ vectorBlockCost n + ((vectorBlockCost n + Fintype.card (Edge n)) +
        (outerCostBound sdp n cfg + vectorBlockCost n)) := by
      apply CostedLaw.charge_cost_le
      apply CostedLaw.bind_cost_le _ _ (le_refl _)
      intro y
      exact add_le_add_right (costedOuterLoop_cost sdp _ _ _ _ _ _) _
    _ = _ := by dsimp [fullCostBound, cfg]; ring

end DPCut
