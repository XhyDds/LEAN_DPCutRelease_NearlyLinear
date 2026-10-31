import DPCut.CostedProgram

/-! Erasing costs gives exactly the release laws already proved private and accurate. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

lemma costedFindTrials_law {n : ℕ} (o : OracleConfig) (D r : Weights n) (t : ℕ) :
    (costedFindTrials o D r t).law = findTrials o D r t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [costedFindTrials, findTrials, CostedLaw.bind_law, CostedLaw.sample_law]
    congr 1
    funext z
    congr 1
    funext noise
    simp only [CostedLaw.charge_law]
    split_ifs <;> simp [ih]

lemma costedFindWitness_law {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (D r : Weights n) :
    (costedFindWitness sdp o D r).law = findWitness o D r := by
  simp only [costedFindWitness, findWitness, CostedLaw.charge_law]
  split_ifs <;> simp [costedFindTrials_law]

lemma costedAggregateLoop_law {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    (costedAggregateLoop sdp o γ w h t a).law = aggregateLoop o γ w h t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
    simp only [costedAggregateLoop, aggregateLoop, CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, costedFindWitness_law]
      congr 1
      funext gp
      cases gp with
      | some g => exact ih _
      | none =>
        simp only [CostedLaw.bind_law, costedFindWitness_law]
        congr 1
        funext gm
        cases gm <;> simp [ih]

lemma costedAggregate_law {n : ℕ} (sdp : ExactSDPOracleCost) (o : OracleConfig) (γ : ℝ)
    (w h : Weights n) : (costedAggregate sdp o γ w h).law = aggregateLaw o γ w h :=
  costedAggregateLoop_law sdp o γ w h _ _

lemma costedInnerLoop_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    (costedInnerLoop sdp p c w M t h).law = innerLoop p c w M t h := by
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    simp only [costedInnerLoop, innerLoop, CostedLaw.bind_law, costedAggregate_law]
    congr 1
    funext a
    simp only [CostedLaw.charge_law]
    split_ifs <;> simp [ih]

lemma costedOuterLoop_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    (costedOuterLoop sdp p c w t a out).law = outerLoop p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    simp only [costedOuterLoop, outerLoop, CostedLaw.bind_law, CostedLaw.sample_law]
    congr 1
    funext z
    simp only [CostedLaw.charge_law]
    split_ifs
    · rfl
    · simp only [CostedLaw.bind_law, costedInnerLoop_law]
      congr 1
      funext r
      cases r with
      | none => exact ih _ _
      | some pair => exact ih _ _

theorem costedFullRelease_law {n : ℕ} (sdp : ExactSDPOracleCost) (p : Parameters) (w : Weights n) :
    (costedFullRelease sdp p w).law = fullReleaseLaw p outerUtilityConstants w := by
  simp only [costedFullRelease, CostedLaw.charge_law, CostedLaw.bind_law,
    CostedLaw.sample_law, CostedLaw.map_law, costedOuterLoop_law]
  rfl

end DPCut
