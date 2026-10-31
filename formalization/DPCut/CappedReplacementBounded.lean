import DPCut.CappedReplacement

/-! The objective guard is inactive in the ideal capped execution, including
outside accuracy events. Only bounded input weights are needed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.CappedReplacement
attribute [local instance] Classical.propDecidable
open OracleReplacement (WitnessKernel)

variable {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
  (ho : OraclePrivacyBounds n c.oracle) (K : WitnessKernel n)
  {B : ℝ} (hγ : 0 ≤ p.gamma)
  (hB : (2 + p.gamma) * Fintype.card (Edge n) ≤ B)
  (hK : ∀ D r, l1 D ≤ B → K (D,r) = findWitness c.oracle D r)

lemma mask_mass_le {a : Weights n} (ha : IsMask a) :
    mass a ≤ Fintype.card (Edge n) := by
  calc
    _ ≤ ∑ _ : Edge n, (1:ℝ) := Finset.sum_le_sum (fun e _ => (ha e).2)
    _ = _ := by simp

include hn ho hγ hB hK in
lemma innerLoop_bounded_eq {w a : Weights n} (hw : Bounded 1 w) (ha : IsMask a)
    {H : ℝ} (hH : 0 < H) (hHa : H ≤ mass a) (t : ℕ) (h : Weights n)
    (hh : CappedEstimateValid a H h) :
    innerLoop K p c w a H t h = cappedInnerLoop p c w a H t h := by
  have hbound : (Fintype.card (Edge n):ℝ) + (1+p.gamma)*Fintype.card (Edge n)*1 ≤ B := by
    nlinarith
  induction t generalizing h with
  | zero => rfl
  | succ t ih =>
    have hag : OracleReplacement.aggregateLaw K p.gamma w h = aggregateLaw c.oracle p.gamma w h :=
      OracleReplacement.aggregateLoop_bounded_eq hn c.oracle (by linarith [ho.lam_lower]) ho.eps_pos
        K hγ hbound hK hw hh.1 (hh.2.1.le.trans (hHa.trans (mask_mass_le ha))) _ _
        (by intro e; simp)
    rw [innerLoop, cappedInnerLoop, hag]
    congr 1
    funext b
    split_ifs
    · rfl
    · exact ih _ (cappedNext_valid c (fun e => (ha e).1) hH hHa hh b)

include hn ho hγ hB hK in
lemma outerLoop_bounded_eq (hstop : 0 ≤ c.stop) {w : Weights n} (hw : Bounded 1 w)
    (t : ℕ) (a out : Weights n) (ha : IsMask a) :
    outerLoop K p c w t a out = cappedOuterLoop p c w t a out := by
  induction t generalizing a out with
  | zero => rfl
  | succ t ih =>
    rw [outerLoop, cappedOuterLoop]
    congr 1
    funext noise
    dsimp only
    split_ifs with hdone
    · rfl
    · let H := lowerBiasedMass (mass a) (mass (hadamard a w)) noise c.tau2
      have hH : 0 < H := hstop.trans_lt (lt_of_not_ge (fun h => hdone (Or.inr h)))
      have hHa : H ≤ mass a := (lowerBiasedMass_bounds
        (show 0 ≤ mass a from Finset.sum_nonneg fun e _ => (ha e).1)).2
      have hwi : Bounded 1 (hadamard a w) := fun e =>
        ⟨mul_nonneg (ha e).1 (hw e).1,
          (mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2⟩
      rw [innerLoop_bounded_eq hn p c ho K hγ hB hK hwi ha hH hHa _ _
        (initialEstimate_capped_valid (fun e => (ha e).1) hH hHa)]
      apply Measure.bind_congr_right
      filter_upwards [cappedInnerLoop_supported hn p c ho (hadamard a w) a H c.T2 (initialEstimate H a)] with r hr
      cases r with
      | none => exact ih a out ha
      | some pair => exact ih _ _ (residualUpdate_isMask ha hr)

end DPCut.CappedReplacement
