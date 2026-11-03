import DPCut.ApproxSDPOracle
import DPCut.OracleReplacementCost
import DPCut.VerifiedGaussianSampling

/-! One approximate solve followed by the Gaussian/Laplace attempts of FindWitness. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DPCut.ApproxSDPCosted
attribute [local instance] Classical.propDecidable

def trials {n : ℕ} (o : OracleConfig) (X : Mat n) (D r : Weights n) :
    ℕ → CostedLaw (Option (Weights n))
  | 0 => .pure none
  | t + 1 => (verifiedGaussianBatch X o.k).bind fun z =>
      (CostedLaw.sample (laplace (1 / o.eps1)) 1).bind fun noise =>
      .charge (vectorBlockCost n)
        (let g := clippedWitness z
         if o.tau1 ≤ pairing D g + noise ∧ 0 < activeMaximum r g
         then .pure (some (normalizeWitness r g)) else trials o X D r t)

def witness {n : ℕ} (sdp : ApproxSDPOracle) (μ : ℝ) (o : OracleConfig) (D r : Weights n) :
    CostedLaw (Option (Weights n)) :=
  .charge (vectorBlockCost n) (if r = 0 then .pure none
    else .charge (sdp.charge n μ) (trials o (sdp.solve n o.lam μ D) D r o.K))

theorem trials_law {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (X : Mat n) (hX : X.PosDef) (D r : Weights n) (t : ℕ) :
    (trials o X D r t).law = repeatUntil (approximateTrialLaw o D X) (acceptTrial o r) t := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [repeatUntil, approximateTrialLaw, bind_map_eq (scoreShear D).measurable
      (measurable_repeat_continuation _ (measurable_acceptTrial_fixed o r))]
    change (trials o X D r (t + 1)).law =
      ((gaussianBatch X o.k).prod (laplace (1 / o.eps1))).bind
        (fun p => (acceptTrial o r (scoreShear D p)).elim
          (repeatUntil (approximateTrialLaw o D X) (acceptTrial o r) t) (fun y => Measure.dirac (some y)))
    rw [bind_prod_eq (gaussianBatch X o.k) (laplace (1 / o.eps1))
      (show Measurable (fun p : TrialSample n o.k =>
      (acceptTrial o r (scoreShear D p)).elim (repeatUntil (approximateTrialLaw o D X) (acceptTrial o r) t)
        (fun y => Measure.dirac (some y))) from (measurable_repeat_continuation _
          (measurable_acceptTrial_fixed o r)).comp (scoreShear D).measurable)]
    simp only [trials, CostedLaw.bind_law, CostedLaw.sample_law, CostedLaw.charge_law,
      verifiedGaussianBatch_law X hX]
    congr 1
    funext z
    congr 1
    funext noise
    dsimp [acceptTrial, scoreShear]
    split_ifs
    · rfl
    · exact ih

lemma witness_law {n : ℕ} (sdp : ApproxSDPOracle) (μ : ℝ) (o : OracleConfig)
    (he : 0 < o.eps1) (D r : Weights n) (hX : (sdp.solve n o.lam μ D).PosDef) :
    (witness sdp μ o D r).law = approximateFindWitness o D r (sdp.solve n o.lam μ D) := by
  simp only [witness, approximateFindWitness, CostedLaw.charge_law]
  split_ifs
  · rfl
  · exact trials_law o he _ hX _ _ _

def witnessBound (sdp : ApproxSDPOracle) (μ : ℝ) (n : ℕ) (o : OracleConfig) : ℝ≥0∞ :=
  vectorBlockCost n + sdp.charge n μ + o.K * trialCostBound n o

lemma trials_cost {n : ℕ} (o : OracleConfig) (X : Mat n) (D r : Weights n) (t : ℕ) :
    (trials o X D r t).cost ≤ t * trialCostBound n o := by
  induction t with
  | zero => simp [trials, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ gaussianBatchCost n o.k + (1 + (vectorBlockCost n + t * trialCostBound n o)) := by
        apply CostedLaw.bind_cost_le _ _ (verifiedGaussianBatch_cost X o.k)
        intro z
        apply CostedLaw.bind_cost_le _ _ (le_refl _)
        intro noise
        apply CostedLaw.charge_cost_le
        dsimp only
        split_ifs
        · exact zero_le _
        · exact ih
      _ = _ := by simp only [Nat.cast_add, Nat.cast_one, trialCostBound]; ring

lemma witness_cost {n : ℕ} (sdp : ApproxSDPOracle) (μ : ℝ) (o : OracleConfig) (D r : Weights n) :
    (witness sdp μ o D r).cost ≤ witnessBound sdp μ n o := by
  unfold witnessBound
  rw [add_assoc]
  apply CostedLaw.charge_cost_le
  split_ifs
  · exact zero_le _
  · exact CostedLaw.charge_cost_le _ _ (trials_cost o (sdp.solve n o.lam μ D) D r o.K)


end DPCut.ApproxSDPCosted
