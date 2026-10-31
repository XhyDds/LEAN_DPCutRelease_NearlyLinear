import DPCut.OracleCalibration
import DPCut.RepeatUntil

/-! The actual finite-trial witness oracle and its conditioned auxiliary law. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

def acceptTrial {n : ℕ} (o : OracleConfig) (r : Weights n)
    (p : TrialSample n o.k) : Option (Weights n) :=
  if o.tau1 ≤ p.2 ∧ 0 < activeMaximum r (clippedWitness p.1)
  then some (normalizeWitness r (clippedWitness p.1)) else none

lemma measurable_acceptTrial {n : ℕ} (o : OracleConfig) :
    Measurable (fun p : Weights n × TrialSample n o.k => acceptTrial o p.1 p.2) := by
  have hg : Measurable (fun p : Weights n × TrialSample n o.k => clippedWitness p.2.1) :=
    (measurable_pi_lambda _ measurable_clippedWitness).comp (measurable_fst.comp measurable_snd)
  have hm := measurable_activeMaximum.comp (measurable_fst.prodMk hg)
  exact Measurable.ite
    ((measurableSet_le measurable_const (measurable_snd.comp measurable_snd)).inter
      (measurableSet_lt measurable_const hm))
    (measurable_some.comp (measurable_normalizeWitness.comp (measurable_fst.prodMk hg)))
    measurable_const

lemma measurable_acceptTrial_fixed {n : ℕ} (o : OracleConfig) (r : Weights n) :
    Measurable (acceptTrial o r) :=
  (measurable_acceptTrial o).comp measurable_prodMk_left

theorem findTrials_eq_repeatUntil {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D r : Weights n) (t : ℕ) :
    findTrials o D r t = repeatUntil (trialLaw o D) (acceptTrial o r) t := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [repeatUntil, trialLaw, bind_map_eq (scoreShear D).measurable
      (measurable_repeat_continuation _ (measurable_acceptTrial_fixed o r))]
    change findTrials o D r (t + 1) =
      ((gaussianBatch (optimizer o.lam D) o.k).prod (laplace (1 / o.eps1))).bind
        (fun p => (acceptTrial o r (scoreShear D p)).elim
          (repeatUntil (trialLaw o D) (acceptTrial o r) t) (fun y => Measure.dirac (some y)))
    rw [bind_prod_eq (gaussianBatch (optimizer o.lam D) o.k) (laplace (1 / o.eps1))
      (show Measurable (fun p : TrialSample n o.k =>
      (acceptTrial o r (scoreShear D p)).elim (repeatUntil (trialLaw o D) (acceptTrial o r) t)
        (fun y => Measure.dirac (some y))) from (measurable_repeat_continuation _
          (measurable_acceptTrial_fixed o r)).comp (scoreShear D).measurable)]
    simp only [findTrials, ih]
    congr 1
    funext z
    congr 1
    funext noise
    dsimp [acceptTrial, scoreShear]
    split_ifs <;> rfl

lemma findTrials_probability {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D r : Weights n) (t : ℕ) : IsProbabilityMeasure (findTrials o D r t) := by
  letI := trialLaw_probability o he D
  rw [findTrials_eq_repeatUntil o he]
  exact repeatUntil_probability _ (measurable_acceptTrial_fixed o r) t

lemma findWitness_probability {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D r : Weights n) : IsProbabilityMeasure (findWitness o D r) := by
  unfold findWitness
  split_ifs
  · infer_instance
  · exact findTrials_probability o he D r o.K

def auxiliaryFindWitness {n : ℕ} (o : OracleConfig) (D D' ζ r : Weights n) :
    Measure (Option (Weights n)) :=
  if r = 0 then Measure.dirac none else
    repeatUntil ((trialLaw o D)[|trialGood o D D' ζ r]) (acceptTrial o r) o.K

theorem findWitness_auxiliary {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (D D' ζ r : Weights n) (hr : IsMask r)
    (hζ : l1 ζ ≤ 1) (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    let N := auxiliaryFindWitness o D D' ζ r
    let N' := auxiliaryFindWitness o D' D ζ r
    IsProbabilityMeasure N ∧ IsProbabilityMeasure N' ∧
    N ≪ findWitness o D r ∧ N' ≪ findWitness o D' r ∧
    TVClose (findWitness o D r) N (2 * o.K * o.delta1) ∧
    TVClose (findWitness o D' r) N' (2 * o.K * o.delta1) ∧
    Indistinguishable N N'
      (10 * o.K * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) 0 := by
  dsimp
  have heps := ho.eps_pos
  have hdelta := ho.delta_pos
  have hW := (oracleSensitivity_bounds hn hr ζ (optimizer_isOptimizer hn o.lam D).1
    (optimizer_isOptimizer hn o.lam D').1).1
  have he : 0 ≤ 10 * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D') :=
    mul_nonneg (by positivity) hW
  by_cases hr0 : r = 0
  · simp only [auxiliaryFindWitness, findWitness, if_pos hr0]
    exact ⟨inferInstance, inferInstance, Measure.AbsolutelyContinuous.rfl,
      Measure.AbsolutelyContinuous.rfl, TVClose.refl _ (by positivity),
      TVClose.refl _ (by positivity), Indistinguishable.of_eq rfl
        (by nlinarith [mul_nonneg (Nat.cast_nonneg o.K) he]) le_rfl⟩
  obtain ⟨h0, h1, hac0, hac1, htv0, htv1, hp⟩ :=
    calibrated_trial_auxiliary hn o ho D D' ζ r hr hζ hξ
  letI := h0
  letI := h1
  letI := trialLaw_probability o ho.eps_pos D
  letI := trialLaw_probability o ho.eps_pos D'
  simp only [auxiliaryFindWitness, findWitness, if_neg hr0, trialGood_swap o D D' ζ r,
    findTrials_eq_repeatUntil o ho.eps_pos]
  have hf := measurable_acceptTrial_fixed o r
  refine ⟨repeatUntil_probability _ hf o.K, repeatUntil_probability _ hf o.K,
    repeatUntil_ac hac0 hf o.K, repeatUntil_ac hac1 hf o.K, ?_, ?_, ?_⟩
  · convert repeatUntil_tv htv0 hf o.K using 1; ring
  · convert repeatUntil_tv htv1 hf o.K using 1; ring
  · convert repeatUntil_private he hp hf o.K using 1; ring

end DPCut
