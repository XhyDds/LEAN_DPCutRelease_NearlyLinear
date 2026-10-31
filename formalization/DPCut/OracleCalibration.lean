import DPCut.OracleTrial

/-! Explicit sufficient numerical conditions for the local analysis in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DPCut

structure OraclePrivacyBounds (n : ℕ) (o : OracleConfig) : Prop where
  eps_pos : 0 < o.eps1
  lam_lower : 8 ≤ o.lam
  beta_pos : 0 < o.betaChi
  beta_lt_one : o.betaChi < 1
  delta_pos : 0 < o.delta1
  delta_lt_half : o.delta1 < 1 / 2
  batch_pos : 0 < o.k
  batch_lower : 96 * Real.log (n / (o.betaChi * o.delta1)) ≤ o.k
  gaussian_scale : 8 * ((o.k : ℝ) / 4 + Real.sqrt (o.k * Real.log (1 / o.delta1)) +
    Real.log (1 / o.delta1)) / o.lam ≤ o.eps1

lemma calibrated_gaussian_loss {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (D D' ζ r : Weights n) (hr : IsMask r)
    (hζ : l1 ζ ≤ 1) (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    let X := optimizer o.lam D
    let Y := optimizer o.lam D'
    covarianceDistance X Y < 1 / 2 ∧
      4 * (o.k * covarianceDistance X Y ^ 2 +
        Real.sqrt (o.k * Real.log (1 / o.delta1)) * covarianceDistance X Y +
        Real.log (1 / o.delta1) * covarianceDistance X Y) ≤
          o.eps1 * oracleSensitivity ζ r X Y := by
  dsimp
  let d := covarianceDistance (optimizer o.lam D) (optimizer o.lam D')
  let W := oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')
  have hl : 0 < o.lam := by linarith [ho.lam_lower]
  have hW := oracleSensitivity_bounds hn hr ζ (optimizer_isOptimizer hn o.lam D).1
    (optimizer_isOptimizer hn o.lam D').1
  have hW0 : 0 ≤ W := hW.1
  have hW1 : W ≤ 1 := hW.2.trans hζ
  have hd0 : 0 ≤ d := frobenius_nonneg _
  have hd : d ≤ 2 * W / o.lam := optimizer_covariance_le_charge hn hl D D' ζ r hr hξ
  have hdlam : d * o.lam ≤ 2 * W := (le_div_iff₀ hl).mp hd
  have hdquarter : d ≤ 1 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left ho.lam_lower hd0]
  refine ⟨by change d < 1 / 2; linarith, ?_⟩
  have ht : 0 ≤ Real.log (1 / o.delta1) := Real.log_nonneg
    ((one_le_div ho.delta_pos).mpr (by linarith [ho.delta_lt_half]))
  let B := (o.k : ℝ) / 4 + Real.sqrt (o.k * Real.log (1 / o.delta1)) + Real.log (1 / o.delta1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hk : (o.k : ℝ) * d ≤ (o.k : ℝ) / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hdquarter (Nat.cast_nonneg o.k)]
  have hstep : 4 * ((o.k : ℝ) * d ^ 2 + Real.sqrt (o.k * Real.log (1 / o.delta1)) * d +
      Real.log (1 / o.delta1) * d) ≤ 4 * d * B := by
    have hh := mul_le_mul_of_nonneg_right hk hd0
    dsimp [B]
    nlinarith
  have hs : 8 * B / o.lam ≤ o.eps1 := ho.gaussian_scale
  have hscaled := mul_le_mul_of_nonneg_right hs hW0
  have hbd := mul_le_mul_of_nonneg_right hd (show 0 ≤ 4 * B by positivity)
  change _ ≤ o.eps1 * W
  have he : (2 * W / o.lam) * (4 * B) = (8 * B / o.lam) * W := by ring
  rw [he] at hbd
  nlinarith

theorem calibrated_trial_good {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (D D' ζ r : Weights n) (hr : IsMask r)
    (hζ : l1 ζ ≤ 1) (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    HighProbability (trialLaw o D) (2 * o.delta1) (fun p => p ∈ trialGood o D D' ζ r) := by
  obtain ⟨hd, he⟩ := calibrated_gaussian_loss hn o ho D D' ζ r hr hζ hξ
  have h := commonTrialGood_highProbability hn (optimizer_isOptimizer hn o.lam D).1
    (optimizer_isOptimizer hn o.lam D').1 ho.beta_pos ho.beta_lt_one ho.delta_pos
    ho.delta_lt_half ho.batch_pos ho.batch_lower hd he
  refine ⟨measurableSet_trialGood o D D' ζ r, ?_⟩
  rw [← trialLaw_map_fst o ho.eps_pos D] at h
  simpa only [prob, Measure.map_apply measurable_fst h.1] using h.2

theorem calibrated_trial_auxiliary {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (D D' ζ r : Weights n) (hr : IsMask r)
    (hζ : l1 ζ ≤ 1) (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    let G := trialGood o D D' ζ r
    IsProbabilityMeasure ((trialLaw o D)[|G]) ∧
    IsProbabilityMeasure ((trialLaw o D')[|G]) ∧
    ((trialLaw o D)[|G]) ≪ trialLaw o D ∧ ((trialLaw o D')[|G]) ≪ trialLaw o D' ∧
    TVClose (trialLaw o D) ((trialLaw o D)[|G]) (2 * o.delta1) ∧
    TVClose (trialLaw o D') ((trialLaw o D')[|G]) (2 * o.delta1) ∧
    Indistinguishable ((trialLaw o D)[|G]) ((trialLaw o D')[|G])
      (10 * o.eps1 * oracleSensitivity ζ r (optimizer o.lam D) (optimizer o.lam D')) 0 := by
  dsimp
  letI := trialLaw_probability o ho.eps_pos D
  letI := trialLaw_probability o ho.eps_pos D'
  have h0 := calibrated_trial_good hn o ho D D' ζ r hr hζ hξ
  have h1 := calibrated_trial_good hn o ho D' D ζ r hr hζ
    (fun e => by simpa only [abs_sub_comm] using hξ e)
  rw [trialGood_swap o D D' ζ r] at h1
  have hp0 : trialLaw o D (trialGood o D D' ζ r) ≠ 0 := by
    intro hz
    have he : prob (trialLaw o D) (trialGood o D D' ζ r) = 0 := by simp [prob, hz]
    have hb : 1 - 2 * o.delta1 ≤ prob (trialLaw o D) (trialGood o D D' ζ r) := h0.2
    linarith [ho.delta_lt_half]
  have hp1 : trialLaw o D' (trialGood o D D' ζ r) ≠ 0 := by
    intro hz
    have he : prob (trialLaw o D') (trialGood o D D' ζ r) = 0 := by simp [prob, hz]
    have hb : 1 - 2 * o.delta1 ≤ prob (trialLaw o D') (trialGood o D D' ζ r) := h1.2
    linarith [ho.delta_lt_half]
  refine ⟨cond_isProbabilityMeasure hp0, cond_isProbabilityMeasure hp1,
    cond_absolutelyContinuous, cond_absolutelyContinuous, ?_, ?_, ?_⟩
  · intro s hs
    exact (conditioning_tv _ h0.1 hp0 s hs).trans (by linarith [h0.2])
  · intro s hs
    exact (conditioning_tv _ h1.1 hp1 s hs).trans (by linarith [h1.2])
  · exact conditional_trial_private hn o (by linarith [ho.lam_lower]) ho.eps_pos D D' ζ r hr hξ hp0 hp1

end DPCut
