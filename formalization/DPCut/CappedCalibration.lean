import DPCut.CappedReleaseUtility
import DPCut.CappedOutput
import DPCut.MainCalibration

/-! Uniform error and failure calibration for Lemma 29. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

lemma capped_stopping_threshold {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    let c := cappedRunConfig n p
    100 * (c.B + c.tau2 / p.gamma) ≤ c.stop := by
  have h := outer_stopping_threshold hn (le_refl 1) p hp
  change 100 * ((runConfig n 1 p outerUtilityConstants).B +
    (runConfig n 1 p outerUtilityConstants).tau2 / p.gamma) ≤
      10 * (runConfig n 1 p outerUtilityConstants).stop
  linarith

lemma capped_stop_nonneg {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    0 ≤ (cappedRunConfig n p).stop := by
  have hc := cappedConfig_inner_utility_bounds hn p hp
  have hτ : 0 < (cappedRunConfig n p).tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ (cappedRunConfig n p).B := (by positivity : 0 ≤ (n : ℝ) * 1).trans hc.certificate_lower
  have hg := hp.1
  exact (by positivity : 0 ≤ 100 * ((cappedRunConfig n p).B +
    (cappedRunConfig n p).tau2 / p.gamma)).trans (capped_stopping_threshold hn p hp)

theorem cappedRelease_utility_explicit {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (D : Finset (Edge n)) (w : Weights n) (hw : CappedOn D w) :
    let c := cappedRunConfig n p
    HighProbability (cappedReleaseLaw p (supportMask D) w) p.beta
      (fun h => AllCuts w h p.gamma (c.T1 * c.B + c.stop + 2 * c.tau2)) := by
  let c := cappedRunConfig n p
  have hc := cappedConfig_inner_utility_bounds hn p hp
  have hstop := capped_stopping_threshold hn p hp
  have hstop0 := capped_stop_nonneg hn p hp
  have hstop' : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop := by
    change 100 * (c.B + c.tau2 / p.gamma) ≤ c.stop at hstop
    change 0 ≤ c.stop at hstop0
    linarith
  have hb := outer_initial_budget hn (le_refl 1) p c hc hp.1 hp.2.1 rfl hstop' hw.1
  have hi : ReleaseInvariant w (supportMask D) 0 p.gamma 0 := by
    constructor
    · intro e; simp
    · rw [supportMask_input hw, sub_self]
      intro S
      simp [cut, pairing]
  have hbudget : (19 / 20 : ℝ) ^ (c.T1 - 1) * mass (hadamard (supportMask D) w) + 2 * c.tau2 ≤ c.stop := by
    rw [supportMask_input hw]
    simpa [hadamard, mass] using hb.2
  have hf := cappedOuterLoop_release_failure hn p c hc hp.1 hp.2.1 hstop w hw.1 c.T1 hb.1
    (supportMask D) 0 0 (supportMask_isMask D) hi hbudget
  letI : IsProbabilityMeasure (cappedReleaseLaw p (supportMask D) w) :=
    cappedOuterLoop_probability hn p c hc.oracle_privacy hc.eps2_pos w c.T1 (supportMask D) 0
  have heq : (c.T1 : ℝ) * (c.T2 * c.betaGE + c.beta2) = p.beta := by
    have h := release_failure_budget hn (le_refl 1) p hp
    change c.T1 * c.T2 * c.betaGE + c.T1 * c.beta2 = p.beta at h
    linarith
  have hg : HighProbability (cappedReleaseLaw p (supportMask D) w) p.beta
      (fun h => Nonnegative h ∧ AllCuts w h p.gamma (c.T1 * c.B + c.stop + 2 * c.tau2)) := by
    apply highProbability_of_failure (measurableSet_release_good w p.gamma _) hp.2.2.2.2.2.2.1.le
    simpa only [zero_add, heq] using hf
  exact HighProbability.mono _ hg (measurableSet_allCuts measurable_const measurable_id _ _)
    (fun _ hh => hh.2)

lemma boundedError_unit_le {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    boundedError n 1 p ≤ 2 * mainError n p := by
  have hL := (core_log_bounds hn (le_refl 1) p hp).one_le
  have hL0 : 0 ≤ logFactor n 1 p := by linarith
  have hg := hp.1
  have he := hp.2.2.1
  have hge : p.gamma * p.epsilon ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hp.2.2.2.1 hg.le
    linarith [hp.2.1]
  have hnle : (n : ℝ) ≤ n / (p.gamma * p.epsilon) :=
    (le_div_iff₀ (mul_pos hg he)).mpr (mul_le_of_le_one_right (Nat.cast_nonneg _) hge)
  have hpow : logFactor n 1 p ≤ logFactor n 1 p ^ 7 := by
    simpa using pow_le_pow_right₀ hL (show 1 ≤ 7 by omega)
  have h := mul_le_mul hnle hpow hL0 (by positivity : 0 ≤ n / (p.gamma * p.epsilon))
  unfold boundedError mainError
  simp only [mul_one]
  linarith

theorem cappedRelease_error_bound {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    let c := cappedRunConfig n p
    c.T1 * c.B + c.stop + 2 * c.tau2 ≤ (2 : ℝ) ^ 126 * mainError n p := by
  let c := runConfig n 1 p outerUtilityConstants
  have hc := outerConfig_inner_utility_bounds hn (le_refl 1) p hp
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ c.B := (by positivity : 0 ≤ (n : ℝ) * 1).trans hc.certificate_lower
  have hs := outer_stopping_threshold hn (le_refl 1) p hp
  change 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop at hs
  have hτγ : c.tau2 ≤ c.tau2 / p.gamma := (le_div_iff₀ hp.1).mpr
    (mul_le_of_le_one_right hτ.le (by linarith [hp.2.1]))
  have hTB : 0 ≤ c.T1 * c.B := mul_nonneg (Nat.cast_nonneg _) hB
  have hbound := release_error_bound hn (le_refl 1) p hp
  change c.T1 * c.B + c.stop ≤ (2 : ℝ) ^ 121 * boundedError n 1 p at hbound
  have hb := mul_le_mul_of_nonneg_left (boundedError_unit_le hn p hp) (by positivity : (0 : ℝ) ≤ 2 ^ 121)
  change c.T1 * c.B + 10 * c.stop + 2 * c.tau2 ≤ _
  have hmain : 0 ≤ mainError n p := by
    unfold mainError
    have hg := hp.1
    have he := hp.2.2.1
    have hL := (core_log_bounds hn (le_refl 1) p hp).one_le
    positivity
  norm_num at hbound hb ⊢
  linarith

end DPCut
