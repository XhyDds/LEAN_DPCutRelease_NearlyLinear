import DPCut.OuterHorizon
import DPCut.StoppingCalibration

/-!
Lemma 22 (`lem:outer_round`) of the current root manuscript. The original
`OuterRoundStatement` is proved with explicit universal constants, including
the stopping calibration; there is no additional threshold hypothesis.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

theorem outerRound_utility {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hT : c.T1 = outerHorizon n U 80) (hstop : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop)
    (w : Weights n) (hw : Bounded U w) :
    HighProbability (outerStopsLaw p c w c.T1 1)
      (c.T1 * c.T2 * c.betaGE + c.T1 * c.beta2) (fun stopped => stopped = true) := by
  obtain ⟨hT1, hbudget⟩ := outer_initial_budget hn hU p c hc hγ hγ1 hT hstop hw
  have hfail := outerStopsLaw_failure hn (by linarith) p c hc hγ hγ1 hstop w hw c.T1 hT1 1
    (by intro e; norm_num) hbudget
  letI := outerStopsLaw_probability hn p c hc.oracle_privacy hc.eps2_pos w c.T1 1
  apply highProbability_of_failure (measurableSet_singleton true)
    (add_nonneg (mul_nonneg (by positivity) hc.betaGE_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) hc.beta2_pos.le))
  have hs : {b : Bool | ¬b = true} = {false} := by ext b; cases b <;> simp
  change outerStopsLaw p c w c.T1 1 {b | ¬b = true} ≤ _
  rw [hs]
  convert hfail using 1
  congr 1
  ring

/-- **Lemma 22**, with the original target and an explicit universal calibration. -/
theorem lemma22 : OuterRoundStatement outerUtilityConstants := by
  intro n hn U hU p hp w hw
  exact outerRound_utility hn hU p _ (outerConfig_inner_utility_bounds_general hn hU p hp)
    hp.1 hp.2.1 rfl (outer_stopping_threshold_general hn hU p hp) w hw

end DPCut
