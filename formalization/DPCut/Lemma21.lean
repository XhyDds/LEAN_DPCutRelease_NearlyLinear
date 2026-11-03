import DPCut.InnerUtilityCalibration
import DPCut.MassClipping

/-!
Lemma 21 (`lem:inner_round`).
The probability is joint over the mass release and all adaptive inner calls.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def innerRoundContinuation {n : ℕ} (p : Parameters) (c : RunConfig) (w a : Weights n) (z : ℝ) :
    Measure (ℝ × Option (Weights n × Weights n)) :=
  let H := clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
  (innerLoop p c (hadamard a w) H c.T2 (initialEstimate H a)).map (fun result => (H, result))

lemma measurable_innerRoundContinuation {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) :
    Measurable (innerRoundContinuation p c w a) := by
  let H := fun z : ℝ => clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hi : Measurable (fun z => innerLoop p c (hadamard a w) (H z) c.T2 (initialEstimate (H z) a)) :=
    measurable_innerLoop hn p c ho c.T2 measurable_const (by unfold initialEstimate; fun_prop) hH
  letI (z : ℝ) : IsProbabilityMeasure (innerLoop p c (hadamard a w) (H z) c.T2
      (initialEstimate (H z) a)) := innerLoop_probability hn p c ho _ _ _ _
  exact measurable_map_kernel hi (show Measurable (Function.uncurry
    (fun z (r : Option (Weights n × Weights n)) => (H z, r))) from
      (hH.comp measurable_fst).prodMk measurable_snd)

lemma innerRoundContinuation_probability {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (z : ℝ) :
    IsProbabilityMeasure (innerRoundContinuation p c w a z) := by
  let H := clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
  letI := innerLoop_probability hn p c ho (hadamard a w) H c.T2 (initialEstimate H a)
  exact Measure.isProbabilityMeasure_map (measurable_const.prodMk measurable_id).aemeasurable

lemma innerRoundLaw_probability {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (w a : Weights n) :
    IsProbabilityMeasure (innerRoundLaw p c w a) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  letI (z : ℝ) := innerRoundContinuation_probability hn p c ho w a z
  change IsProbabilityMeasure ((laplace (1 / c.eps2)).bind (innerRoundContinuation p c w a))
  exact probability_bind _ _ (measurable_innerRoundContinuation hn p c ho w a)

/-- Joint success of a fixed round, under exactly the displayed stopping threshold. -/
theorem innerRound_utility {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 0 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (w a : Weights n)
    (hw : Bounded U w) (ha : IsMask a) (hstop : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop) :
    HighProbability (innerRoundLaw p c w a) (c.T2 * c.betaGE + c.beta2)
      (fun result => c.stop < result.1 → result.2.isSome) := by
  let P := fun y : ℝ × Option (Weights n × Weights n) => c.stop < y.1 → y.2.isSome
  have hbad : MeasurableSet {y | ¬P y} := by
    have hs : MeasurableSet {y : ℝ × Option (Weights n × Weights n) |
        c.stop < y.1 ∧ y.2 = none} :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurable_snd measurableSet_option_none)
    convert hs using 1
    ext y
    cases y.2 <;> simp [P]
  have hP : MeasurableSet {y | P y} := by
    convert hbad.compl using 1
    ext y
    simp only [mem_setOf_eq, mem_compl_iff, not_not]
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ c.B := (mul_nonneg (Nat.cast_nonneg n) hU).trans hc.certificate_lower
  have hβ := hc.betaGE_nonneg
  have hβ2 := hc.beta2_pos
  have hwA : Bounded U (hadamard a w) := by
    intro e
    exact ⟨mul_nonneg (ha e).1 (hw e).1,
      (mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2⟩
  have hM0 : 0 ≤ mass (hadamard a w) := Finset.sum_nonneg fun e _ => (hwA e).1
  letI := innerRoundLaw_probability hn p c hc.oracle_privacy hc.eps2_pos w a
  apply highProbability_of_failure hP (by positivity)
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hc.eps2_pos)
  letI (z : ℝ) := innerRoundContinuation_probability hn p c hc.oracle_privacy w a z
  have hnoise : laplace (1 / c.eps2) (Icc (-c.tau2) c.tau2)ᶜ ≤ ENNReal.ofReal c.beta2 := by
    rw [hc.tau2_eq]
    exact laplace_interval_failure hc.eps2_pos hc.beta2_pos hc.beta2_lt_one
  have hb : (laplace (1 / c.eps2)).bind (innerRoundContinuation p c w a) {y | ¬P y} ≤
      ENNReal.ofReal (c.beta2 + c.T2 * c.betaGE) := by
    apply measure_bind_le_of_good (measurable_innerRoundContinuation hn p c hc.oracle_privacy w a)
      measurableSet_Icc hbad hc.beta2_pos.le (by positivity) hnoise
    intro z hz
    let H := clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
    change (innerLoop p c (hadamard a w) H c.T2 (initialEstimate H a)).map
      (fun r => (H, r)) {y | ¬P y} ≤ _
    rw [Measure.map_apply (show Measurable (fun r : Option (Weights n × Weights n) => (H, r)) from
      measurable_const.prodMk measurable_id) hbad]
    by_cases hcontinue : c.stop < H
    · have hmass := clipped_mass_bounds hM0
        ((add_le_add_right (masked_mass_le_public_bound hw ha) _).trans hc.massCap_lower) hz
      obtain ⟨hM, hH, hlarge, hHH⟩ := continuing_mass_bounds hB hτ.le hγ hγ1
        hmass.1 hmass.2 hstop hcontinue
      have hi := innerLoop_initial_failure hn p c hc.oracle_privacy hU hw ha hM hH hmass.1 hHH
        (hc.certificate_lower.trans hlarge) hγ hγ1 hc.eta_eq hc.horizon_eq hc.betaGE_nonneg
        (fun h hh => hc.aggregate_utility _ h hwA hh)
      apply le_trans (measure_mono (t := {none}) ?_) hi
      intro r hr
      cases r with
      | none => rfl
      | some v => exact False.elim (hr (by simp [P]))
    · have he : (fun r : Option (Weights n × Weights n) => (H, r)) ⁻¹' {y | ¬P y} = ∅ := by
        ext r
        simp [P, hcontinue]
      rw [he, measure_empty]
      exact zero_le _
  simpa only [add_comm] using hb

/-- **Lemma 21**, with Lemma 20's constants; the probability bound is joint. -/
theorem lemma21 : InnerRoundStatement utilityConstants := by
  intro n hn U hU p hp w a hw ha
  exact innerRound_utility hn (by linarith) p _ (runConfig_inner_utility_bounds_general hn hU p hp)
    hp.1 hp.2.1 w a hw ha

end DPCut
