import DPCut.InnerContraction
import DPCut.OuterStopsMeasurable

/-! Adaptive outer stopping, including the noisy mass in the stopping round. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma hadamard_residualUpdate {n : ℕ} (a w r : Weights n) :
    hadamard (residualUpdate a r) w = residualUpdate (hadamard a w) r := by
  funext e
  dsimp [hadamard, residualUpdate]
  ring

/-- The remaining horizon includes one final mass-release stopping test. -/
theorem outerStopsLaw_failure {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 0 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hstop : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop)
    (w : Weights n) (hw : Bounded U w) (t : ℕ) (ht : 0 < t) (a : Weights n) (ha : IsMask a)
    (hbudget : (19 / 20 : ℝ) ^ (t - 1) * mass (hadamard a w) + 2 * c.tau2 ≤ c.stop) :
    outerStopsLaw p c w t a {false} ≤ ENNReal.ofReal (t * (c.T2 * c.betaGE + c.beta2)) := by
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ c.B := (mul_nonneg (Nat.cast_nonneg n) hU).trans hc.certificate_lower
  have hβ := hc.betaGE_nonneg
  have hβ2 := hc.beta2_pos
  induction t generalizing a with
  | zero => omega
  | succ t ih =>
    rw [outerStopsLaw_succ_raw]
    letI := laplace_isProbabilityMeasure (one_div_pos.mpr hc.eps2_pos)
    let H := fun z : ℝ => clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
    have hHm : Measurable H := by dsimp [H]; fun_prop
    letI (z : ℝ) := outerStopAfterMass_probability hn p c hc.oracle_privacy hc.eps2_pos w a t (H z)
    have hnoise : laplace (1 / c.eps2) (Icc (-c.tau2) c.tau2)ᶜ ≤ ENNReal.ofReal c.beta2 := by
      rw [hc.tau2_eq]
      exact laplace_interval_failure hc.eps2_pos hc.beta2_pos hc.beta2_lt_one
    have hb : (laplace (1 / c.eps2)).bind (fun z => outerStopAfterMass p c w t a (H z)) {false} ≤
        ENNReal.ofReal (c.beta2 + (c.T2 * c.betaGE + t * (c.T2 * c.betaGE + c.beta2))) := by
      apply measure_bind_le_of_good (f := fun z => outerStopAfterMass p c w t a (H z))
        ((measurable_outerStopAfterMass hn p c hc.oracle_privacy hc.eps2_pos w a t).comp hHm)
        measurableSet_Icc (measurableSet_singleton false) hβ2.le (by positivity) hnoise
      intro z hz
      unfold outerStopAfterMass
      split_ifs with hdone
      · simp [Measure.dirac_apply']
      · have hcontinue : c.stop < H z := lt_of_not_ge (fun hh => hdone (Or.inr hh))
        have hM0 : 0 ≤ mass (hadamard a w) := Finset.sum_nonneg fun e _ => mul_nonneg (ha e).1 (hw e).1
        have hm := clipped_mass_bounds hM0
          ((add_le_add_right (masked_mass_le_public_bound hw ha) _).trans hc.massCap_lower) hz
        obtain ⟨hM, hH, _, hHH⟩ := continuing_mass_bounds hB hτ.le hγ hγ1 hm.1 hm.2 hstop hcontinue
        have hτγ : c.tau2 ≤ c.tau2 / p.gamma := (le_div_iff₀ hγ).mpr
          (mul_le_of_le_one_right hτ.le (by linarith))
        have hlarge : 10 * c.B ≤ mass (hadamard a w) := by
          change c.stop < clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2 at hcontinue
          linarith [hm.2]
        have ht' : 0 < t := by
          by_contra h
          have ht0 : t = 0 := by omega
          subst t
          simp only [Nat.add_sub_cancel, pow_zero, one_mul] at hbudget
          exact (not_lt_of_ge (hm.2.trans hbudget)) hcontinue
        letI := innerLoop_probability hn p c hc.oracle_privacy (hadamard a w) (H z) c.T2 (initialEstimate (H z) a)
        letI (r : Option (Weights n × Weights n)) :=
          outerStopResult_probability hn p c hc.oracle_privacy hc.eps2_pos w a t r
        apply measure_bind_le_of_good
          (measurable_outerStopResult hn p c hc.oracle_privacy hc.eps2_pos w a t)
          (measurableSet_innerContracts (hadamard a w)) (measurableSet_singleton false)
          (by positivity) (by positivity)
          (innerLoop_initial_contracts hn hU p c hc hγ hγ1 hw ha hM hH hm.1 hHH hlarge)
        intro r hr
        cases r with
        | none => exact False.elim hr
        | some pair =>
          apply ih ht' _ (residualUpdate_isMask ha hr.1)
          rw [hadamard_residualUpdate]
          have hc' := mul_le_mul_of_nonneg_left hr.2 (by positivity : 0 ≤ (19 / 20 : ℝ) ^ (t - 1))
          have htEq : t = t - 1 + 1 := by omega
          simp only [Nat.add_sub_cancel] at hbudget
          conv_rhs at hc' => rw [← mul_assoc, ← pow_succ, ← htEq]
          linarith
    convert hb using 1
    push_cast
    congr 1
    ring

end DPCut
