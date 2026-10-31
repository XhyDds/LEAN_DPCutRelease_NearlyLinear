import DPCut.InnerReleaseUtility

/-! Simultaneous accuracy of the actual CutRelease output under adaptive sampling. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma measurableSet_release_good {n : ℕ} (w : Weights n) (γ E : ℝ) :
    MeasurableSet {h | Nonnegative h ∧ AllCuts w h γ E} :=
  (measurableSet_nonnegative measurable_id).inter
    (measurableSet_allCuts measurable_const measurable_id γ E)

/-- Each released portion adds `B` to the same all-cut invariant. The remaining
mass is discarded only at a successful stopping test. -/
theorem outerLoop_release_failure {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 0 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hstop : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop)
    (w : Weights n) (hw : Bounded U w) (t : ℕ) (ht : 0 < t)
    (a out : Weights n) (A : ℝ) (ha : IsMask a) (hi : ReleaseInvariant w a out p.gamma A)
    (hbudget : (19 / 20 : ℝ) ^ (t - 1) * mass (hadamard a w) + 2 * c.tau2 ≤ c.stop) :
    outerLoop p c w t a out {h | ¬(Nonnegative h ∧ AllCuts w h p.gamma (A + t * c.B + c.stop))} ≤
      ENNReal.ofReal (t * (c.T2 * c.betaGE + c.beta2)) := by
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ c.B := (mul_nonneg (Nat.cast_nonneg n) hU).trans hc.certificate_lower
  have hβ := hc.betaGE_nonneg
  have hβ2 := hc.beta2_pos
  have hS : 0 ≤ c.stop := (by positivity : 0 ≤ 10 * (c.B + c.tau2 / p.gamma)).trans hstop
  induction t generalizing a out A with
  | zero => omega
  | succ t ih =>
    let P := fun h : Weights n => Nonnegative h ∧ AllCuts w h p.gamma (A + (t + 1) * c.B + c.stop)
    have hP : MeasurableSet {h | P h} := measurableSet_release_good w p.gamma _
    rw [outerLoop_succ_raw]
    letI := laplace_isProbabilityMeasure (one_div_pos.mpr hc.eps2_pos)
    let H := fun z : ℝ => clipNoisyMass c.massCap (mass (hadamard a w)) z c.tau2
    have hHm : Measurable H := by dsimp [H]; fun_prop
    letI (z : ℝ) := outerAfterMass_probability hn p c hc.oracle_privacy hc.eps2_pos w a out t (H z)
    have hnoise : laplace (1 / c.eps2) (Icc (-c.tau2) c.tau2)ᶜ ≤ ENNReal.ofReal c.beta2 := by
      rw [hc.tau2_eq]
      exact laplace_interval_failure hc.eps2_pos hc.beta2_pos hc.beta2_lt_one
    have hb : (laplace (1 / c.eps2)).bind (fun z => outerAfterMass p c w t a out (H z)) {h | ¬P h} ≤
        ENNReal.ofReal (c.beta2 + (c.T2 * c.betaGE + t * (c.T2 * c.betaGE + c.beta2))) := by
      apply measure_bind_le_of_good (f := fun z => outerAfterMass p c w t a out (H z))
        ((measurable_outerAfterMass hn p c hc.oracle_privacy hc.eps2_pos w a out t).comp hHm)
        measurableSet_Icc hP.compl hβ2.le (by positivity) hnoise
      intro z hz
      have hM0 : 0 ≤ mass (hadamard a w) := Finset.sum_nonneg fun e _ => mul_nonneg (ha e).1 (hw e).1
      have hm := clipped_mass_bounds hM0
          ((add_le_add_right (masked_mass_le_public_bound hw ha) _).trans hc.massCap_lower) hz
      unfold outerAfterMass
      split_ifs with hdone
      · have hres : mass (hadamard a w) ≤ c.stop := by
          rcases hdone with hzero | hsmall
          · simpa [hzero, mass, hadamard] using hS
          · exact hm.1.trans hsmall
        have hg := hi.finish (fun e => (hw e).1) ha hγ.le hres
        have hpout : P out := ⟨hg.1, hg.2.mono_error (by
          have hnonneg : 0 ≤ ((t : ℝ) + 1) * c.B := mul_nonneg (by positivity) hB
          linarith)⟩
        simp [Measure.dirac_apply' _ hP.compl, hpout]
      · have hcontinue : c.stop < H z := lt_of_not_ge (fun hh => hdone (Or.inr hh))
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
          outerResult_probability hn p c hc.oracle_privacy hc.eps2_pos w a out t r
        apply measure_bind_le_of_good
          (measurable_outerResult hn p c hc.oracle_privacy hc.eps2_pos w a out t)
          (measurableSet_innerReleaseGood (hadamard a w) p.gamma c.B) hP.compl
          (by positivity) (by positivity)
          (innerLoop_initial_release hn hU p c hc hγ hγ1 hw ha hM hH hm.1 hHH hlarge)
        intro r hr
        cases r with
        | none => exact False.elim hr
        | some pair =>
          have hi' := hi.update hr.1 hr.2.1 hr.2.2.2
          have hbudget' : (19 / 20 : ℝ) ^ (t - 1) * mass (hadamard (residualUpdate a pair.2) w) +
              2 * c.tau2 ≤ c.stop := by
            rw [hadamard_residualUpdate]
            have hc' := mul_le_mul_of_nonneg_left hr.2.2.1 (by positivity : 0 ≤ (19 / 20 : ℝ) ^ (t - 1))
            have htEq : t = t - 1 + 1 := by omega
            simp only [Nat.add_sub_cancel] at hbudget
            conv_rhs at hc' => rw [← mul_assoc, ← pow_succ, ← htEq]
            linarith
          have hrec := ih ht' _ _ (A + c.B) (residualUpdate_isMask ha hr.2.1) hi' hbudget'
          have heq : A + c.B + t * c.B + c.stop = A + ((t : ℝ) + 1) * c.B + c.stop := by ring
          simpa only [heq] using hrec
    have heq : c.beta2 + (c.T2 * c.betaGE + t * (c.T2 * c.betaGE + c.beta2)) =
        ((t + 1 : ℕ) : ℝ) * (c.T2 * c.betaGE + c.beta2) := by push_cast; ring
    rw [heq] at hb
    simpa only [P, Nat.cast_add, Nat.cast_one] using hb

theorem cutRelease_utility_explicit {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) (w : Weights n) (hw : Bounded U w) :
    let c := runConfig n U p outerUtilityConstants
    HighProbability (cutReleaseLaw U p outerUtilityConstants w)
      (c.T1 * c.T2 * c.betaGE + c.T1 * c.beta2)
      (fun h => Nonnegative h ∧ AllCuts w h p.gamma (c.T1 * c.B + c.stop)) := by
  let c := runConfig n U p outerUtilityConstants
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  have hstop := outer_stopping_threshold hn hU p hp
  have hb := outer_initial_budget hn hU p c hc hp.1 hp.2.1 rfl hstop hw
  have hf := outerLoop_release_failure hn (by linarith) p c hc hp.1 hp.2.1 hstop w hw c.T1 hb.1
    1 0 0 (by intro e; norm_num) (releaseInvariant_initial w p.gamma) hb.2
  letI := outerLoop_probability hn p c hc.oracle_privacy hc.eps2_pos w c.T1 1 0
  letI : IsProbabilityMeasure (cutReleaseLaw U p outerUtilityConstants w) := by
    change IsProbabilityMeasure (outerLoop p c w c.T1 1 0)
    infer_instance
  apply highProbability_of_failure (measurableSet_release_good w p.gamma _)
    (add_nonneg (mul_nonneg (by positivity) hc.betaGE_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) hc.beta2_pos.le))
  change outerLoop p c w c.T1 1 0 _ ≤ _
  have heq : (c.T1 : ℝ) * (c.T2 * c.betaGE + c.beta2) =
      c.T1 * c.T2 * c.betaGE + c.T1 * c.beta2 := by ring
  simpa only [zero_add, heq] using hf

end DPCut
