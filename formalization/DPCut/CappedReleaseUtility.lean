import DPCut.CappedInnerRelease
import DPCut.CappedReleasePrivacy
import DPCut.ReleaseUtility

/-! The actual capped release satisfies the simultaneous cut guarantee. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

/-- Each released portion adds `B` to the same all-cut invariant. The remaining
mass is discarded only at a successful stopping test. -/
theorem cappedOuterLoop_release_failure {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n 1 p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hstop : 100 * (c.B + c.tau2 / p.gamma) ≤ c.stop)
    (w : Weights n) (hw : Bounded 1 w) (t : ℕ) (ht : 0 < t)
    (a out : Weights n) (A : ℝ) (ha : IsMask a) (hi : ReleaseInvariant w a out p.gamma A)
    (hbudget : (19 / 20 : ℝ) ^ (t - 1) * mass (hadamard a w) + 2 * c.tau2 ≤ c.stop) :
    cappedOuterLoop p c w t a out {h | ¬(Nonnegative h ∧ AllCuts w h p.gamma (A + t * c.B + c.stop + 2 * c.tau2))} ≤
      ENNReal.ofReal (t * (c.T2 * c.betaGE + c.beta2)) := by
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hB : 0 ≤ c.B := (by positivity : 0 ≤ (n : ℝ) * 1).trans hc.certificate_lower
  have hβ := hc.betaGE_nonneg
  have hβ2 := hc.beta2_pos
  have hS : 0 ≤ c.stop := (by positivity : 0 ≤ 100 * (c.B + c.tau2 / p.gamma)).trans hstop
  induction t generalizing a out A with
  | zero => omega
  | succ t ih =>
    let P := fun h : Weights n => Nonnegative h ∧ AllCuts w h p.gamma (A + (t + 1) * c.B + c.stop + 2 * c.tau2)
    have hP : MeasurableSet {h | P h} := measurableSet_release_good w p.gamma _
    rw [cappedOuterLoop_succ_raw]
    letI := laplace_isProbabilityMeasure (one_div_pos.mpr hc.eps2_pos)
    let H := fun z : ℝ => lowerBiasedMass (mass a) (mass (hadamard a w)) z c.tau2
    have hHm : Measurable H := by dsimp [H]; fun_prop
    letI (z : ℝ) := cappedOuterAfterMass_probability hn p c hc.oracle_privacy hc.eps2_pos w a out t (H z)
    have hnoise : laplace (1 / c.eps2) (Icc (-c.tau2) c.tau2)ᶜ ≤ ENNReal.ofReal c.beta2 := by
      rw [hc.tau2_eq]
      exact laplace_interval_failure hc.eps2_pos hc.beta2_pos hc.beta2_lt_one
    have hb : (laplace (1 / c.eps2)).bind (fun z => cappedOuterAfterMass p c w t a out (H z)) {h | ¬P h} ≤
        ENNReal.ofReal (c.beta2 + (c.T2 * c.betaGE + t * (c.T2 * c.betaGE + c.beta2))) := by
      apply measure_bind_le_of_good (f := fun z => cappedOuterAfterMass p c w t a out (H z))
        ((measurable_cappedOuterAfterMass hn p c hc.oracle_privacy hc.eps2_pos w a out t).comp hHm)
        measurableSet_Icc hP.compl hβ2.le (by positivity) hnoise
      intro z hz
      have hM0 : 0 ≤ mass (hadamard a w) := Finset.sum_nonneg fun e _ => mul_nonneg (ha e).1 (hw e).1
      have hcap : mass (hadamard a w) ≤ mass a :=
        Finset.sum_le_sum fun e _ => mul_le_of_le_one_right (ha e).1 (hw e).2
      have hm := lowerBiasedMass_good hM0 hcap (abs_le.mpr hz)
      change mass (hadamard a w) - 2 * c.tau2 ≤ H z ∧ H z ≤ mass (hadamard a w) at hm
      unfold cappedOuterAfterMass
      split_ifs with hdone
      · have hres : mass (hadamard a w) ≤ c.stop + 2 * c.tau2 := by
          rcases hdone with hzero | hsmall
          · simpa [hzero, mass, hadamard] using (add_nonneg hS (by positivity : 0 ≤ 2 * c.tau2))
          · linarith [hm.1]
        have hg := hi.finish (fun e => (hw e).1) ha hγ.le hres
        have hpout : P out := ⟨hg.1, hg.2.mono_error (by
          have hnonneg : 0 ≤ ((t : ℝ) + 1) * c.B := mul_nonneg (by positivity) hB
          linarith)⟩
        simp [Measure.dirac_apply' _ hP.compl, hpout]
      · have hcontinue : c.stop < H z := lt_of_not_ge (fun hh => hdone (Or.inr hh))
        obtain ⟨hH, hM, hHM, hMH, hlarge'⟩ := capped_continuing_mass hγ hB hτ.le hm
          (hstop.trans_lt hcontinue)
        have hlarge : 100 * c.B ≤ mass (hadamard a w) := by linarith
        have ht' : 0 < t := by
          by_contra h
          have ht0 : t = 0 := by omega
          subst t
          simp only [Nat.add_sub_cancel, pow_zero, one_mul] at hbudget
          exact (not_lt_of_ge (hm.2.trans (by linarith [hτ]))) hcontinue
        letI := cappedInnerLoop_probability hn p c hc.oracle_privacy (hadamard a w) a (H z) c.T2 (initialEstimate (H z) a)
        letI (r : Option (Weights n × Weights n)) :=
          cappedOuterResult_probability hn p c hc.oracle_privacy hc.eps2_pos w a out t r
        apply measure_bind_le_of_good
          (measurable_cappedOuterResult hn p c hc.oracle_privacy hc.eps2_pos w a out t)
          (measurableSet_innerReleaseGood (hadamard a w) p.gamma c.B) hP.compl
          (by positivity) (by positivity)
          (cappedInnerLoop_initial_release hn p c hc hγ hγ1 hw ha hM hH hHM hMH hlarge)
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
          have heq : A + c.B + t * c.B + c.stop + 2 * c.tau2 = A + ((t : ℝ) + 1) * c.B + c.stop + 2 * c.tau2 := by ring
          simpa only [heq] using hrec
    have heq : c.beta2 + (c.T2 * c.betaGE + t * (c.T2 * c.betaGE + c.beta2)) =
        ((t + 1 : ℕ) : ℝ) * (c.T2 * c.betaGE + c.beta2) := by push_cast; ring
    rw [heq] at hb
    simpa only [P, Nat.cast_add, Nat.cast_one] using hb


end DPCut
