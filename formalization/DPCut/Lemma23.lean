import DPCut.ReleaseUtility
import DPCut.ReleaseCalibration
import DPCut.ReleaseNonnegative

/-!
Lemma 23 (`lem:utility`): simultaneous relative
cut accuracy for the actual bounded CutRelease law, with a uniform coefficient.
The constants and algorithm are the same as in Lemma 22.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

theorem bounded_cut_release_utility {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) (w : Weights n) (hw : Bounded U w) :
    HighProbability (cutReleaseLaw U p outerUtilityConstants w) p.beta
      (fun h => Nonnegative h ∧ AllCuts w h p.gamma ((2 : ℝ) ^ 121 * boundedError n U p)) := by
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  letI : IsProbabilityMeasure (cutReleaseLaw U p outerUtilityConstants w) :=
    outerLoop_probability hn p _ hc.oracle_privacy hc.eps2_pos w _ 1 0
  have hh := cutRelease_utility_explicit hn hU p hp w hw
  dsimp only at hh
  rw [release_failure_budget hn hU p hp] at hh
  apply HighProbability.mono _ hh (measurableSet_release_good w p.gamma _)
  intro h hgood
  exact ⟨hgood.1, hgood.2.mono_error (release_error_bound hn hU p hp)⟩

/-- **Lemma 23**, with the universal choice `C = 2^121`. -/
theorem lemma23 : BoundedUtilityStatement outerUtilityConstants := by
  refine ⟨(2 : ℝ) ^ 121, by positivity, ?_⟩
  intro n hn U hU p hp w hw
  exact bounded_cut_release_utility hn hU p hp w hw

end DPCut
