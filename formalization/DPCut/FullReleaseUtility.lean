import DPCut.FullReleaseLaw
import DPCut.MainCalibration

/-! Joint all-cut accuracy for the complete release, including both failure budgets. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DPCut

lemma fullRelease_accuracy_add {n : ℕ} {w h y : Weights n} {U γ A : ℝ} (hγ : 0 ≤ γ)
    (hpre : AllCuts w (y + clipWeights U w) (γ / 2) 0)
    (hinner : AllCuts (clipWeights U w) h (γ / 2) A) : AllCuts w (h + y) γ A := by
  intro S
  have hp := hpre S
  have hi := hinner S
  rw [cut_add] at hp ⊢
  have hid : cut w S - (cut h S + cut y S) =
      (cut w S - (cut y S + cut (clipWeights U w) S)) +
        (cut (clipWeights U w) S - cut h S) := by ring
  rw [hid]
  have ht := abs_add_le (cut w S - (cut y S + cut (clipWeights U w) S))
    (cut (clipWeights U w) S - cut h S)
  have hc := mul_le_mul_of_nonneg_left (cut_clipWeights_le U w S) hγ
  linarith

theorem fullRelease_utility {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid)
    (w : Weights n) (hw : Nonnegative w) :
    HighProbability (fullReleaseLaw p outerUtilityConstants w) p.beta
      (fun h => AllCuts w h p.gamma ((2 : ℝ) ^ 166 * mainError n p)) := by
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  let A := (2 : ℝ) ^ 121 * boundedError n U q
  have hU : 1 ≤ U := preprocessingThreshold_one_le hn hp
  have hq : q.Valid := boundedParameters_valid hp
  have he : 0 < p.epsilon / 2 := by linarith [hp.2.2.1]
  have hb : 0 < p.beta / 2 := by linarith [hp.2.2.2.2.2.2.1]
  have hb1 : p.beta / 2 < 1 := by linarith [hp.2.2.2.2.2.2.2]
  letI := preprocessLaw_probability he (p.beta / 2) p.gamma w
  letI := cutRelease_shared_probability hn hU q hq (clipWeights U w)
  letI := fullReleaseLaw_probability hn hp w
  letI (y : Weights n) : IsProbabilityMeasure (fullReleaseContinuation p w y) :=
    fullReleaseContinuation_probability hn hp w y
  have hpre := preprocess_utility hn he hb hb1 hp.1 w hw
  have hinner := bounded_cut_release_utility hn hU q hq (clipWeights U w)
    (clipWeights_bounded (by linarith) hw)
  have hgood : MeasurableSet {y : Weights n | AllCuts w (y + clipWeights U w) (p.gamma / 2) 0} :=
    hpre.1
  have hs : MeasurableSet {h : Weights n | AllCuts w h p.gamma ((2 : ℝ) ^ 166 * mainError n p)} :=
    measurableSet_allCuts measurable_const measurable_id _ _
  have hbad : MeasurableSet {h : Weights n | ¬AllCuts w h p.gamma ((2 : ℝ) ^ 166 * mainError n p)} :=
    hs.compl
  apply highProbability_of_failure hs hp.2.2.2.2.2.2.1.le
  rw [fullReleaseLaw_eq]
  have hfail := measure_bind_le_of_good (f := fullReleaseContinuation p w)
    ((measurable_fullReleaseContinuation hn hp).comp measurable_prodMk_left) hgood hbad
    hb.le hb.le (hpre.failure_bound hb.le) (fun y hy => ?_)
  · simpa only [add_halves] using hfail
  · change (fullReleaseContinuation p w y) _ ≤ ENNReal.ofReal (p.beta / 2)
    rw [fullReleaseContinuation, Measure.map_apply (by fun_prop) hbad]
    apply le_trans (measure_mono ?_) (hinner.failure_bound hb.le)
    intro h hbad' hh
    apply hbad'
    exact (fullRelease_accuracy_add hp.1.le hy hh.2).mono_error (full_release_error_bound hn hp)

end DPCut
