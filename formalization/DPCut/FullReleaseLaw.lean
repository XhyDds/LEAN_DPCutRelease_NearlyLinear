import DPCut.MainParameters
import DPCut.SharedPrivacy

/-! A measurable, probability-valued, nonnegative full release kernel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

lemma cutRelease_shared_probability {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) (w : Weights n) :
    IsProbabilityMeasure (cutReleaseLaw U p outerUtilityConstants w) := by
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  exact outerLoop_probability hn p _ hc.oracle_privacy hc.eps2_pos w _ 1 0

lemma measurable_cutRelease_shared {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    Measurable (cutReleaseLaw (n := n) U p outerUtilityConstants) := by
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  exact measurable_outerLoop hn p _ hc.oracle_privacy hc.eps2_pos _
    measurable_id measurable_const measurable_const

lemma measurable_preprocessLaw {n : ℕ} {ε : ℝ} (hε : 0 < ε) (β γ : ℝ) :
    Measurable (preprocessLaw (n := n) ε β γ) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hε)
  apply measurable_map_kernel measurable_const
  unfold Function.uncurry noisyExcess excess
  fun_prop

lemma preprocessLaw_nonnegative {n : ℕ} (ε β γ : ℝ) (w : Weights n) :
    ∀ᵐ y ∂preprocessLaw ε β γ w, Nonnegative y := by
  apply (ae_map_iff (measurable_noisyExcess _ _ _).aemeasurable
    (measurableSet_nonnegative measurable_id)).mpr
  exact Filter.Eventually.of_forall (fun _ => noisyExcess_nonnegative _ _ _ _)

def fullReleaseContinuation {n : ℕ} (p : Parameters) (w y : Weights n) : Measure (Weights n) :=
  (cutReleaseLaw (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants
    (clipWeights (preprocessingThreshold n p) w)).map (fun h => h + y)

lemma fullReleaseLaw_eq {n : ℕ} (p : Parameters) (w : Weights n) :
    fullReleaseLaw p outerUtilityConstants w =
      (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w).bind (fullReleaseContinuation p w) := rfl

lemma fullReleaseContinuation_probability {n : ℕ} (hn : 2 ≤ n) {p : Parameters}
    (hp : p.Valid) (w y : Weights n) : IsProbabilityMeasure (fullReleaseContinuation p w y) := by
  letI := cutRelease_shared_probability hn (preprocessingThreshold_one_le hn hp)
    (boundedParameters p) (boundedParameters_valid hp) (clipWeights (preprocessingThreshold n p) w)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma measurable_fullReleaseContinuation {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    Measurable (Function.uncurry (fullReleaseContinuation (n := n) p)) := by
  let U := preprocessingThreshold n p
  let q := boundedParameters p
  letI (wy : Weights n × Weights n) :
      IsProbabilityMeasure (cutReleaseLaw U q outerUtilityConstants (clipWeights U wy.1)) :=
    cutRelease_shared_probability hn (preprocessingThreshold_one_le hn hp) q
      (boundedParameters_valid hp) _
  exact measurable_map_kernel
    (μ := fun wy : Weights n × Weights n => cutReleaseLaw U q outerUtilityConstants (clipWeights U wy.1))
    (f := fun wy h => h + wy.2)
    ((measurable_cutRelease_shared hn (preprocessingThreshold_one_le hn hp) q
      (boundedParameters_valid hp)).comp ((measurable_clipWeights U).comp measurable_fst))
    (by fun_prop)

lemma fullReleaseLaw_probability {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid)
    (w : Weights n) : IsProbabilityMeasure (fullReleaseLaw p outerUtilityConstants w) := by
  letI := preprocessLaw_probability (show 0 < p.epsilon / 2 by linarith [hp.2.2.1])
    (p.beta / 2) p.gamma w
  letI (y : Weights n) : IsProbabilityMeasure (fullReleaseContinuation p w y) :=
    fullReleaseContinuation_probability hn hp w y
  rw [fullReleaseLaw_eq]
  exact probability_bind _ _ ((measurable_fullReleaseContinuation hn hp).comp measurable_prodMk_left)

lemma measurable_fullReleaseLaw {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    Measurable (fullReleaseLaw (n := n) p outerUtilityConstants) := by
  letI := preprocessLaw_probability (n := n) (show 0 < p.epsilon / 2 by linarith [hp.2.2.1])
    (p.beta / 2) p.gamma
  exact measurable_bind_kernel
    (measurable_preprocessLaw (by linarith [hp.2.2.1]) _ _) (measurable_fullReleaseContinuation hn hp)

def fullReleaseKernel {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    Kernel (Weights n) (Weights n) :=
  ⟨fullReleaseLaw p outerUtilityConstants, measurable_fullReleaseLaw hn hp⟩

instance fullReleaseKernel_markov {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    IsMarkovKernel (fullReleaseKernel hn p hp) := ⟨fullReleaseLaw_probability hn hp⟩

theorem fullReleaseLaw_nonnegative {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid)
    (w : Weights n) : ∀ᵐ h ∂fullReleaseLaw p outerUtilityConstants w, Nonnegative h := by
  rw [fullReleaseLaw_eq]
  apply ae_bind_of_ae_ae ((measurable_fullReleaseContinuation hn hp).comp measurable_prodMk_left)
    (measurableSet_nonnegative measurable_id)
  filter_upwards [preprocessLaw_nonnegative (p.epsilon / 2) (p.beta / 2) p.gamma w] with y hy
  apply (ae_map_iff (by fun_prop) (measurableSet_nonnegative measurable_id)).mpr
  filter_upwards [cutRelease_nonnegative hn (preprocessingThreshold_one_le hn hp)
    (boundedParameters p) (boundedParameters_valid hp) (clipWeights (preprocessingThreshold n p) w)] with h hh
  exact fun e => add_nonneg (hh e) (hy e)

end DPCut
