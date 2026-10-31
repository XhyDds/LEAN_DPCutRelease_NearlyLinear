import DPCut.CappedCalibration

/-! Lemma 29: the actual capped mechanism, its privacy, output support and
exponent-seven error with a universal multiplicative constant. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def cappedReleaseKernel {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (D : Finset (Edge n)) : Kernel (Weights n) (Weights n) :=
  ⟨cappedReleaseLaw p (supportMask D),
    measurable_cappedOuterLoop hn p _ (cappedConfig_inner_utility_bounds hn p hp).oracle_privacy
      (cappedConfig_inner_utility_bounds hn p hp).eps2_pos _ measurable_id measurable_const measurable_const⟩

instance cappedReleaseKernel_markov {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (D : Finset (Edge n)) : IsMarkovKernel (cappedReleaseKernel hn p hp D) := by
  constructor
  intro w
  exact cappedOuterLoop_probability hn p _ (cappedConfig_inner_utility_bounds hn p hp).oracle_privacy
    (cappedConfig_inner_utility_bounds hn p hp).eps2_pos w _ _ _

theorem lemma29_explicit {n : ℕ} (hn : 2 ≤ n) (D : Finset (Edge n))
    (p : Parameters) (hp : p.Valid) :
    let M := cappedReleaseKernel hn p hp D
    DP (fun w w' => CappedOn D w ∧ CappedOn D w' ∧ Adjacent w w') M p.epsilon p.delta ∧
    ∀ w, CappedOn D w → (∀ᵐ h ∂M w, CappedOn D h) ∧
      HighProbability (M w) p.beta (fun h => AllCuts w h p.gamma ((2 : ℝ) ^ 126 * mainError n p)) := by
  constructor
  · intro w w' hw s hs
    exact (cappedRelease_private hn p hp.privacyValid w w' (supportMask D) (supportMask_isMask D) hw.2.2).1 s hs
  · intro w hw
    constructor
    · have hc := cappedConfig_inner_utility_bounds hn p hp
      have hcap := cappedOuterLoop_belowCap hn p _ hc.oracle_privacy hc.eps2_pos
        (capped_stop_nonneg hn p hp) w (supportMask D) (cappedRunConfig n p).T1
        (supportMask D) 0 (supportMask_isMask D)
        (by intro e; simp) (by intro e; simp)
      exact hcap.mono fun _ hh => belowCap_supportMask D hh
    · exact HighProbability.mono _ (cappedRelease_utility_explicit hn p hp D w hw)
        (measurableSet_allCuts measurable_const measurable_id _ _)
        (fun _ hh => hh.mono_error (cappedRelease_error_bound hn p hp))

lemma capped_log_two_le {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    2 ≤ logFactor n 1 p := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hg := hp.1
  have he := hp.2.2.1
  have hd := hp.2.2.2.2.1
  have hb := hp.2.2.2.2.2.2.1
  have hgb : p.gamma * p.epsilon ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hp.2.2.2.1 hg.le
    linarith [hp.2.1]
  have hdb : p.delta * p.beta ≤ 1 / 10 := by
    have h := mul_le_of_le_one_right hd.le (show p.beta ≤ 1 by linarith [hp.2.2.2.2.2.2.2])
    linarith [hp.2.2.2.2.2.1]
  have hden : p.delta * p.beta * p.gamma * p.epsilon ≤ 1 / 10 := by
    nlinarith [mul_le_mul_of_nonneg_left hgb (mul_nonneg hd.le hb.le)]
  have harg : (8 : ℝ) ≤ n * 1 / (p.delta * p.beta * p.gamma * p.epsilon) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8) harg
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1
    norm_num
  change 2 ≤ Real.log (n * 1 / (p.delta * p.beta * p.gamma * p.epsilon))
  rw [heq] at hlog
  linarith [Real.log_two_gt_d9]

theorem lemma29 : CappedReleaseStatement := by
  refine ⟨(2 : ℝ) ^ 126, by positivity, ?_⟩
  intro n hn D p hp
  exact ⟨cappedReleaseKernel hn p hp D, inferInstance, lemma29_explicit hn D p hp⟩

end DPCut
