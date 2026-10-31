import DPCut.CappedLSWWitness
import DPCut.CappedReplacementTV
import DPCut.CappedReplacementBounded

/-! The capped release implemented with LSW, including reserved approximation
error, capped outputs, privacy and accuracy for the actual program law. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut.CappedLSW
attribute [local instance] Classical.propDecidable

def clamp {n : ℕ} (D : Finset (Edge n)) (h : Weights n) : Weights n :=
  fun e => min (supportMask D e) (max 0 (h e))
lemma measurable_clamp {n : ℕ} (D : Finset (Edge n)) : Measurable (clamp D) := by
  unfold clamp; fun_prop
lemma clamp_capped {n : ℕ} (D : Finset (Edge n)) (h : Weights n) : CappedOn D (clamp D h) := by
  apply belowCap_supportMask
  exact ⟨fun e => le_min (supportMask_isMask D e).1 (le_max_left _ _), fun e => min_le_left _ _⟩
lemma clamp_eq {n : ℕ} {D : Finset (Edge n)} {h : Weights n} (hh : CappedOn D h) : clamp D h = h := by
  funext e
  unfold clamp supportMask
  by_cases he : e ∈ D
  · simp [he, max_eq_right (hh.1 e).1, min_eq_right (hh.1 e).2]
  · simp [he, hh.2 e he]

lemma measurableSet_cappedOn {n : ℕ} (D : Finset (Edge n)) :
    MeasurableSet {h : Weights n | CappedOn D h} := by
  have heq : {h : Weights n | CappedOn D h} = {h | BelowCap (supportMask D) h} := by
    ext h
    constructor
    · intro hh
      refine ⟨fun e => (hh.1 e).1, fun e => ?_⟩
      by_cases he : e ∈ D
      · simpa [supportMask, he] using (hh.1 e).2
      · simp [supportMask, he, hh.2 e he]
    · exact belowCap_supportMask D
  rw [heq]
  exact measurableSet_belowCap _

variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def run (D : Finset (Edge n)) (w : Weights n) : CostedLaw (Weights n) :=
  (CappedReplacement.costedRelease (witness F hn p hp) (precisionParameters p) (supportMask D) w).map
    (clamp D) (vectorBlockCost n)

lemma run_law (D : Finset (Edge n)) (w : Weights n) :
    (run F hn p hp D w).law =
      (CappedReplacement.outerLoop (witnessKernel F hn p hp) (precisionParameters p) (config n p)
        w (config n p).T1 (supportMask D) 0).map (clamp D) := by
  rw [run, CostedLaw.map_law, CappedReplacement.costedRelease_law _ (witnessKernel F hn p hp) (fun _ _ => rfl)]
  rfl

lemma measurable_run (D : Finset (Edge n)) : Measurable (fun w => (run F hn p hp D w).law) := by
  simp_rw [run_law]
  exact (Measure.measurable_map _ (measurable_clamp D)).comp
    (CappedReplacement.measurable_outerLoop (witnessKernel F hn p hp) _ _
      (cappedConfig_inner_utility_bounds hn _ (precisionParameters_valid hp)).eps2_pos _
      measurable_id measurable_const measurable_const)

instance run_probability (D : Finset (Edge n)) (w : Weights n) : IsProbabilityMeasure (run F hn p hp D w).law := by
  rw [run_law]
  letI := CappedReplacement.outerLoop_probability (witnessKernel F hn p hp) (precisionParameters p) (config n p)
    (cappedConfig_inner_utility_bounds hn _ (precisionParameters_valid hp)).eps2_pos w (config n p).T1 (supportMask D) 0
  exact Measure.isProbabilityMeasure_map (measurable_clamp D).aemeasurable

def kernel (D : Finset (Edge n)) : Kernel (Weights n) (Weights n) :=
  ⟨fun w => (run F hn p hp D w).law, measurable_run F hn p hp D⟩
instance kernel_markov (D : Finset (Edge n)) : IsMarkovKernel (kernel F hn p hp D) :=
  ⟨run_probability F hn p hp D⟩

lemma run_capped (D : Finset (Edge n)) (w : Weights n) :
    ∀ᵐ h ∂(run F hn p hp D w).law, CappedOn D h := by
  rw [run_law]
  apply (ae_map_iff (measurable_clamp D).aemeasurable (measurableSet_cappedOn D)).mpr
  exact Filter.Eventually.of_forall (clamp_capped D)

lemma run_tv (D : Finset (Edge n)) (w : Weights n) (hw : CappedOn D w) :
    TVClose (run F hn p hp D w).law (cappedReleaseLaw (precisionParameters p) (supportMask D) w)
      (implementationTV p) := by
  let q := precisionParameters p
  have hq := precisionParameters_valid hp
  let c := config n p
  have ho := oracle_bounds hn hp
  have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
  let H := OracleReplacement.boundedKernel hn c.oracle hl ho.eps_pos (objectiveBound n)
  have hKH : ∀ z, TVClose (witnessKernel F hn p hp z) (H z) (witnessError n p) :=
    fun z => witness_tv F hn p hp z.1 z.2
  have he := (cappedConfig_inner_utility_bounds hn q hq).eps2_pos
  have ht := CappedReplacement.outerLoop_tv (witnessKernel F hn p hp) H
    (witnessError_nonneg n p) hKH q c he w c.T1 (supportMask D) 0
  have hB : (2+q.gamma)*(Fintype.card (Edge n):ℝ) ≤ objectiveBound n := by
    unfold objectiveBound
    have hg := hq.2.1
    nlinarith [Nat.cast_nonneg (α:=ℝ) (Fintype.card (Edge n))]
  have href := CappedReplacement.outerLoop_bounded_eq hn q c ho H hq.1.le hB
    (fun _ _ hh => OracleReplacement.boundedKernel_eq hn c.oracle hl ho.eps_pos hh)
    (capped_stop_nonneg hn q hq) hw.1 c.T1 (supportMask D) 0 (supportMask_isMask D)
  rw [href] at ht
  have hclose := ht.mono (total_error hp)
  have hm : (cappedReleaseLaw q (supportMask D) w).map (clamp D) = cappedReleaseLaw q (supportMask D) w := by
    calc
      _ = (cappedReleaseLaw q (supportMask D) w).map id :=
        Measure.map_congr (((lemma29_explicit hn D q hq).2 w hw).1.mono (fun _ hh => clamp_eq hh))
      _ = _ := Measure.map_id
  change TVClose (CappedReplacement.outerLoop (witnessKernel F hn p hp) q c w c.T1 (supportMask D) 0)
    (cappedReleaseLaw q (supportMask D) w) (implementationTV p) at hclose
  rw [run_law]
  simpa only [hm] using hclose.map (measurable_clamp D)

lemma run_private (D : Finset (Edge n)) :
    DP (fun w w' => CappedOn D w ∧ CappedOn D w' ∧ Adjacent w w')
      (kernel F hn p hp D) p.epsilon p.delta := by
  intro w w' hw s hs
  let q := precisionParameters p
  have hq := precisionParameters_valid hp
  let hc := cappedConfig_inner_utility_bounds hn q hq
  letI : IsProbabilityMeasure (cappedReleaseLaw q (supportMask D) w) :=
    cappedOuterLoop_probability hn q _ hc.oracle_privacy hc.eps2_pos w _ _ _
  letI : IsProbabilityMeasure (cappedReleaseLaw q (supportMask D) w') :=
    cappedOuterLoop_probability hn q _ hc.oracle_privacy hc.eps2_pos w' _ _ _
  have hi := cappedRelease_private hn q hq.privacyValid w w' (supportMask D) (supportMask_isMask D) hw.2.2
  have ht := hi.tv_transfer hq.2.2.2.2.1.le
    (run_tv F hn p hp D w hw.1) (run_tv F hn p hp D w' hw.2.1)
  exact (ht.1 s hs).trans (add_le_add_left (ENNReal.ofReal_le_ofReal implementationTV_privacy) _)

lemma run_utility (D : Finset (Edge n)) (w : Weights n) (hw : CappedOn D w) :
    HighProbability (run F hn p hp D w).law p.beta
      (fun h => AllCuts w h p.gamma ((2:ℝ)^138 * mainError n p)) := by
  let q := precisionParameters p
  have hq := precisionParameters_valid hp
  let hc := cappedConfig_inner_utility_bounds hn q hq
  letI : IsProbabilityMeasure (cappedReleaseLaw q (supportMask D) w) :=
    cappedOuterLoop_probability hn q _ hc.oracle_privacy hc.eps2_pos w _ _ _
  have herr : (2:ℝ)^126 * mainError n q ≤ (2:ℝ)^138 * mainError n p := by
    have h := mul_le_mul_of_nonneg_left (precision_mainError_le hn hp) (by positivity : (0:ℝ)≤2^126)
    have h0 := mainError_one_le hn hp
    norm_num at h ⊢
    nlinarith
  have hgood := (((lemma29_explicit hn D q hq).2 w hw).2).mono _
    (measurableSet_allCuts measurable_const measurable_id _ _) (fun _ hh => hh.mono_error herr)
  apply (hgood.tv_transfer (run_tv F hn p hp D w hw)).weaken
  change p.beta/2 + implementationTV p ≤ p.beta
  unfold implementationTV
  linarith [min_le_left (p.beta/2) (p.delta/(2*(1+Real.exp p.epsilon)))]

def costBound (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  CappedReplacement.costBound (witnessCost F n p) n (precisionParameters p) + vectorBlockCost n
lemma run_cost (D : Finset (Edge n)) (w : Weights n) :
    (run F hn p hp D w).cost ≤ costBound F n p :=
  add_le_add_right (CappedReplacement.costedRelease_cost (witness F hn p hp) (witnessCost F n p)
    (witness_cost F hn p hp) (precisionParameters p) _ _) _

end DPCut.CappedLSW
