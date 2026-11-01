import DPCut.ApproxSDPCosted
import DPCut.ApproxSDPPrecision
import DPCut.OracleReplacementTV
import DPCut.ApplicationPostprocessing

/-! The approximate optimizer is used by the actual release program. Its output
law, measurability, probability, nonnegativity and total-variation bound are proved. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def positiveWeights {n : ℕ} (w : Weights n) : Weights n := fun e => max 0 (w e)

@[fun_prop] lemma measurable_positiveWeights {n : ℕ} : Measurable (positiveWeights (n := n)) := by
  unfold positiveWeights
  fun_prop

lemma positiveWeights_nonnegative {n : ℕ} (w : Weights n) : Nonnegative (positiveWeights w) :=
  fun _ => le_max_left _ _

lemma positiveWeights_eq {n : ℕ} {w : Weights n} (hw : Nonnegative w) : positiveWeights w = w := by
  funext e
  exact max_eq_right (hw e)

def costedApproxRelease {n : ℕ} (sdp : ApproxSDPOracle) (p : Parameters) (w : Weights n) :
    CostedLaw (Weights n) :=
  let q := precisionParameters p
  let o := (fullRunConfig n q).oracle
  .charge (vectorBlockCost n)
    ((OracleReplacement.costedFullRelease (ApproxSDPCosted.witness sdp (approximationRadius n p) o) q w).map
      positiveWeights (vectorBlockCost n))

lemma approxConfig_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    OraclePrivacyBounds n (fullRunConfig n (precisionParameters p)).oracle :=
  (outerConfig_inner_utility_bounds hn (preprocessingThreshold_one_le hn (precisionParameters_valid hp))
    (boundedParameters (precisionParameters p)) (boundedParameters_valid (precisionParameters_valid hp))).oracle_privacy

def approxWitnessKernel {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    OracleReplacement.WitnessKernel n :=
  sdp.witnessKernel hn (fullRunConfig n (precisionParameters p)).oracle
    (by linarith [(approxConfig_bounds hn hp).lam_lower]) (approxConfig_bounds hn hp).eps_pos
    (approximationRadius_bounds (n := n) hp).1 (approximationRadius_bounds (n := n) hp).2

instance approxWitnessKernel_markov {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) : IsMarkovKernel (approxWitnessKernel sdp hn p hp) :=
  ApproxSDPOracle.witnessKernel_markov ..

theorem costedApproxRelease_law {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) (w : Weights n) :
    (costedApproxRelease sdp p w).law =
      (OracleReplacement.fullRelease (approxWitnessKernel sdp hn p hp) (precisionParameters p) w).map
        positiveWeights := by
  simp only [costedApproxRelease, CostedLaw.charge_law, CostedLaw.map_law]
  congr 1
  apply OracleReplacement.costedFullRelease_law
  intro D r
  exact ApproxSDPCosted.witness_law sdp _ _ (approxConfig_bounds hn hp).eps_pos D r
    (feasible_posDef hn (sdp.feasible n hn _ _
      (by linarith [(approxConfig_bounds hn hp).lam_lower])
      (approximationRadius_bounds (n := n) hp).1 (approximationRadius_bounds (n := n) hp).2 D))

lemma measurable_approxRelease {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) : Measurable (fun w : Weights n => (costedApproxRelease sdp p w).law) := by
  simp_rw [costedApproxRelease_law sdp hn p hp]
  exact (Measure.measurable_map _ measurable_positiveWeights).comp
    (OracleReplacement.measurable_fullRelease _ hn (precisionParameters_valid hp))

instance approxRelease_probability {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) (w : Weights n) : IsProbabilityMeasure (costedApproxRelease sdp p w).law := by
  rw [costedApproxRelease_law sdp hn p hp]
  letI := OracleReplacement.fullRelease_probability (approxWitnessKernel sdp hn p hp) hn
    (precisionParameters_valid hp) w
  exact Measure.isProbabilityMeasure_map measurable_positiveWeights.aemeasurable

def approxReleaseKernel {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    Kernel (Weights n) (Weights n) :=
  ⟨fun w => (costedApproxRelease sdp p w).law, measurable_approxRelease sdp hn p hp⟩

instance approxReleaseKernel_markov {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) : IsMarkovKernel (approxReleaseKernel sdp hn p hp) :=
  ⟨approxRelease_probability sdp hn p hp⟩

theorem approxRelease_nonnegative {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∀ᵐ h ∂(costedApproxRelease sdp p w).law, Nonnegative h := by
  rw [costedApproxRelease_law sdp hn p hp]
  apply (ae_map_iff measurable_positiveWeights.aemeasurable (measurableSet_nonnegative measurable_id)).mpr
  exact Filter.Eventually.of_forall positiveWeights_nonnegative

theorem approxRelease_tv {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) (w : Weights n) :
    TVClose (costedApproxRelease sdp p w).law
      (fullReleaseLaw (precisionParameters p) outerUtilityConstants w) (implementationTV p) := by
  let c := fullRunConfig n (precisionParameters p)
  have ho : OraclePrivacyBounds n c.oracle := approxConfig_bounds hn hp
  have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
  obtain ⟨hμ, hμhalf⟩ := approximationRadius_bounds (n := n) hp
  let K := approxWitnessKernel sdp hn p hp
  let H := OracleReplacement.exactKernel hn c.oracle hl ho.eps_pos
  let η : ℝ := c.oracle.K * (2 * Real.sqrt c.oracle.k * approximationRadius n p)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hKH : ∀ q, TVClose (K q) (H q) η :=
    sdp.witnessKernel_tv hn c.oracle hl ho.eps_pos hμ hμhalf ho.batch_pos
  have ht := OracleReplacement.fullRelease_tv K H hη hKH hn (precisionParameters p)
    (precisionParameters_valid hp) w
  have hsqrt : Real.sqrt c.oracle.k ≤ c.oracle.k + 1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg c.oracle.k)
    have h0 := Real.sqrt_nonneg (c.oracle.k : ℝ)
    nlinarith [sq_nonneg (Real.sqrt c.oracle.k - 1),
      (Nat.cast_nonneg c.oracle.k : (0 : ℝ) ≤ c.oracle.k)]
  have hbudget : (c.T1 : ℝ) * (c.T2 * ((Fintype.card (Edge n) : ℝ) * (2 * η))) ≤
      approximationBudget n p * approximationRadius n p := by
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 4 * (Fintype.card (Edge n) : ℝ) * c.T1 * c.T2 * c.oracle.K * approximationRadius n p by positivity)
    calc
      _ = (4 * (Fintype.card (Edge n) : ℝ) * c.T1 * c.T2 * c.oracle.K * approximationRadius n p) *
          Real.sqrt c.oracle.k := by dsimp only [η]; ring
      _ ≤ (4 * (Fintype.card (Edge n) : ℝ) * c.T1 * c.T2 * c.oracle.K * approximationRadius n p) *
          (c.oracle.k + 1) := hh
      _ = _ := by
        change _ = (4 * (Fintype.card (Edge n) : ℝ) * c.T1 * c.T2 * c.oracle.K *
          (c.oracle.k + 1)) * approximationRadius n p
        ring
  have hclose := ht.mono (hbudget.trans (approximationBudget_error hp))
  have heq := OracleReplacement.fullRelease_exact hn c.oracle hl ho.eps_pos (precisionParameters p) rfl w
  change OracleReplacement.fullRelease H (precisionParameters p) w = _ at heq
  rw [heq] at hclose
  have hmap : (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map positiveWeights =
      fullReleaseLaw (precisionParameters p) outerUtilityConstants w := by
    calc
      _ = (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map id :=
        Measure.map_congr ((fullReleaseLaw_nonnegative hn (precisionParameters_valid hp) w).mono
          (fun _ hh => positiveWeights_eq hh))
      _ = _ := Measure.map_id
  rw [costedApproxRelease_law sdp hn p hp]
  simpa only [hmap] using hclose.map measurable_positiveWeights

theorem approxRelease_private {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) : EdgeDP (fun w : Weights n => (costedApproxRelease sdp p w).law)
      p.epsilon p.delta := by
  intro w w' hw s hs
  letI := approxRelease_probability sdp hn p hp w
  letI := approxRelease_probability sdp hn p hp w'
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w'
  have hsymm : Nonnegative w' ∧ Nonnegative w ∧ Adjacent w' w := by
    refine ⟨hw.2.1, hw.1, ?_⟩
    simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2
  have hi : Indistinguishable (fullReleaseLaw (precisionParameters p) outerUtilityConstants w)
      (fullReleaseLaw (precisionParameters p) outerUtilityConstants w') p.epsilon (p.delta / 2) :=
    ⟨fullRelease_private hn (precisionParameters_valid hp) w w' hw,
      fullRelease_private hn (precisionParameters_valid hp) w' w hsymm⟩
  have ht := hi.tv_transfer (by linarith [hp.2.2.2.2.1])
    (approxRelease_tv sdp hn p hp w) (approxRelease_tv sdp hn p hp w')
  exact (ht.1 s hs).trans (add_le_add_left (ENNReal.ofReal_le_ofReal implementationTV_privacy) _)

theorem approxRelease_utility {n : ℕ} (sdp : ApproxSDPOracle) (hn : 2 ≤ n)
    (p : Parameters) (hp : p.Valid) (w : Weights n) (hw : Nonnegative w) :
    HighProbability (costedApproxRelease sdp p w).law p.beta
      (fun h => AllCuts w h p.gamma ((2 : ℝ) ^ 178 * mainError n p)) := by
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  have hlarge := (fullRelease_utility hn (precisionParameters_valid hp) w hw).mono _
    (measurableSet_allCuts measurable_const measurable_id _ _) (fun h hh => hh.mono_error
      (precision_error_le hn hp))
  apply (hlarge.tv_transfer (approxRelease_tv sdp hn p hp w)).weaken
  have hm := min_le_left (p.beta / 2) (p.delta / (2 * (1 + Real.exp p.epsilon)))
  change p.beta / 2 + implementationTV p ≤ p.beta
  unfold implementationTV
  linarith

end DPCut
