import DPCut.LSWWitness
import DPCut.BoundedObjectiveRelease

/-! The release program with the LSW-derived randomized approximate solver.
The reference-law equality uses the public mass cap on every adaptive history. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.LSWRelease

lemma bounded_fullRelease_eq {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (w : Weights n) (hw : Nonnegative w) :
    let c := fullRunConfig n p
    let ho := (outerConfig_inner_utility_bounds hn (preprocessingThreshold_one_le hn hp)
      (boundedParameters p) (boundedParameters_valid hp)).oracle_privacy
    OracleReplacement.fullRelease
      (OracleReplacement.boundedKernel hn c.oracle (lt_of_lt_of_le (by norm_num : (0:ℝ)<8) ho.lam_lower) ho.eps_pos (publicObjectiveBound n p)) p w =
      fullReleaseLaw p outerUtilityConstants w := by
  dsimp only
  let c := fullRunConfig n p
  have ho : OraclePrivacyBounds n c.oracle := (outerConfig_inner_utility_bounds hn
    (preprocessingThreshold_one_le hn hp) (boundedParameters p) (boundedParameters_valid hp)).oracle_privacy
  have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
  unfold OracleReplacement.fullRelease fullReleaseLaw cutReleaseLaw
  dsimp only
  congr 1
  funext y
  congr 1
  apply OracleReplacement.outerLoop_bounded_eq hn c.oracle hl ho.eps_pos _ _ c rfl ho
    (boundedParameters_valid hp).1.le (full_massCap_nonneg hn hp) (le_refl _) _
    (clipWeights_bounded (by linarith [preprocessingThreshold_one_le hn hp]) hw) _ _ _ (by intro e; simp)
  intro D r hD
  exact OracleReplacement.boundedKernel_eq hn c.oracle hl ho.eps_pos hD

variable (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def run (w : Weights n) : CostedLaw (Weights n) :=
  .charge (vectorBlockCost n)
    ((OracleReplacement.costedFullRelease (witness F hn p hp) (precisionParameters p) w).map
      positiveWeights (vectorBlockCost n))

lemma run_law (w : Weights n) : (run F hn p hp w).law =
    (OracleReplacement.fullRelease (witnessKernel F hn p hp) (precisionParameters p) w).map positiveWeights := by
  simp only [run, CostedLaw.charge_law, CostedLaw.map_law]
  congr 1
  exact OracleReplacement.costedFullRelease_law _ _ (fun _ _ => rfl) _ w

lemma measurable_run : Measurable (fun w => (run F hn p hp w).law) := by
  simp_rw [run_law F hn p hp]
  exact (Measure.measurable_map _ measurable_positiveWeights).comp
    (OracleReplacement.measurable_fullRelease _ hn (precisionParameters_valid hp))

instance run_probability (w : Weights n) : IsProbabilityMeasure (run F hn p hp w).law := by
  rw [run_law]
  letI := OracleReplacement.fullRelease_probability (witnessKernel F hn p hp) hn (precisionParameters_valid hp) w
  exact Measure.isProbabilityMeasure_map measurable_positiveWeights.aemeasurable

def kernel : Kernel (Weights n) (Weights n) := ⟨fun w => (run F hn p hp w).law, measurable_run F hn p hp⟩
instance kernel_markov : IsMarkovKernel (kernel F hn p hp) := ⟨run_probability F hn p hp⟩

lemma run_nonnegative (w : Weights n) : ∀ᵐ h ∂(run F hn p hp w).law, Nonnegative h := by
  rw [run_law]
  apply (ae_map_iff measurable_positiveWeights.aemeasurable (measurableSet_nonnegative measurable_id)).mpr
  exact Filter.Eventually.of_forall positiveWeights_nonnegative

lemma run_tv (w : Weights n) (hw : Nonnegative w) :
    TVClose (run F hn p hp w).law
      (fullReleaseLaw (precisionParameters p) outerUtilityConstants w) (implementationTV p) := by
  let c := fullRunConfig n (precisionParameters p)
  have ho : OraclePrivacyBounds n c.oracle := approxConfig_bounds hn hp
  have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
  let K := witnessKernel F hn p hp
  let H := OracleReplacement.boundedKernel hn c.oracle hl ho.eps_pos
    (publicObjectiveBound n (precisionParameters p))
  let η : ℝ := c.oracle.K * (2 * Real.sqrt c.oracle.k * approximationRadius n p)
  have hη : 0 ≤ η := by have := (approximationRadius_bounds (n:=n) hp).1; dsimp [η]; positivity
  have hKH : ∀ q, TVClose (K q) (H q) η := by
    intro q
    change TVClose (witness F hn p hp q.1 q.2).law
      (findWitness c.oracle (boundedObjective (publicObjectiveBound n (precisionParameters p)) q.1) q.2) η
    exact witness_tv F hn p hp q.1 q.2
  have ht := OracleReplacement.fullRelease_tv K H hη hKH hn (precisionParameters p) (precisionParameters_valid hp) w
  have hsqrt : Real.sqrt c.oracle.k ≤ c.oracle.k+1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg c.oracle.k)
    have h0 := Real.sqrt_nonneg (c.oracle.k:ℝ)
    nlinarith [sq_nonneg (Real.sqrt c.oracle.k - 1), (Nat.cast_nonneg c.oracle.k : (0:ℝ)≤c.oracle.k)]
  have hbudget : (c.T1:ℝ) * (c.T2 * ((Fintype.card (Edge n):ℝ) * (2*η))) ≤
      approximationBudget n p * approximationRadius n p := by
    have hr := (approximationRadius_bounds (n:=n) hp).1
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p by positivity)
    calc
      _ = (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p) * Real.sqrt c.oracle.k := by
        dsimp only [η]; ring
      _ ≤ (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p) * (c.oracle.k+1) := hh
      _ = _ := by
        change _ = (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*(c.oracle.k+1)) * approximationRadius n p
        ring
  have hclose := ht.mono (hbudget.trans (approximationBudget_error hp))
  have heq := bounded_fullRelease_eq hn (precisionParameters p) (precisionParameters_valid hp) w hw
  change OracleReplacement.fullRelease H (precisionParameters p) w = _ at heq
  rw [heq] at hclose
  have hmap : (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map positiveWeights =
      fullReleaseLaw (precisionParameters p) outerUtilityConstants w := by
    calc
      _ = (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map id :=
        Measure.map_congr ((fullReleaseLaw_nonnegative hn (precisionParameters_valid hp) w).mono
          (fun _ hh => positiveWeights_eq hh))
      _ = _ := Measure.map_id
  rw [run_law]
  simpa only [hmap] using hclose.map measurable_positiveWeights

lemma run_private : EdgeDP (fun w => (run F hn p hp w).law) p.epsilon p.delta := by
  intro w w' hw s hs
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w'
  have hsymm : Nonnegative w' ∧ Nonnegative w ∧ Adjacent w' w := by
    refine ⟨hw.2.1, hw.1, ?_⟩
    simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2
  have hi : Indistinguishable (fullReleaseLaw (precisionParameters p) outerUtilityConstants w)
      (fullReleaseLaw (precisionParameters p) outerUtilityConstants w') p.epsilon (p.delta/2) :=
    ⟨fullRelease_private hn (precisionParameters_valid hp) w w' hw,
      fullRelease_private hn (precisionParameters_valid hp) w' w hsymm⟩
  have ht := hi.tv_transfer (by linarith [hp.2.2.2.2.1])
    (run_tv F hn p hp w hw.1) (run_tv F hn p hp w' hw.2.1)
  exact (ht.1 s hs).trans (add_le_add_left (ENNReal.ofReal_le_ofReal implementationTV_privacy) _)

lemma run_utility (w : Weights n) (hw : Nonnegative w) :
    HighProbability (run F hn p hp w).law p.beta
      (fun h => AllCuts w h p.gamma ((2:ℝ)^178 * mainError n p)) := by
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  have hlarge := (fullRelease_utility hn (precisionParameters_valid hp) w hw).mono _
    (measurableSet_allCuts measurable_const measurable_id _ _) (fun h hh => hh.mono_error (precision_error_le hn hp))
  apply (hlarge.tv_transfer (run_tv F hn p hp w hw)).weaken
  change p.beta/2 + implementationTV p ≤ p.beta
  have hm := min_le_left (p.beta/2) (p.delta/(2*(1+Real.exp p.epsilon)))
  unfold implementationTV
  linarith

end DPCut.LSWRelease
