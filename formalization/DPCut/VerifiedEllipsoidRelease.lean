import DPCut.VerifiedEllipsoidWitness

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.VerifiedRelease

variable {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def release (w : Weights n) : Measure (Weights n) :=
  (OracleReplacement.fullRelease (witnessKernel hn p hp) (precisionParameters p) w).map positiveWeights

@[fun_prop] theorem measurable_release : Measurable (release hn p hp) :=
  (Measure.measurable_map _ measurable_positiveWeights).comp
    (OracleReplacement.measurable_fullRelease _ hn (precisionParameters_valid hp))

instance release_probability (w : Weights n) : IsProbabilityMeasure (release hn p hp w) := by
  letI := OracleReplacement.fullRelease_probability (witnessKernel hn p hp) hn (precisionParameters_valid hp) w
  exact Measure.isProbabilityMeasure_map measurable_positiveWeights.aemeasurable

theorem release_nonnegative (w : Weights n) : ∀ᵐ h ∂release hn p hp w, Nonnegative h := by
  apply (ae_map_iff measurable_positiveWeights.aemeasurable (measurableSet_nonnegative measurable_id)).mpr
  exact Filter.Eventually.of_forall positiveWeights_nonnegative

theorem release_tv (w : Weights n) (hw : Nonnegative w) :
    TVClose (release hn p hp w) (fullReleaseLaw (precisionParameters p) outerUtilityConstants w) (implementationTV p) := by
  let c := fullRunConfig n (precisionParameters p)
  have ho := approxConfig_bounds hn hp
  have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
  let K := witnessKernel hn p hp
  let H := OracleReplacement.boundedKernel hn c.oracle hl ho.eps_pos
    (publicObjectiveBound n (precisionParameters p))
  let eta : ℝ := c.oracle.K * (2*Real.sqrt c.oracle.k*approximationRadius n p)
  have heta : 0 ≤ eta := by
    have h := (approximationRadius_bounds (n:=n) hp).1
    dsimp [eta]
    positivity
  have hKH : ∀ q, TVClose (K q) (H q) eta := fun q => witness_tv hn p hp q.1 q.2
  have ht := OracleReplacement.fullRelease_tv K H heta hKH hn (precisionParameters p) (precisionParameters_valid hp) w
  have hsqrt : Real.sqrt c.oracle.k ≤ c.oracle.k+1 := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg c.oracle.k)
    have h0 := Real.sqrt_nonneg (c.oracle.k:ℝ)
    nlinarith [sq_nonneg (Real.sqrt c.oracle.k-1), (Nat.cast_nonneg c.oracle.k : (0:ℝ)≤c.oracle.k)]
  have hbudget : (c.T1:ℝ)*(c.T2*((Fintype.card (Edge n):ℝ)*(2*eta))) ≤
      approximationBudget n p*approximationRadius n p := by
    have hr := (approximationRadius_bounds (n:=n) hp).1.le
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (show 0 ≤ 4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p by positivity)
    calc
      _ = (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p)*Real.sqrt c.oracle.k := by
        dsimp only [eta]
        ring
      _ ≤ (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*approximationRadius n p)*(c.oracle.k+1) := hh
      _ = _ := by
        change _ = (4*(Fintype.card (Edge n):ℝ)*c.T1*c.T2*c.oracle.K*(c.oracle.k+1))*approximationRadius n p
        ring
  have hclose := ht.mono (hbudget.trans (approximationBudget_error hp))
  have heq := LSWRelease.bounded_fullRelease_eq hn (precisionParameters p) (precisionParameters_valid hp) w hw
  change OracleReplacement.fullRelease H (precisionParameters p) w = _ at heq
  rw [heq] at hclose
  have hmap : (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map positiveWeights =
      fullReleaseLaw (precisionParameters p) outerUtilityConstants w := by
    calc
      _ = (fullReleaseLaw (precisionParameters p) outerUtilityConstants w).map id :=
        Measure.map_congr ((fullReleaseLaw_nonnegative hn (precisionParameters_valid hp) w).mono
          (fun _ hh => positiveWeights_eq hh))
      _ = _ := Measure.map_id
  simpa only [hmap] using hclose.map measurable_positiveWeights

theorem release_private : EdgeDP (release hn p hp) p.epsilon p.delta := by
  intro w w' hw s hs
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w'
  have hsymm : Nonnegative w' ∧ Nonnegative w ∧ Adjacent w' w := by
    refine ⟨hw.2.1,hw.1,?_⟩
    simpa only [Adjacent,l1,Pi.sub_apply,abs_sub_comm] using hw.2.2
  have hi : Indistinguishable (fullReleaseLaw (precisionParameters p) outerUtilityConstants w)
      (fullReleaseLaw (precisionParameters p) outerUtilityConstants w') p.epsilon (p.delta/2) :=
    ⟨fullRelease_private hn (precisionParameters_valid hp) w w' hw,
      fullRelease_private hn (precisionParameters_valid hp) w' w hsymm⟩
  have ht := hi.tv_transfer (by linarith [hp.2.2.2.2.1])
    (release_tv hn p hp w hw.1) (release_tv hn p hp w' hw.2.1)
  exact (ht.1 s hs).trans (add_le_add_left (ENNReal.ofReal_le_ofReal implementationTV_privacy) _)

theorem release_utility (w : Weights n) (hw : Nonnegative w) :
    HighProbability (release hn p hp w) p.beta
      (fun h => AllCuts w h p.gamma ((2:ℝ)^178*mainError n p)) := by
  letI := fullReleaseLaw_probability hn (precisionParameters_valid hp) w
  have hlarge := (fullRelease_utility hn (precisionParameters_valid hp) w hw).mono _
    (measurableSet_allCuts measurable_const measurable_id _ _) (fun h hh => hh.mono_error (precision_error_le hn hp))
  apply (hlarge.tv_transfer (release_tv hn p hp w hw)).weaken
  change p.beta/2+implementationTV p ≤ p.beta
  have h := min_le_left (p.beta/2) (p.delta/(2*(1+Real.exp p.epsilon)))
  unfold implementationTV
  linarith

end DPCut.VerifiedRelease
