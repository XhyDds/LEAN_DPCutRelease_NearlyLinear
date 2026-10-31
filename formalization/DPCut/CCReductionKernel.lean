import DPCut.CCOptimization
import DPCut.Lemma29

/-! The composed correlation-clustering reduction: private baseline, capped
residual release, independent rounding, and a public clustering solver. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

@[fun_prop] lemma measurable_ccResidual {n : ℕ} (π : Partition n) : Measurable (ccResidual π) := by
  apply measurable_pi_lambda
  intro e
  unfold ccResidual
  by_cases he : π e.val.1 = π e.val.2 <;> simp only [he, if_true, if_false] <;> fun_prop

lemma measurableSet_bounded_unit {n : ℕ} : MeasurableSet {w : Weights n | Bounded 1 w} := by
  simp only [Bounded, Set.setOf_forall]
  exact MeasurableSet.iInter fun e => (measurableSet_le measurable_const (measurable_pi_apply e)).inter
    (measurableSet_le (measurable_pi_apply e) measurable_const)

lemma measurableSet_unweighted {n : ℕ} : MeasurableSet {w : Weights n | IsUnweighted w} := by
  simp only [IsUnweighted, Set.setOf_forall]
  exact MeasurableSet.iInter fun e => (measurableSet_eq_fun (measurable_pi_apply e) measurable_const).union
    (measurableSet_eq_fun (measurable_pi_apply e) measurable_const)

def ccRoundedSolver {n : ℕ} (π₀ : Partition n) (K : Kernel (Weights n) (Partition n))
    [IsMarkovKernel K] : Kernel (Weights n) (Partition n) :=
  ⟨fun h => (bernoulliRounding (ccResidual π₀ h)).bind K,
    by
      letI : ∀ h : Weights n, IsProbabilityMeasure (bernoulliRounding (ccResidual π₀ h)) :=
        fun _ => inferInstance
      exact measurable_bind_kernel (μ := fun h => bernoulliRounding (ccResidual π₀ h))
        (bernoulliRounding.measurable.comp (measurable_ccResidual π₀))
        (K.measurable.comp measurable_snd)⟩

instance ccRoundedSolver_markov {n : ℕ} (π₀ : Partition n) (K : Kernel (Weights n) (Partition n))
    [IsMarkovKernel K] : IsMarkovKernel (ccRoundedSolver π₀ K) :=
  ⟨fun _ => probability_bind _ _ K.measurable⟩

def ccSecondStage {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    Kernel (Weights n) (Partition n) :=
  ⟨fun w => (cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w)).bind (ccRoundedSolver π₀ K),
    by
      letI : ∀ w : Weights n, IsProbabilityMeasure (cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w)) :=
        fun _ => inferInstance
      exact measurable_bind_kernel (μ := fun w => cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w))
        ((cappedReleaseKernel hn p hp Finset.univ).measurable.comp (measurable_ccResidual π₀))
        ((ccRoundedSolver π₀ K).measurable.comp measurable_snd)⟩

instance ccSecondStage_markov {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    IsMarkovKernel (ccSecondStage hn p hp π₀ K) :=
  ⟨fun _ => probability_bind _ _ (ccRoundedSolver π₀ K).measurable⟩

lemma measurable_ccSecondStage_history {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    Measurable (fun x : Weights n × Partition n => ccSecondStage hn p hp x.2 K x.1) :=
  measurable_from_prod_countable_left fun π₀ => (ccSecondStage hn p hp π₀ K).measurable

def ccPrivateKernel {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K] :
    Kernel (Weights n) (Partition n) :=
  ⟨fun w => (base w).bind (fun π₀ => ccSecondStage hn p hp π₀ K w),
    measurable_bind_kernel base.measurable (measurable_ccSecondStage_history hn p hp K)⟩

instance ccPrivateKernel_markov {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K] :
    IsMarkovKernel (ccPrivateKernel hn p hp base K) :=
  ⟨fun _ => probability_bind _ _ (measurable_of_finite _)⟩

lemma ccSecondStage_private {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {w w' : Weights n} (hw : Adjacent w w') :
    Indistinguishable (ccSecondStage hn p hp π₀ K w) (ccSecondStage hn p hp π₀ K w')
      p.epsilon p.delta := by
  have hres : Adjacent (ccResidual π₀ w) (ccResidual π₀ w') := by
    simpa only [Adjacent, ccResidual_distance] using hw
  have hpriv := cappedRelease_private hn p hp.privacyValid _ _ (supportMask Finset.univ)
    (supportMask_isMask Finset.univ) hres
  change Indistinguishable (cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w))
    (cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w')) p.epsilon p.delta at hpriv
  have h := hpriv.bind_approx hp.2.2.1.le (le_refl 0) hp.2.2.2.2.1.le (le_refl 0)
    (ccRoundedSolver π₀ K).measurable (ccRoundedSolver π₀ K).measurable
    (fun h => Indistinguishable.of_eq (μ := ccRoundedSolver π₀ K h) rfl (le_refl 0) (le_refl 0))
  simpa only [add_zero] using h

theorem ccPrivateKernel_private {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K]
    {ε₀ δ₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hδ₀ : 0 ≤ δ₀)
    (hbase : DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') base ε₀ δ₀) :
    DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w')
      (ccPrivateKernel hn p hp base K) (ε₀ + p.epsilon) (δ₀ + p.delta) := by
  intro w w' hw
  have hrev : Adjacent w' w := by
    simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2
  have hb : Indistinguishable (base w) (base w') ε₀ δ₀ :=
    ⟨hbase w w' hw, hbase w' w ⟨hw.2.1, hw.1, hrev⟩⟩
  exact (hb.bind_approx hε₀ hp.2.2.1.le hδ₀ hp.2.2.2.2.1.le
    (measurable_of_finite _) (measurable_of_finite _)
    (fun π₀ => ccSecondStage_private hn p hp π₀ K hw.2.2)).1

end DPCut
