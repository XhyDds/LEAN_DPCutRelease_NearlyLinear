import DPCut.CappedLSWRelease
import DPCut.CCReductionUtility

/-! Correlation clustering using the implemented approximate capped release.
Privacy and utility below refer to this program's actual law. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.LSWApplications
attribute [local instance] Classical.propDecidable

def ccSecondStage {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    Kernel (Weights n) (Partition n) :=
  ⟨fun w => (CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w)).bind (ccRoundedSolver π₀ K),
    by
      letI : ∀ w : Weights n, IsProbabilityMeasure (CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w)) :=
        fun _ => inferInstance
      exact measurable_bind_kernel (μ := fun w => CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w))
        ((CappedLSW.kernel F hn p hp Finset.univ).measurable.comp (measurable_ccResidual π₀))
        ((ccRoundedSolver π₀ K).measurable.comp measurable_snd)⟩

instance ccSecondStage_markov {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    IsMarkovKernel (ccSecondStage F hn p hp π₀ K) :=
  ⟨fun _ => probability_bind _ _ (ccRoundedSolver π₀ K).measurable⟩

lemma measurable_ccSecondStage_history {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K] :
    Measurable (fun x : Weights n × Partition n => ccSecondStage F hn p hp x.2 K x.1) :=
  measurable_from_prod_countable_left fun π₀ => (ccSecondStage F hn p hp π₀ K).measurable

def ccPrivateKernel {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K] :
    Kernel (Weights n) (Partition n) :=
  ⟨fun w => (base w).bind (fun π₀ => ccSecondStage F hn p hp π₀ K w),
    measurable_bind_kernel base.measurable (measurable_ccSecondStage_history F hn p hp K)⟩

instance ccPrivateKernel_markov {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K] :
    IsMarkovKernel (ccPrivateKernel F hn p hp base K) :=
  ⟨fun _ => probability_bind _ _ (measurable_of_finite _)⟩

lemma ccSecondStage_private {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {w w' : Weights n} (hw : Bounded 1 w) (hw' : Bounded 1 w') (ha : Adjacent w w') :
    Indistinguishable (ccSecondStage F hn p hp π₀ K w) (ccSecondStage F hn p hp π₀ K w')
      p.epsilon p.delta := by
  have hres : Adjacent (ccResidual π₀ w) (ccResidual π₀ w') := by
    simpa only [Adjacent, ccResidual_distance] using ha
  have hwcap : CappedOn Finset.univ (ccResidual π₀ w) :=
    ⟨ccResidual_bounded π₀ hw, fun e he => False.elim (he (Finset.mem_univ e))⟩
  have hwcap' : CappedOn Finset.univ (ccResidual π₀ w') :=
    ⟨ccResidual_bounded π₀ hw', fun e he => False.elim (he (Finset.mem_univ e))⟩
  have hrev : Adjacent (ccResidual π₀ w') (ccResidual π₀ w) := by
    simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hres
  have hpriv : Indistinguishable (CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w))
      (CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w')) p.epsilon p.delta :=
    ⟨CappedLSW.run_private F hn p hp Finset.univ _ _ ⟨hwcap,hwcap',hres⟩,
      CappedLSW.run_private F hn p hp Finset.univ _ _ ⟨hwcap',hwcap,hrev⟩⟩
  have h := hpriv.bind_approx hp.2.2.1.le (le_refl 0) hp.2.2.2.2.1.le (le_refl 0)
    (ccRoundedSolver π₀ K).measurable (ccRoundedSolver π₀ K).measurable
    (fun h => Indistinguishable.of_eq (μ := ccRoundedSolver π₀ K h) rfl (le_refl 0) (le_refl 0))
  simpa only [add_zero] using h

theorem ccPrivateKernel_private {n : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (base K : Kernel (Weights n) (Partition n)) [IsMarkovKernel base] [IsMarkovKernel K]
    {ε₀ δ₀ : ℝ} (hε₀ : 0 ≤ ε₀) (hδ₀ : 0 ≤ δ₀)
    (hbase : DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') base ε₀ δ₀) :
    DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w')
      (ccPrivateKernel F hn p hp base K) (ε₀ + p.epsilon) (δ₀ + p.delta) := by
  intro w w' hw
  have hrev : Adjacent w' w := by
    simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2
  have hb : Indistinguishable (base w) (base w') ε₀ δ₀ :=
    ⟨hbase w w' hw, hbase w' w ⟨hw.2.1, hw.1, hrev⟩⟩
  exact (hb.bind_approx hε₀ hp.2.2.1.le hδ₀ hp.2.2.2.2.1.le
    (measurable_of_finite _) (measurable_of_finite _)
    (fun π₀ => ccSecondStage_private F hn p hp π₀ K hw.1.bounded hw.2.1.bounded hw.2.2)).1

theorem ccSecondStage_utility {n k : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (p : Parameters) (hp : p.Valid) (π₀ : Partition n)
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {w : Weights n} {c A₀ η β τ ρ : ℝ}
    (hw : Bounded 1 w) (hc : 0 ≤ c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hθ : ccTransferTheta c p.gamma η < 1)
    (hbase : ccCost w π₀ ≤ c * ccOptimum w + A₀)
    (hK : ∀ j, IsUnweighted j → HighProbability (K j) τ
      (fun π => clusterCount π ≤ k ∧ ccCost j π ≤ ρ * ccOptimumK j k)) :
    HighProbability (ccSecondStage F hn p hp π₀ K w) (p.beta + (β + τ))
      (CCTransferredGood w k ρ (ccTransferTheta c p.gamma η)
        (ccTransferError n p.gamma η A₀ ((2 : ℝ) ^ 138 * mainError n p) β)) := by
  have hinput : CappedOn Finset.univ (ccResidual π₀ w) :=
    ⟨ccResidual_bounded π₀ hw, fun e he => False.elim (he (Finset.mem_univ e))⟩
  have hcap := CappedLSW.run_capped F hn p hp Finset.univ (ccResidual π₀ w)
  have hcut := CappedLSW.run_utility F hn p hp Finset.univ (ccResidual π₀ w) hinput
  have hh : ∀ᵐ h ∂CappedLSW.kernel F hn p hp Finset.univ (ccResidual π₀ w), Bounded 1 h :=
    hcap.mono fun _ hh => hh.1
  have hboth := hcut.and_ae measurableSet_bounded_unit hh
  apply hboth.bind (ccRoundedSolver π₀ K) hp.2.2.2.2.2.2.1.le (add_nonneg hβ.le hτ)
    (Set.toFinite _ |>.measurableSet)
  intro h hh
  exact ccRoundedSolver_utility hn hk π₀ K hw hh.2 hp.1.le hc hη hη1 hβ hβ1 hτ hρ hθ hbase hh.1 hK

theorem ccPrivateKernel_utility {n k : ℕ} (F : CuttingPlaneFamily) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (p : Parameters) (hp : p.Valid) (base K : Kernel (Weights n) (Partition n))
    [IsMarkovKernel base] [IsMarkovKernel K]
    {w : Weights n} {c A₀ η β τ ρ β₀ : ℝ}
    (hw : Bounded 1 w) (hc : 0 ≤ c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hβ₀ : 0 ≤ β₀)
    (hθ : ccTransferTheta c p.gamma η < 1)
    (hbase : HighProbability (base w) β₀ (fun π₀ => ccCost w π₀ ≤ c * ccOptimum w + A₀))
    (hK : ∀ j, IsUnweighted j → HighProbability (K j) τ
      (fun π => clusterCount π ≤ k ∧ ccCost j π ≤ ρ * ccOptimumK j k)) :
    HighProbability (ccPrivateKernel F hn p hp base K w) (β₀ + (p.beta + (β + τ)))
      (CCTransferredGood w k ρ (ccTransferTheta c p.gamma η)
        (ccTransferError n p.gamma η A₀ ((2 : ℝ) ^ 138 * mainError n p) β)) := by
  let J : Kernel (Partition n) (Partition n) :=
    ⟨fun π₀ => ccSecondStage F hn p hp π₀ K w, measurable_of_finite _⟩
  letI : IsMarkovKernel J := ⟨fun π₀ =>
    inferInstanceAs (IsProbabilityMeasure (ccSecondStage F hn p hp π₀ K w))⟩
  apply hbase.bind J hβ₀ (add_nonneg hp.2.2.2.2.2.2.1.le (add_nonneg hβ.le hτ))
    (Set.toFinite _ |>.measurableSet)
  intro π₀ hπ₀
  exact ccSecondStage_utility F hn hk p hp π₀ K hw hc hη hη1 hβ hβ1 hτ hρ hθ hπ₀ hK


end DPCut.LSWApplications
