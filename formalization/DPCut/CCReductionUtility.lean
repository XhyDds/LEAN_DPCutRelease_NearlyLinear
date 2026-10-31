import DPCut.CCReductionKernel

/-! The full CC reduction's accuracy, including the three post-baseline failure
budgets. It applies to the same restricted family for both CC variants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def ccTransferTheta (c γ η : ℝ) : ℝ := 9 * c * γ + η * (1 + 9 * c * γ)
def ccTransferError (n : ℕ) (γ η A₀ A β : ℝ) : ℝ :=
  (1 + η) * (9 * γ * A₀ + 18 * A) + 3 / η * (n * Real.log n + Real.log (2 / β))

def CCTransferredGood {n : ℕ} (w : Weights n) (k : ℕ) (ρ θ B : ℝ) (π : Partition n) : Prop :=
  clusterCount π ≤ k ∧ ccCost w π ≤
    ρ * (1 + θ) / (1 - θ) * ccOptimumK w k + (ρ + 1) / (1 - θ) * B

theorem ccRoundedSolver_utility {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (π₀ : Partition n) (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {w h : Weights n} {γ A c A₀ η β τ ρ : ℝ}
    (hw : Bounded 1 w) (hh : Bounded 1 h) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hη : 0 < η) (hη1 : η ≤ 1) (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hθ : ccTransferTheta c γ η < 1)
    (hbase : ccCost w π₀ ≤ c * ccOptimum w + A₀)
    (hcut : AllCuts (ccResidual π₀ w) h γ A)
    (hK : ∀ j, IsUnweighted j → HighProbability (K j) τ
      (fun π => clusterCount π ≤ k ∧ ccCost j π ≤ ρ * ccOptimumK j k)) :
    HighProbability (ccRoundedSolver π₀ K h) (β + τ)
      (CCTransferredGood w k ρ (ccTransferTheta c γ η) (ccTransferError n γ η A₀ A β)) := by
  have hp : Bounded 1 (ccResidual π₀ h) := ccResidual_bounded π₀ hh
  have hrnd := (cc_bernoulli_rounding hn hp hη hη1 hβ hβ1).and_ae
    measurableSet_unweighted (bernoulliRounding_unweighted (ccResidual π₀ h))
  apply hrnd.bind K hβ.le hτ (Set.toFinite _ |>.measurableSet)
  intro j hj
  apply HighProbability.mono _ (hK j hj.2) (Set.toFinite _ |>.measurableSet)
  intro π hπ
  refine ⟨hπ.1, ?_⟩
  have hres : ∀ π : Partition n, |ccCost (ccResidual π₀ h) π - ccCost w π| ≤
      (9 * c * γ) * ccCost w π + (9 * γ * A₀ + 18 * A) := by
    intro π
    convert cc_baseline_transfer hw hγ hcut hbase hc π using 1
    ring
  exact cc_approximation_transferK (by omega) hk hθ hρ
    (fun π => by simpa only [ccTransferTheta, ccTransferError, add_assoc] using
      cc_surrogate_transfer hη.le hres hj.1 π) hπ.2

theorem ccSecondStage_utility {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (p : Parameters) (hp : p.Valid) (π₀ : Partition n)
    (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {w : Weights n} {c A₀ η β τ ρ : ℝ}
    (hw : Bounded 1 w) (hc : 0 ≤ c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hθ : ccTransferTheta c p.gamma η < 1)
    (hbase : ccCost w π₀ ≤ c * ccOptimum w + A₀)
    (hK : ∀ j, IsUnweighted j → HighProbability (K j) τ
      (fun π => clusterCount π ≤ k ∧ ccCost j π ≤ ρ * ccOptimumK j k)) :
    HighProbability (ccSecondStage hn p hp π₀ K w) (p.beta + (β + τ))
      (CCTransferredGood w k ρ (ccTransferTheta c p.gamma η)
        (ccTransferError n p.gamma η A₀ ((2 : ℝ) ^ 126 * mainError n p) β)) := by
  have hinput : CappedOn Finset.univ (ccResidual π₀ w) :=
    ⟨ccResidual_bounded π₀ hw, fun e he => False.elim (he (Finset.mem_univ e))⟩
  obtain ⟨hcap, hcut⟩ := (lemma29_explicit hn Finset.univ p hp).2 _ hinput
  have hh : ∀ᵐ h ∂cappedReleaseKernel hn p hp Finset.univ (ccResidual π₀ w), Bounded 1 h :=
    hcap.mono fun _ hh => hh.1
  have hboth := hcut.and_ae measurableSet_bounded_unit hh
  apply hboth.bind (ccRoundedSolver π₀ K) hp.2.2.2.2.2.2.1.le (add_nonneg hβ.le hτ)
    (Set.toFinite _ |>.measurableSet)
  intro h hh
  exact ccRoundedSolver_utility hn hk π₀ K hw hh.2 hp.1.le hc hη hη1 hβ hβ1 hτ hρ hθ hbase hh.1 hK

theorem ccPrivateKernel_utility {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (p : Parameters) (hp : p.Valid) (base K : Kernel (Weights n) (Partition n))
    [IsMarkovKernel base] [IsMarkovKernel K]
    {w : Weights n} {c A₀ η β τ ρ β₀ : ℝ}
    (hw : Bounded 1 w) (hc : 0 ≤ c) (hη : 0 < η) (hη1 : η ≤ 1)
    (hβ : 0 < β) (hβ1 : β < 1) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hβ₀ : 0 ≤ β₀)
    (hθ : ccTransferTheta c p.gamma η < 1)
    (hbase : HighProbability (base w) β₀ (fun π₀ => ccCost w π₀ ≤ c * ccOptimum w + A₀))
    (hK : ∀ j, IsUnweighted j → HighProbability (K j) τ
      (fun π => clusterCount π ≤ k ∧ ccCost j π ≤ ρ * ccOptimumK j k)) :
    HighProbability (ccPrivateKernel hn p hp base K w) (β₀ + (p.beta + (β + τ)))
      (CCTransferredGood w k ρ (ccTransferTheta c p.gamma η)
        (ccTransferError n p.gamma η A₀ ((2 : ℝ) ^ 126 * mainError n p) β)) := by
  let J : Kernel (Partition n) (Partition n) :=
    ⟨fun π₀ => ccSecondStage hn p hp π₀ K w, measurable_of_finite _⟩
  letI : IsMarkovKernel J := ⟨fun π₀ =>
    inferInstanceAs (IsProbabilityMeasure (ccSecondStage hn p hp π₀ K w))⟩
  apply hbase.bind J hβ₀ (add_nonneg hp.2.2.2.2.2.2.1.le (add_nonneg hβ.le hτ))
    (Set.toFinite _ |>.measurableSet)
  intro π₀ hπ₀
  exact ccSecondStage_utility hn hk p hp π₀ K hw hc hη hη1 hβ hβ1 hτ hρ hθ hπ₀ hK

end DPCut
