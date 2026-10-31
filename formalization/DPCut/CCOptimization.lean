import DPCut.CCBernoulliRounding
import DPCut.ExpectedApproximation

/-! Restricted CC optima and amplification with an explicitly feasible fallback. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma IsUnweighted.bounded {n : ℕ} {w : Weights n} (hw : IsUnweighted w) : Bounded 1 w := by
  intro e
  rcases hw e with h | h <;> rw [h] <;> norm_num

lemma clusterCount_le_n {n : ℕ} (π : Partition n) : clusterCount π ≤ n := by
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

lemma ccOptimumK_le {n k : ℕ} (w : Weights n) {π : Partition n} (hπ : clusterCount π ≤ k) :
    ccOptimumK w k ≤ ccCost w π :=
  csInf_le ((Set.toFinite _).image (ccCost w)).bddBelow ⟨π, hπ, rfl⟩

lemma ccOptimumK_n {n : ℕ} (w : Weights n) : ccOptimumK w n = ccOptimum w := by
  have hset : {π : Partition n | clusterCount π ≤ n} = Set.univ := by
    ext π
    simp [clusterCount_le_n π]
  simp [ccOptimumK, ccOptimum, hset]

lemma ccOptimum_le_ccOptimumK {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) (w : Weights n) :
    ccOptimum w ≤ ccOptimumK w k := by
  obtain ⟨π, _, he⟩ := ccOptimumK_exists (k := k) hn hk w
  rw [← he]
  exact ccOptimum_le w π

lemma ccOptimumK_nonneg {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k) {w : Weights n}
    (hw : Bounded 1 w) : 0 ≤ ccOptimumK w k := by
  obtain ⟨π, _, he⟩ := ccOptimumK_exists (k := k) hn hk w
  rw [← he]
  exact ccCost_nonneg hw π

lemma cc_approximation_transferK {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    {w j : Weights n} {θ B ρ : ℝ}
    (hθ : θ < 1) (hρ : 0 ≤ ρ) (hcmp : ∀ π : Partition n,
      |ccCost j π - ccCost w π| ≤ θ * ccCost w π + B)
    {π : Partition n} (hπ : ccCost j π ≤ ρ * ccOptimumK j k) :
    ccCost w π ≤ ρ * (1 + θ) / (1 - θ) * ccOptimumK w k + (ρ + 1) / (1 - θ) * B := by
  obtain ⟨πstar, hf, hopt⟩ := ccOptimumK_exists (k := k) hn hk w
  have h₁ := (abs_le.mp (hcmp π)).1
  have h₂ := (abs_le.mp (hcmp πstar)).2
  rw [hopt] at h₂
  have hs := mul_le_mul_of_nonneg_left (ccOptimumK_le j hf) hρ
  have hr := mul_le_mul_of_nonneg_left h₂ hρ
  have hpos : 0 < 1 - θ := by linarith
  have hh : ccCost w π ≤ (ρ * (1 + θ) * ccOptimumK w k + (ρ + 1) * B) / (1 - θ) :=
    (le_div_iff₀ hpos).mpr (by nlinarith)
  convert hh using 1
  ring

@[fun_prop] lemma measurable_ccCost {n : ℕ} (π : Partition n) :
    Measurable (fun j : Weights n => ccCost j π) := by
  unfold ccCost
  apply Finset.measurable_sum
  intro e _
  by_cases he : π e.val.1 = π e.val.2 <;> simp only [he, if_true, if_false] <;> fun_prop

def feasibleCC {n : ℕ} (k : ℕ) (seed π : Partition n) : Partition n :=
  if clusterCount π ≤ k then π else seed

lemma feasibleCC_feasible {n k : ℕ} (seed π : Partition n) (hs : clusterCount seed ≤ k) :
    clusterCount (feasibleCC k seed π) ≤ k := by
  unfold feasibleCC
  split <;> assumption

def safeCCKernel {n : ℕ} (K : Kernel (Weights n) (Partition n)) (k : ℕ) (seed : Partition n) :
    Kernel (Weights n) (Partition n) :=
  ⟨fun w => (K w).map (feasibleCC k seed),
    (Measure.measurable_map _ (measurable_of_finite _)).comp K.measurable⟩

instance safeCCKernel_markov {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    (k : ℕ) (seed : Partition n) : IsMarkovKernel (safeCCKernel K k seed) := by
  constructor
  intro w
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

def amplifiedCC {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    (k t : ℕ) (seed : Partition n) : Kernel (Weights n) (Partition n) :=
  bestOfKernel (safeCCKernel K k seed) (fun w π => -ccCost w π)
    (fun π => (measurable_ccCost π).neg) t seed

instance amplifiedCC_markov {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    (k t : ℕ) (seed : Partition n) : IsMarkovKernel (amplifiedCC K k t seed) :=
  bestOfKernel_markov _ _ _ _ _

theorem amplifiedCC_success {n : ℕ} (K : Kernel (Weights n) (Partition n)) [IsMarkovKernel K]
    {k : ℕ} (seed : Partition n) (hseed : clusterCount seed ≤ k) (w : Weights n)
    {ρ s τ : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hτ : 0 < τ)
    (hgood : HighProbability (K w) (1 - s) (fun π => clusterCount π ≤ k ∧ ccCost w π ≤ ρ * ccOptimumK w k))
    (t : ℕ) (ht : Real.log (1 / τ) / s ≤ t) :
    HighProbability (amplifiedCC K k t seed w) τ
      (fun π => clusterCount π ≤ k ∧ ccCost w π ≤ ρ * ccOptimumK w k) := by
  have hsafe : s ≤ prob (safeCCKernel K k seed w) {π | - (ρ * ccOptimumK w k) ≤ -ccCost w π} := by
    have hm := measurable_of_finite (feasibleCC k seed)
    have hset : MeasurableSet {π : Partition n | -(ρ * ccOptimumK w k) ≤ -ccCost w π} :=
      Set.toFinite _ |>.measurableSet
    change s ≤ ((K w).map (feasibleCC k seed) _).toReal
    rw [Measure.map_apply hm hset]
    have hsub : {π | clusterCount π ≤ k ∧ ccCost w π ≤ ρ * ccOptimumK w k} ⊆
        (feasibleCC k seed) ⁻¹' {π | -(ρ * ccOptimumK w k) ≤ -ccCost w π} := by
      intro π hπ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, feasibleCC, if_pos hπ.1]
      linarith [hπ.2]
    have h := measure_mono (μ := K w) hsub
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) h
    have hprob := hgood.2
    dsimp only [prob] at hprob
    linarith
  have hsuccess := (bestOf_success (fun π => -ccCost w π) (-(ρ * ccOptimumK w k)) hs.le hs1 hsafe t seed).weaken
    (repetition_failure_bound hs hs1 hτ t ht)
  have hfeasible : ∀ᵐ π ∂safeCCKernel K k seed w, clusterCount π ≤ k := by
    apply (ae_map_iff (measurable_of_finite _).aemeasurable (Set.toFinite _ |>.measurableSet)).mpr
    exact Filter.Eventually.of_forall (fun π => feasibleCC_feasible seed π hseed)
  have hf := bestOf_ae (safeCCKernel K k seed w) (fun π => -ccCost w π) t seed hseed hfeasible
  have hboth := hsuccess.and_ae (Set.toFinite _ |>.measurableSet) hf
  exact hboth.mono _ (Set.toFinite _ |>.measurableSet) (fun π hπ => ⟨hπ.2, by linarith [hπ.1]⟩)

end DPCut
