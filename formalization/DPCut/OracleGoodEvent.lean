import DPCut.OracleSensitivity
import DPCut.Lemma14

/-! The common Gaussian event used to condition each attempt in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DPCut

lemma HighProbability.mono {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {δ : ℝ} {P Q : α → Prop}
    (h : HighProbability μ δ P) (hQ : MeasurableSet {x | Q x}) (hPQ : ∀ x, P x → Q x) :
    HighProbability μ δ Q :=
  ⟨hQ, h.2.trans (measureReal_mono hPQ)⟩

lemma HighProbability.and {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {δ η : ℝ} {P Q : α → Prop}
    (hP : HighProbability μ δ P) (hQ : HighProbability μ η Q) :
    HighProbability μ (δ + η) (fun x => P x ∧ Q x) := by
  refine ⟨hP.1.inter hQ.1, ?_⟩
  have h := measureReal_union_add_inter (μ := μ) (s := {x | P x}) hQ.1
  have hu : μ.real ({x | P x} ∪ {x | Q x}) ≤ 1 := measureReal_le_one
  have hp : 1 - δ ≤ μ.real {x | P x} := hP.2
  have hq : 1 - η ≤ μ.real {x | Q x} := hQ.2
  change 1 - (δ + η) ≤ μ.real ({x | P x} ∩ {x | Q x})
  linarith

lemma covarianceDistance_symm {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    covarianceDistance X Y = covarianceDistance Y X := by
  have he : covarianceDistance X Y ^ 2 = covarianceDistance Y X ^ 2 := by
    rw [covarianceDistance_sq hX hY, covarianceDistance_sq hY hX]
    congr 1
    noncomm_ring
  have h0 : 0 ≤ covarianceDistance X Y := frobenius_nonneg _
  have h1 : 0 ≤ covarianceDistance Y X := frobenius_nonneg _
  nlinarith

def CommonTrialGood {n k : ℕ} (X Y : Mat n) (ε : ℝ) (z : Fin k → Fin n → ℝ) : Prop :=
  |batchLogRatio X Y z| ≤ ε ∧
    ∀ e, queryMax X Y e / 8 ≤ clippedWitness z e ∧
      clippedWitness z e ≤ 2 * queryMax X Y e

lemma measurableSet_CommonTrialGood {n k : ℕ} (X Y : Mat n) (ε : ℝ) :
    MeasurableSet {z : Fin k → Fin n → ℝ | CommonTrialGood X Y ε z} := by
  simp only [CommonTrialGood, Set.setOf_and, Set.setOf_forall]
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_batchLogRatio X Y).abs measurable_const
  · exact MeasurableSet.iInter fun e =>
      (measurableSet_le measurable_const (measurable_clippedWitness e)).inter
      (measurableSet_le (measurable_clippedWitness e) measurable_const)

lemma commonTrialGood_symm {n k : ℕ} (X Y : Mat n) (ε : ℝ) (z : Fin k → Fin n → ℝ) :
    CommonTrialGood X Y ε z ↔ CommonTrialGood Y X ε z := by
  have hr : batchLogRatio Y X z = -batchLogRatio X Y z := by
    simp [batchLogRatio, Finset.sum_sub_distrib]
  simp only [CommonTrialGood, hr, abs_neg, queryMax, max_comm]

lemma chiGood_common_bounds {n k : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n)
    (hd : covarianceDistance X Y ≤ 1 / 2) {z : Fin k → Fin n → ℝ}
    (hz : ChiGood X z) (e : Edge n) :
    queryMax X Y e / 8 ≤ clippedWitness z e ∧
      clippedWitness z e ≤ 2 * queryMax X Y e := by
  have hc := fractionalQuery_comparable hn hX hY hd e
  have hmax : queryMax X Y e ≤ 2 * fractionalQuery X e := by
    apply max_le
    · linarith [(feasible_fractionalQuery_bounds hn hX e).1]
    · linarith
  have hge : fractionalQuery X e ≤ queryMax X Y e := le_max_left _ _
  have hq := (queryMax_bounds hn hX hY e).1
  constructor <;> linarith [(hz e).1, (hz e).2]

theorem commonTrialGood_highProbability {n k : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n)
    {β δ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hδ : 0 < δ) (hδ1 : δ < 1 / 2)
    (hk : 0 < k) (hsize : 96 * Real.log (n / (β * δ)) ≤ k)
    (hd : covarianceDistance X Y < 1 / 2)
    (hε : 4 * (k * covarianceDistance X Y ^ 2 +
      Real.sqrt (k * Real.log (1 / δ)) * covarianceDistance X Y +
      Real.log (1 / δ) * covarianceDistance X Y) ≤ ε) :
    HighProbability (gaussianBatch X k) (2 * δ) (CommonTrialGood X Y ε) := by
  have hl := gaussian_privacy (k := k) (feasible_posDef hn hX) (feasible_posDef hn hY) hδ hδ1 hd
  have hf := (chiGood_failure_bound hn hX k hk).trans
    ((chi_sampleSize_bound n k hn β δ hβ hβ1 hδ (by linarith) hsize).trans (min_le_right _ _))
  have hc : HighProbability (gaussianBatch X k) δ (ChiGood X) := by
    refine ⟨measurableSet_ChiGood X, ?_⟩
    have he : (gaussianBatch X k).real {z | ¬ChiGood X z} =
        1 - (gaussianBatch X k).real {z | ChiGood X z} := by
      simpa using measureReal_compl (μ := gaussianBatch X k) (measurableSet_ChiGood X)
    change (gaussianBatch X k).real {z | ¬ChiGood X z} ≤ δ at hf
    rw [he] at hf
    change 1 - δ ≤ (gaussianBatch X k).real {z | ChiGood X z}
    linarith
  have hm := (hl.and _ hc).mono _ (measurableSet_CommonTrialGood X Y ε) (by
    intro z hz
    exact ⟨hz.1.trans hε, chiGood_common_bounds hn hX hY hd.le hz.2⟩)
  simpa only [two_mul] using hm

end DPCut
