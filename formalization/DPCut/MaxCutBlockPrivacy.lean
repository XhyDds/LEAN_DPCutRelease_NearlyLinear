import DPCut.MaxCutHardFamily

/-! One-block approximate-DP comparison and averaging over all independent
input blocks, as used in Remark 33. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def edgeContribution {n : ℕ} (μ : Measure (Finset (Fin n))) (e : Edge n) : ℝ :=
  ∑ S, prob μ {S} * cutQuery S e

def edgeMiss {n : ℕ} (μ : Measure (Finset (Fin n))) (e : Edge n) : ℝ :=
  prob μ {S | cutQuery S e = 0}

lemma edgeContribution_nonneg {n : ℕ} (μ : Measure (Finset (Fin n))) (e : Edge n) :
    0 ≤ edgeContribution μ e := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg ENNReal.toReal_nonneg (by unfold cutQuery; split <;> norm_num)

lemma edgeMiss_add_contribution {n : ℕ} (μ : Measure (Finset (Fin n))) [IsProbabilityMeasure μ]
    (e : Edge n) : edgeMiss μ e + edgeContribution μ e = 1 := by
  rw [edgeMiss, ← sum_prob_singletons]
  unfold edgeContribution
  rw [← Finset.sum_add_distrib]
  have he (S : Finset (Fin n)) :
      (if cutQuery S e = 0 then prob μ {S} else 0) + prob μ {S} * cutQuery S e = prob μ {S} := by
    unfold cutQuery
    split <;> simp
  simp only [he]
  simp [prob, ← measureReal_def]

lemma block_sum_contribution {n : ℕ} (μ : Measure (Finset (Fin n))) [IsProbabilityMeasure μ]
    (i : Fin (n / 8)) : (∑ e : Edge 8, edgeContribution μ (blockEdge i e)) ≤ 16 := by
  unfold edgeContribution
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  calc
    _ ≤ ∑ S : Finset (Fin n), prob μ {S} * 16 := Finset.sum_le_sum fun S _ =>
      mul_le_mul_of_nonneg_left (sum_block_cutQuery_le i S) ENNReal.toReal_nonneg
    _ = 16 := by rw [← Finset.sum_mul]; simp [prob, ← measureReal_def]

lemma block_average_private {n : ℕ} {ε δ : ℝ}
    (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (M : Kernel (Weights n) (Finset (Fin n))) [IsMarkovKernel M]
    (hDP : DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') M ε δ)
    (x : Fin (n / 8) → Edge 8) (i : Fin (n / 8)) :
    (𝔼 e : Edge 8, edgeContribution (M (blockGraph (Function.update x i e))) (blockEdge i e)) ≤ 106 / 125 := by
  have hexp : Real.exp ε ≤ 11 / 4 :=
    (Real.exp_le_exp.mpr hε1).trans (by linarith [Real.exp_one_lt_d9])
  let μ := M (deletedBlockGraph x i)
  let ν := fun e => M (blockGraph (Function.update x i e))
  have hpoint (e : Edge 8) : edgeMiss μ (blockEdge i e) ≤ (11 / 4 : ℝ) * edgeMiss (ν e) (blockEdge i e) + δ := by
    have hadj : Adjacent (deletedBlockGraph x i) (blockGraph (Function.update x i e)) := by
      rw [← deletedBlockGraph_update x i e]
      exact blockGraph_adjacent_deleted _ i
    have h := (privacy_event_iff_real _ _ _ ε hδ).mp
      (hDP _ _ ⟨deletedBlockGraph_unweighted x i, blockGraph_unweighted _, hadj⟩
        {S | cutQuery S (blockEdge i e) = 0} (Set.toFinite _ |>.measurableSet))
    have hm := mul_le_mul_of_nonneg_right hexp
      (show 0 ≤ edgeMiss (ν e) (blockEdge i e) from ENNReal.toReal_nonneg)
    change edgeMiss μ (blockEdge i e) ≤ Real.exp ε * edgeMiss (ν e) (blockEdge i e) + δ at h
    linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)
  have hμ := block_sum_contribution μ i
  have hmissμ : (∑ e : Edge 8, edgeMiss μ (blockEdge i e)) +
      (∑ e : Edge 8, edgeContribution μ (blockEdge i e)) = 28 := by
    rw [← Finset.sum_add_distrib]
    simp [edgeMiss_add_contribution, eight_edge_card]
  have hmissν : (∑ e : Edge 8, edgeMiss (ν e) (blockEdge i e)) +
      (∑ e : Edge 8, edgeContribution (ν e) (blockEdge i e)) = 28 := by
    rw [← Finset.sum_add_distrib]
    simp [edgeMiss_add_contribution, eight_edge_card]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, eight_edge_card, nsmul_eq_mul, Nat.cast_ofNat] at hsum
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, eight_edge_card]
  change (∑ e : Edge 8, edgeContribution (ν e) (blockEdge i e)) / 28 ≤ 106 / 125
  linarith

lemma expect_update_coordinate {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (i : ι) (f : (ι → α) → ℝ) :
    (𝔼 x : ι → α, 𝔼 a : α, f (Function.update x i a)) = 𝔼 x : ι → α, f x := by
  let swap : ((ι → α) × α) → ((ι → α) × α) :=
    fun q => (Function.update q.1 i q.2, q.1 i)
  have hinv : Function.Involutive swap := by
    intro q
    apply Prod.ext
    · funext j
      by_cases hj : j = i <;> simp [swap, hj]
    · simp [swap]
  have hh := Fintype.expect_bijective swap hinv.bijective
    (fun q => f (Function.update q.1 i q.2)) (fun q => f q.1) (fun _ => rfl)
  rw [← Finset.univ_product_univ, Finset.expect_product] at hh
  rw [Finset.expect_product] at hh
  simpa only [Fintype.expect_const] using hh

end DPCut
