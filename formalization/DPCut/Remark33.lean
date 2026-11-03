import DPCut.MaxCutBlockPrivacy

/-! Remark 33's unweighted approximate-DP Max-Cut lower bound, with the exact
statement and constants of the paper. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def finiteExpectedCut {n : ℕ} (μ : Measure (Finset (Fin n))) (w : Weights n) : ℝ :=
  ∑ S, prob μ {S} * cut w S

lemma finiteExpectedCut_blockGraph {n : ℕ} (μ : Measure (Finset (Fin n)))
    (x : Fin (n / 8) → Edge 8) :
    finiteExpectedCut μ (blockGraph x) = ∑ i, edgeContribution μ (blockEdge i (x i)) := by
  simp only [finiteExpectedCut, cut_blockGraph, Finset.mul_sum, edgeContribution]
  rw [Finset.sum_comm]

lemma maxcut_hard_average_upper {n : ℕ} {ε δ : ℝ}
    (hε1 : ε ≤ 1) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (M : Kernel (Weights n) (Finset (Fin n))) [IsMarkovKernel M]
    (hDP : DP (fun w w' => IsUnweighted w ∧ IsUnweighted w' ∧ Adjacent w w') M ε δ) :
    (𝔼 x : Fin (n / 8) → Edge 8, finiteExpectedCut (M (blockGraph x)) (blockGraph x)) ≤
      (106 / 125 : ℝ) * (n / 8 : ℕ) := by
  letI : Nonempty (Edge 8) := ⟨⟨(0, 1), by decide⟩⟩
  have hblock (i : Fin (n / 8)) :
      (𝔼 x : Fin (n / 8) → Edge 8, edgeContribution (M (blockGraph x)) (blockEdge i (x i))) ≤ 106 / 125 := by
    have hb := Finset.expect_le Finset.univ_nonempty (fun x _ => block_average_private hε1 hδ hδ1 M hDP x i)
    have heq := expect_update_coordinate i
      (fun x => edgeContribution (M (blockGraph x)) (blockEdge i (x i)))
    simp only [Function.update_self] at heq
    rwa [heq] at hb
  simp_rw [finiteExpectedCut_blockGraph]
  rw [Finset.expect_sum_comm]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hblock i)
  simpa [mul_comm] using h

lemma maxcut_expected_lower {n : ℕ} {β ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 ≤ B)
    (M : Kernel (Weights n) (Finset (Fin n))) [IsMarkovKernel M]
    (hgood : ∀ w, IsUnweighted w → HighProbability (M w) β
      (fun S => ρ * sSup (Set.range (cut w)) - B ≤ cut w S))
    (x : Fin (n / 8) → Edge 8) :
    (1 - β) * ρ * (n / 8 : ℕ) - B ≤ finiteExpectedCut (M (blockGraph x)) (blockGraph x) := by
  let w := blockGraph x
  let μ := M w
  let good : Finset (Fin n) → Prop := fun S => ρ * (n / 8 : ℕ) - B ≤ cut w S
  have hg : HighProbability μ β good := by
    simpa only [w, μ, good, blockGraph_optimum] using hgood w (blockGraph_unweighted x)
  have hpoint (S : Finset (Fin n)) :
      ρ * (n / 8 : ℕ) * (if good S then prob μ {S} else 0) - B * prob μ {S} ≤
        prob μ {S} * cut w S := by
    have hp : 0 ≤ prob μ {S} := ENNReal.toReal_nonneg
    by_cases hs : good S
    · simp only [if_pos hs]
      have h := mul_le_mul_of_nonneg_left hs hp
      nlinarith
    · simp only [if_neg hs, mul_zero, zero_sub]
      have hw : Nonnegative w := fun e => ((blockGraph_unweighted x).bounded e).1
      nlinarith [mul_nonneg hp (cut_nonneg hw S), mul_nonneg hB hp]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun S _ => hpoint S)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_prob_singletons] at hh
  have hsum : (∑ S : Finset (Fin n), prob μ {S}) = 1 := by simp [prob, ← measureReal_def]
  rw [hsum, mul_one] at hh
  have hl := mul_le_mul_of_nonneg_left hg.2 (show 0 ≤ ρ * (n / 8 : ℕ) by positivity)
  change _ ≤ finiteExpectedCut μ w at hh
  nlinarith

/-- **Remark 33**, presented as a theorem since it includes a substantive lower bound. -/
theorem remark33 : MaxCutLowerBoundStatement := by
  intro n hn ε δ β ρ B _hε hε1 hδ hδ1 hβ hβ1 hρ hρ1 hB M hM hDP hgood
  letI := hM
  letI : Nonempty (Edge 8) := ⟨⟨(0, 1), by decide⟩⟩
  have hu := maxcut_hard_average_upper hε1 hδ hδ1 M hDP
  have hl := Finset.le_expect Finset.univ_nonempty
    (fun x _ => maxcut_expected_lower (by linarith : 0 ≤ ρ) hB M hgood x)
  have hρlo : (99 / 100 : ℝ) * (868 / 1000) ≤ (1 - β) * ρ := by
    apply mul_le_mul (by linarith) hρ (by norm_num) (by linarith)
  have hm : (0 : ℝ) ≤ (n / 8 : ℕ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_right hρlo hm
  nlinarith

end DPCut
