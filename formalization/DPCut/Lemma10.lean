import DPCut.GaussianWitness
import DPCut.Statements

/-!
Lemma 10 (`lem:chi`) of the current root manuscript `STOC2027.tex`.
The theorem proves the existing `ChiStatement`, with universal constant `C = 96`.
Only its Gaussian, chi-square, union-bound, and clipping prerequisites are used.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace DPCut

lemma measurable_rawWitness {n k : ℕ} (e : Edge n) :
    Measurable (fun z : Fin k → Fin n → ℝ => rawWitness z e) := by
  unfold rawWitness
  fun_prop

lemma measurable_clippedWitness {n k : ℕ} (e : Edge n) :
    Measurable (fun z : Fin k → Fin n → ℝ => clippedWitness z e) := by
  exact ((measurable_rawWitness e).div_const 2).min measurable_const

lemma measurableSet_ChiGood {n k : ℕ} (X : Mat n) :
    MeasurableSet {z : Fin k → Fin n → ℝ | ChiGood X z} := by
  simp only [ChiGood, Set.setOf_forall]
  exact MeasurableSet.iInter fun e =>
    (measurableSet_le measurable_const (measurable_clippedWitness e)).inter
      (measurableSet_le (measurable_clippedWitness e) measurable_const)

lemma normalizedEdge_sum_sq {n k : ℕ} {X : Mat n} (e : Edge n)
    (hq : 0 < fractionalQuery X e) (z : Fin k → Fin n → ℝ) :
    (∑ j, normalizedEdge X e (z j) ^ 2) / k = rawWitness z e / fractionalQuery X e := by
  simp only [normalizedEdge, rawWitness, div_pow, mul_pow, Real.sq_sqrt hq.le]
  rw [← Finset.sum_div, ← Finset.sum_div]
  ring

/-- Single-edge concentration, before clipping, with all distributional facts discharged. -/
lemma rawWitness_tail {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n)
    (k : ℕ) (hk : 0 < k) (e : Edge n) :
    prob (gaussianBatch X k)
      {z | ¬(fractionalQuery X e / 2 ≤ rawWitness z e ∧
        rawWitness z e ≤ 2 * fractionalQuery X e)} ≤ 2 * Real.exp (-(k : ℝ) / 32) := by
  have hq := (feasible_fractionalQuery_bounds hn hX e).1
  have hm : Measurable (fun z : Fin k → Fin n → ℝ => fun j => normalizedEdge X e (z j)) := by
    exact measurable_pi_lambda _ fun j =>
      (measurable_normalizedEdge X e).comp (measurable_pi_apply j)
  have hs : MeasurableSet {z : Fin k → ℝ | (∑ i, z i ^ 2) / k ∉ Set.Icc (1 / 2 : ℝ) 2} := by
    apply MeasurableSet.compl
    apply measurableSet_preimage (by fun_prop) measurableSet_Icc
  have he : {z : Fin k → Fin n → ℝ | ¬(fractionalQuery X e / 2 ≤ rawWitness z e ∧
        rawWitness z e ≤ 2 * fractionalQuery X e)} =
      (fun z j => normalizedEdge X e (z j)) ⁻¹'
        {z : Fin k → ℝ | (∑ i, z i ^ 2) / k ∉ Set.Icc (1 / 2 : ℝ) 2} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, normalizedEdge_sum_sq e hq,
      Set.mem_Icc, le_div_iff₀ hq, div_le_iff₀ hq, one_div_mul_eq_div]
  have h := chiSquare_tail k hk
  unfold prob at h ⊢
  rw [he, ← Measure.map_apply hm hs, gaussianBatch_map_normalizedEdge hn hX e k]
  exact h

lemma chiGood_of_unclippedGood {n k : ℕ} {X : Mat n}
    (hq : ∀ e, fractionalQuery X e ≤ 1) {z : Fin k → Fin n → ℝ}
    (hz : UnclippedGood X z) : ChiGood X z := by
  intro e
  obtain ⟨hl, hu⟩ := hz e
  have hc : rawWitness z e / 2 ≤ 1 := by linarith [hq e]
  simp only [clippedWitness, min_eq_left hc]
  constructor <;> linarith

/-- Union bound over the loopless unordered pairs; `n²` is a convenient upper bound. -/
lemma chiGood_failure_bound {n : ℕ} (hn : 2 ≤ n) {X : Mat n} (hX : X ∈ feasible n)
    (k : ℕ) (hk : 0 < k) :
    prob (gaussianBatch X k) {z | ¬ChiGood X z} ≤
      2 * (n : ℝ) ^ 2 * Real.exp (-(k : ℝ) / 32) := by
  classical
  let bad (e : Edge n) := {z : Fin k → Fin n → ℝ |
    ¬(fractionalQuery X e / 2 ≤ rawWitness z e ∧ rawWitness z e ≤ 2 * fractionalQuery X e)}
  have hs : {z : Fin k → Fin n → ℝ | ¬ChiGood X z} ⊆ ⋃ e, bad e := by
    intro z hz
    by_contra h
    have hg : UnclippedGood X z := by
      simpa only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not, bad] using h
    exact hz (chiGood_of_unclippedGood (fun e => (feasible_fractionalQuery_bounds hn hX e).2) hg)
  have hc : Fintype.card (Edge n) ≤ n ^ 2 := by
    have h := Fintype.card_le_of_injective (fun e : Edge n => e.val) Subtype.val_injective
    simpa [Fintype.card_prod, Fintype.card_fin, pow_two] using h
  have hcR : (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hc
  calc
    _ ≤ (gaussianBatch X k).real (⋃ e, bad e) := measureReal_mono hs
    _ ≤ ∑ e, (gaussianBatch X k).real (bad e) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _ : Edge n, 2 * Real.exp (-(k : ℝ) / 32) := by
      apply Finset.sum_le_sum
      intro e _
      exact rawWitness_tail hn hX k hk e
    _ = (Fintype.card (Edge n) : ℝ) * (2 * Real.exp (-(k : ℝ) / 32)) := by simp
    _ ≤ _ := by nlinarith [Real.exp_pos (-(k : ℝ) / 32)]

/-- The manuscript's logarithmic batch-size condition, with an explicit universal constant. -/
lemma chi_sampleSize_bound (n k : ℕ) (hn : 2 ≤ n) (β δ : ℝ)
    (hβ : 0 < β) (hβ1 : β < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hk : 96 * Real.log ((n : ℝ) / (β * δ)) ≤ k) :
    2 * (n : ℝ) ^ 2 * Real.exp (-(k : ℝ) / 32) ≤ min β δ := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hβδ : 0 < β * δ := mul_pos hβ hδ
  have hlogβ : Real.log β ≤ 0 := Real.log_nonpos hβ.le hβ1.le
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hratio : 0 < β * δ / (2 * (n : ℝ) ^ 2) := by positivity
  have hlog : Real.log (β * δ / (2 * (n : ℝ) ^ 2)) =
      Real.log β + Real.log δ - Real.log 2 - 2 * Real.log n := by
    rw [Real.log_div hβδ.ne' (by positivity), Real.log_mul hβ.ne' hδ.ne',
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  have hexp : Real.exp (-(k : ℝ) / 32) ≤ β * δ / (2 * (n : ℝ) ^ 2) := by
    rw [← Real.exp_log hratio]
    apply Real.exp_le_exp.2
    rw [hlog]
    rw [Real.log_div hnpos.ne' hβδ.ne', Real.log_mul hβ.ne' hδ.ne'] at hk
    linarith
  have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
  have he : (2 * (n : ℝ) ^ 2) * (β * δ / (2 * (n : ℝ) ^ 2)) = β * δ := by
    field_simp
  rw [he] at hm
  exact hm.trans (le_min (by nlinarith) (by nlinarith))

/-- **Lemma 10**, exactly the previously declared target, now proved with `C = 96`.
The samples are independent by `gaussianBatch`; `βχ, δ₁ ∈ (0,1)`, `n ≥ 2`, and
`k > 0` make explicit the domain assumptions used in the manuscript. -/
theorem lemma10 : ChiStatement := by
  refine ⟨96, by norm_num, ?_⟩
  intro n hn X hX βχ δ₁ hβ hβ1 hδ hδ1 k hk hsize
  refine ⟨measurableSet_ChiGood X, ?_⟩
  have hf := (chiGood_failure_bound hn hX k hk).trans
    (chi_sampleSize_bound n k hn βχ δ₁ hβ hβ1 hδ hδ1 hsize)
  have he : (gaussianBatch X k).real {z | ¬ChiGood X z} =
      1 - (gaussianBatch X k).real {z | ChiGood X z} := by
    simpa using measureReal_compl (μ := gaussianBatch X k) (measurableSet_ChiGood X)
  change (gaussianBatch X k).real {z | ¬ChiGood X z} ≤ min βχ δ₁ at hf
  rw [he] at hf
  change 1 - min βχ δ₁ ≤ (gaussianBatch X k).real {z | ChiGood X z}
  linarith

end DPCut
