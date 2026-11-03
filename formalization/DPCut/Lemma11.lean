import DPCut.WitnessQuadratic

/-!
Lemma 11 (`lem:chaos`): `ChaosStatement`, with `C = 512` and `c₀ = 1/2048`.
The proof uses exact Gaussian moments and the spectral theorem in place of
the paper's general hypercontractivity lemma.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder

namespace DPCut

/-- Shrinkage of the elliptope gives the strict upper bound needed to undo clipping. -/
lemma feasible_fractionalQuery_lt_one {n : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (e : Edge n) : fractionalQuery X e < 1 := by
  have hpos := feasible_posDef hn hX
  have hij : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have hsym : X e.val.2 e.val.1 = X e.val.1 e.val.2 := by
    simpa using hX.1.apply e.val.1 e.val.2
  have hv : (Pi.single e.val.1 1 + Pi.single e.val.2 1 : Fin n → ℝ) ≠ 0 := by
    intro h
    have := congrFun h e.val.1
    simp [hij] at this
  have hhi := hpos.2 _ hv
  simp [Matrix.mulVec_add, dotProduct_add, hX.2.1, hsym] at hhi
  dsimp [fractionalQuery]
  linarith

lemma unclippedGood_of_chiGood {n k : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) {z : Fin k → Fin n → ℝ} (hz : ChiGood X z) :
    UnclippedGood X z := by
  intro e
  obtain ⟨hl, hu⟩ := hz e
  have hq := feasible_fractionalQuery_lt_one hn hX e
  change _ ≤ min (rawWitness z e / 2) 1 at hl
  change min (rawWitness z e / 2) 1 ≤ _ at hu
  have hl' := (le_min_iff.1 hl).1
  have hu' : rawWitness z e / 2 ≤ fractionalQuery X e := by
    rcases min_le_iff.1 hu with h | h
    · exact h
    · linarith
  constructor <;> linarith

lemma clippedScore_eq_unclippedScore {n k : ℕ} (hn : 2 ≤ n) {X : Mat n}
    (hX : X ∈ feasible n) (D : Weights n) {z : Fin k → Fin n → ℝ} (hz : ChiGood X z) :
    pairing D (clippedWitness z) = unclippedScore D z := by
  have hu := unclippedGood_of_chiGood hn hX hz
  unfold pairing unclippedScore
  apply Finset.sum_congr rfl
  intro e _
  have he : rawWitness z e / 2 ≤ 1 := by
    linarith [(hu e).2, (feasible_fractionalQuery_bounds hn hX e).2]
  simp only [clippedWitness, min_eq_left he]

lemma chaos_failure_bound (n k : ℕ) (hn : 2 ≤ n)
    (hk : 512 * Real.log (n : ℝ) ≤ k) :
    2 * (n : ℝ) ^ 2 * Real.exp (-(k : ℝ) / 32) ≤ (1 / 2048 : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
  have hlogpos : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog : Real.log (4096 * (n : ℝ) ^ 2) = 12 * Real.log 2 + 2 * Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
      show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    norm_num
  have he : Real.exp (-(k : ℝ) / 32) ≤ (4096 * (n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.exp_log (by positivity : 0 < 4096 * (n : ℝ) ^ 2), ← Real.exp_neg]
    apply Real.exp_le_exp.2
    rw [hlog]
    linarith
  have hm := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * (n : ℝ) ^ 2 by positivity)
  have hc : 2 * (n : ℝ) ^ 2 * (4096 * (n : ℝ) ^ 2)⁻¹ = (1 / 2048 : ℝ) := by
    field_simp
    ring
  exact hm.trans_eq hc

/-- A joint good-and-success bound, before dividing by the conditioning probability. -/
theorem chaos_joint_success {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (hk : 0 < k)
    (hsize : 512 * Real.log (n : ℝ) ≤ k) (D : Weights n) {X : Mat n}
    (hX : X ∈ feasible n) :
    (1 / 2048 : ℝ) ≤ prob (gaussianBatch X k)
      {z | ChiGood X z ∧ pairing D (fractionalQuery X) / 2 ≤ pairing D (clippedWitness z)} := by
  have habove := unclippedScore_above_mean hn k hk D hX
  have hbad := (chiGood_failure_bound hn hX k hk).trans (chaos_failure_bound n k hn hsize)
  let s := {z : Fin k → Fin n → ℝ | pairing D (fractionalQuery X) / 2 ≤ unclippedScore D z}
  let t := {z : Fin k → Fin n → ℝ |
    ChiGood X z ∧ pairing D (fractionalQuery X) / 2 ≤ pairing D (clippedWitness z)}
  let b := {z : Fin k → Fin n → ℝ | ¬ChiGood X z}
  have hs : s ⊆ t ∪ b := by
    intro z hz
    by_cases hg : ChiGood X z
    · apply Or.inl
      exact ⟨hg, by rwa [clippedScore_eq_unclippedScore hn hX D hg]⟩
    · exact Or.inr hg
  have h := (measureReal_mono (μ := gaussianBatch X k) hs).trans (measureReal_union_le t b)
  change prob (gaussianBatch X k) s ≤ prob (gaussianBatch X k) t + prob (gaussianBatch X k) b at h
  change (1 / 1024 : ℝ) ≤ prob (gaussianBatch X k) s at habove
  change prob (gaussianBatch X k) b ≤ (1 / 2048 : ℝ) at hbad
  change (1 / 2048 : ℝ) ≤ prob (gaussianBatch X k) t
  linarith

/-- **Lemma 11**, for signed weights and the paper's conditioning event.
No unproved hypercontractivity or moment statement is assumed. -/
theorem lemma11 : ChaosStatement := by
  refine ⟨512, 1 / 2048, by norm_num, by norm_num, ?_⟩
  intro n hn D X hX βχ δ₁ hβ hβ1 hδ hδ1 k hk hsize
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogβ : Real.log βχ ≤ 0 := Real.log_nonpos hβ.le hβ1.le
  have hlogδ : Real.log δ₁ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  have hsize' : 512 * Real.log (n : ℝ) ≤ k := by
    rw [Real.log_div hnpos.ne' (mul_pos hβ hδ).ne', Real.log_mul hβ.ne' hδ.ne'] at hsize
    linarith
  have hj := chaos_joint_success hn k hk hsize' D hX
  let g := {z : Fin k → Fin n → ℝ | ChiGood X z}
  let s := {z : Fin k → Fin n → ℝ |
    ChiGood X z ∧ pairing D (fractionalQuery X) / 2 ≤ pairing D (clippedWitness z)}
  change (1 / 2048 : ℝ) ≤ prob (gaussianBatch X k) s at hj
  have hsg : prob (gaussianBatch X k) s ≤ prob (gaussianBatch X k) g :=
    measureReal_mono (fun _ hz => hz.1)
  have hgpos : 0 < prob (gaussianBatch X k) g := by linarith
  have hg1 : prob (gaussianBatch X k) g ≤ 1 := by
    have h := measureReal_mono (μ := gaussianBatch X k) (Set.subset_univ g)
    simpa only [measureReal_univ_eq_one] using h
  refine ⟨hgpos, ?_⟩
  change (1 / 2048 : ℝ) ≤ prob (gaussianBatch X k) s / prob (gaussianBatch X k) g
  apply (le_div_iff₀ hgpos).2
  nlinarith

end DPCut
