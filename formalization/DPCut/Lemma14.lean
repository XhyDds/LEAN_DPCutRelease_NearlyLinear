import DPCut.GaussianLikelihood
import DPCut.Lemma15

/-! Lemma 14 (`lem:gaussian-privacy`), with explicit universal constant `C = 4`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal MatrixOrder

namespace DPCut

lemma sqrt_variance_bound {V d t : ℝ} {k : ℕ} (hV : 0 ≤ V) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hvar : V ≤ 2 * k * d ^ 2) :
    Real.sqrt V * Real.sqrt t ≤ 2 * Real.sqrt (k * t) * d := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  have hkt : 0 ≤ (k : ℝ) * t := by positivity
  simp only [mul_pow, Real.sq_sqrt hV, Real.sq_sqrt ht, Real.sq_sqrt hkt]
  have hm := mul_le_mul_of_nonneg_right hvar ht
  have hp : 0 ≤ (k : ℝ) * t * d ^ 2 := by positivity
  nlinarith

lemma gaussian_logRatio_tail {n k : ℕ} {X Y : Mat n}
    (hX : X.PosDef) (hY : Y.PosDef) (hd : covarianceDistance X Y < 1 / 2)
    {t : ℝ} (ht : 0 < t) :
    prob (gaussianBatch X k) {z | |batchLogRatio X Y z| >
      k * covarianceDistance X Y ^ 2 +
        2 * Real.sqrt (k * t) * covarianceDistance X Y + 2 * t * covarianceDistance X Y} ≤
      2 * Real.exp (-t) := by
  let d := covarianceDistance X Y
  let hB := relativePrecision_posDef hX hY
  let r := hB.1.eigenvalues
  let a : Fin k × Fin n → ℝ := fun p => r p.2 - 1
  let R := (k : ℝ) * d ^ 2 + 2 * Real.sqrt (k * t) * d + 2 * t * d
  have hd0 : 0 ≤ d := frobenius_nonneg _
  obtain ⟨hm0, hm, hv, ha⟩ := relativePrecision_spectral_bounds hX hY hd
  have hvar : (∑ p, a p ^ 2) ≤ 2 * k * d ^ 2 := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hh := mul_le_mul_of_nonneg_left hv hk
    simpa [a, r, hB, Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm] using hh
  have htail := weighted_chiSquare_tail a (show 0 ≤ 2 * d by positivity)
    (fun p => ha p.2) ht
  have hroot := sqrt_variance_bound (Finset.sum_nonneg fun p _ => sq_nonneg (a p)) hd0 ht.le hvar
  have hpoint (z : Fin k × Fin n → ℝ)
      (hz : |∑ p, a p * (z p ^ 2 - 1)| ≤
        2 * (Real.sqrt (∑ p, a p ^ 2) * Real.sqrt t + 2 * d * t)) :
      |batchLogRatio X Y (diagonalBatch X hB.1.eigenvectorUnitary z)| ≤ R := by
    have he := batchLogRatio_diagonal hX hY z
    change 2 * batchLogRatio X Y (diagonalBatch X hB.1.eigenvectorUnitary z) =
      k * (∑ i, (r i - 1 - Real.log (r i))) + ∑ p, a p * (z p ^ 2 - 1) at he
    have htri := abs_add_le ((k : ℝ) * ∑ i, (r i - 1 - Real.log (r i)))
      (∑ p, a p * (z p ^ 2 - 1))
    rw [← he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) hm0)] at htri
    have hmean := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    change _ ≤ R
    dsimp [R]
    have hk : 0 ≤ (k : ℝ) * d ^ 2 := by positivity
    nlinarith
  have hs : (diagonalBatch X hB.1.eigenvectorUnitary) ⁻¹'
      {z : Fin k → Fin n → ℝ | R < |batchLogRatio X Y z|} ⊆
      {z | 2 * (Real.sqrt (∑ p, a p ^ 2) * Real.sqrt t + 2 * d * t) <
        |∑ p, a p * (z p ^ 2 - 1)|} := by
    intro z hz
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
    by_contra hb
    exact (not_lt_of_ge (hpoint z (le_of_not_gt hb))) hz
  have hmeas : MeasurableSet {z : Fin k → Fin n → ℝ | R < |batchLogRatio X Y z|} :=
    measurableSet_lt measurable_const (measurable_batchLogRatio X Y).abs
  change (gaussianBatch X k).real {z | R < |batchLogRatio X Y z|} ≤ _
  rw [← gaussianProduct_map_diagonalBatch X hB.1.eigenvectorUnitary]
  change ((gaussianProduct (Fin k × Fin n)).map (diagonalBatch X hB.1.eigenvectorUnitary)
    {z | R < |batchLogRatio X Y z|}).toReal ≤ _
  rw [Measure.map_apply (measurable_diagonalBatch _ _) hmeas]
  exact (measureReal_mono hs).trans htail

lemma gaussian_privacy_parameters {k : ℕ} {d δ : ℝ}
    (hd : 0 ≤ d) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    0 < Real.log (2 / δ) ∧ 2 * Real.exp (-Real.log (2 / δ)) = δ ∧
    (k : ℝ) * d ^ 2 + 2 * Real.sqrt (k * Real.log (2 / δ)) * d +
      2 * Real.log (2 / δ) * d ≤
      4 * (k * d ^ 2 + Real.sqrt (k * Real.log (1 / δ)) * d + Real.log (1 / δ) * d) := by
  have hδ1 : δ < 1 := by linarith
  have hL : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have ht : 0 < Real.log (2 / δ) := Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  have hlog : Real.log (2 / δ) = Real.log 2 + Real.log (1 / δ) := by
    rw [Real.log_div (by norm_num) hδ.ne', Real.log_div (by norm_num) hδ.ne', Real.log_one]
    ring
  have h2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hδ).mpr (by linarith))
  have htL : Real.log (2 / δ) ≤ 2 * Real.log (1 / δ) := by linarith
  have hroot : Real.sqrt (k * Real.log (2 / δ)) ≤ 2 * Real.sqrt (k * Real.log (1 / δ)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hh := mul_le_mul_of_nonneg_left htL (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hL.le]
  refine ⟨ht, ?_, ?_⟩
  · rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  · have hh := mul_le_mul_of_nonneg_right hroot hd
    have hl := mul_le_mul_of_nonneg_right htL hd
    have hk : 0 ≤ (k : ℝ) * d ^ 2 := by positivity
    nlinarith

/-- The concrete bound underlying Lemma 14, including empty dimensions or batches. -/
theorem gaussian_privacy {n k : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hd : covarianceDistance X Y < 1 / 2) :
    let d := covarianceDistance X Y
    HighProbability (gaussianBatch X k) δ (fun z => |batchLogRatio X Y z| ≤
      4 * (k * d ^ 2 + Real.sqrt (k * Real.log (1 / δ)) * d + Real.log (1 / δ) * d)) := by
  dsimp
  let d := covarianceDistance X Y
  let R := 4 * ((k : ℝ) * d ^ 2 + Real.sqrt (k * Real.log (1 / δ)) * d + Real.log (1 / δ) * d)
  obtain ⟨ht, he, hR⟩ := gaussian_privacy_parameters (k := k) (d := d) (frobenius_nonneg _) hδ hδhalf
  have htail := gaussian_logRatio_tail (k := k) hX hY hd ht
  rw [he] at htail
  have hs : {z : Fin k → Fin n → ℝ | ¬ |batchLogRatio X Y z| ≤ R} ⊆
      {z | (k : ℝ) * d ^ 2 + 2 * Real.sqrt (k * Real.log (2 / δ)) * d +
        2 * Real.log (2 / δ) * d < |batchLogRatio X Y z|} := by
    intro z hz
    exact hR.trans_lt (lt_of_not_ge hz)
  have hbad := (measureReal_mono hs).trans htail
  have hmeas : MeasurableSet {z : Fin k → Fin n → ℝ | |batchLogRatio X Y z| ≤ R} :=
    measurableSet_le (measurable_batchLogRatio X Y).abs measurable_const
  refine ⟨hmeas, ?_⟩
  have hc : (gaussianBatch X k).real {z | ¬ |batchLogRatio X Y z| ≤ R} =
      1 - (gaussianBatch X k).real {z | |batchLogRatio X Y z| ≤ R} := by
    change (gaussianBatch X k).real {z | |batchLogRatio X Y z| ≤ R}ᶜ = _
    rw [measureReal_compl hmeas, measureReal_univ_eq_one]
  rw [hc] at hbad
  change 1 - δ ≤ (gaussianBatch X k).real {z | |batchLogRatio X Y z| ≤ R}
  linarith

/-- Lemma 14, with the paper's `δ₁ ∈ (0,1/2)` and universal constant `4`. -/
theorem lemma14 : GaussianPrivacyStatement := by
  refine ⟨4, by norm_num, ?_⟩
  intro n k _hn _hk X Y hX hY δ hδ hδhalf hd
  exact gaussian_privacy hX hY hδ hδhalf hd

/-- The product-of-densities inequalities as displayed in the paper. -/
theorem lemma14_density {n k : ℕ}
    {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) (hd : covarianceDistance X Y < 1 / 2) :
    let d := covarianceDistance X Y
    let ε := 4 * (k * d ^ 2 + Real.sqrt (k * Real.log (1 / δ)) * d + Real.log (1 / δ) * d)
    HighProbability (gaussianBatch X k) δ (fun z =>
      Real.exp (-ε) * (∏ j, gaussianDensity Y (z j)) ≤ (∏ j, gaussianDensity X (z j)) ∧
      (∏ j, gaussianDensity X (z j)) ≤ Real.exp ε * (∏ j, gaussianDensity Y (z j))) := by
  dsimp
  simp only [batch_density_bound_iff]
  exact gaussian_privacy hX hY hδ hδhalf hd

end DPCut
