import DPCut.GaussianKL
import DPCut.OptimizerApproximation

/-! The second numerical bridge: relative covariance error bounds the KL
divergence of the actual Gaussian batch law. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators ENNReal MatrixOrder
namespace DPCut

lemma log_gap_le_square {r : ℝ} (hr : 1 / 2 ≤ r) :
    r - 1 - Real.log r ≤ (r - 1) ^ 2 := by
  have hr0 : 0 < r := by linarith
  by_cases hr1 : 1 ≤ r
  · have hl := Real.one_sub_inv_le_log_of_pos hr0
    have he : r - 2 + r⁻¹ = (r - 1) ^ 2 / r := by field_simp; ring
    calc
      r - 1 - Real.log r ≤ r - 2 + r⁻¹ := by linarith
      _ = (r - 1) ^ 2 / r := he
      _ ≤ (r - 1) ^ 2 := div_le_self (sq_nonneg _) hr1
  · have hr1 : r ≤ 1 := le_of_not_ge hr1
    let f : ℝ → ℝ := fun x => x - 1 - Real.log x - (x - 1) ^ 2
    let df : ℝ → ℝ := fun x => (x - 1) * (1 / x - 2)
    have hd (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) : HasDerivAt f (df x) x := by
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have h := (((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx0)).sub
        (((hasDerivAt_id x).sub_const 1).pow 2)
      convert h using 1
      dsimp [df]
      field_simp
    have hm : MonotoneOn f (Set.Icc (1 / 2 : ℝ) 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
        (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
      intro x hx
      have hx' := interior_subset hx
      change 1 / 2 ≤ x ∧ x ≤ 1 at hx'
      have hx0 : 0 < x := by linarith
      have hinv : 1 / x ≤ 2 := (div_le_iff₀ hx0).mpr (by linarith [hx'.1])
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx'.2) (sub_nonpos.mpr hinv)
    have h := hm ⟨hr, hr1⟩ ⟨by norm_num, le_rfl⟩ hr1
    dsimp [f] at h
    rw [Real.log_one] at h
    linarith

lemma normalizedCovariance_sub {n : ℕ} {Y : Mat n} (hY : Y.PosDef) (X : Mat n) :
    (CFC.sqrt Y)⁻¹ * (X - Y) * (CFC.sqrt Y)⁻¹ = normalizedCovariance Y X - 1 := by
  have h := normalizedCovariance_difference hY X
  have he : (CFC.sqrt Y)⁻¹ * (X - Y) * (CFC.sqrt Y)⁻¹ =
      -((CFC.sqrt Y)⁻¹ * (Y - X) * (CFC.sqrt Y)⁻¹) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [he, h, neg_neg]

theorem approximate_gaussian : ApproximateGaussianStatement := by
  intro n k _hn _hk X Y hX hY μ hμ hμhalf hclose
  let B := normalizedCovariance Y X
  let hB : B.PosDef := normalizedCovariance_posDef hY hX
  let r := hB.1.eigenvalues
  rw [normalizedCovariance_sub hY] at hclose
  change frobenius (B - 1) ≤ μ at hclose
  have hsq : (∑ i, (r i - 1) ^ 2) ≤ μ ^ 2 := by
    rw [← hermitian_frobenius_sub_one hB.1]
    exact pow_le_pow_left₀ (frobenius_nonneg _) hclose 2
  have hr (i : Fin n) : 1 / 2 ≤ r i := by
    have hi := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
      (fun j _ => sq_nonneg (r j - 1)) (Finset.mem_univ i)
    have hi' := hi.trans hsq
    nlinarith
  have hsum : (∑ i, (r i - 1 - Real.log (r i))) ≤ μ ^ 2 :=
    (Finset.sum_le_sum fun i _ => log_gap_le_square (hr i)).trans hsq
  have ht : (∑ i, r i) = (Y⁻¹ * X).trace := by
    have htr := hB.1.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at htr
    rw [← htr, normalizedCovariance_trace hY]
  have hl : (∑ i, Real.log (r i)) = Real.log X.det - Real.log Y.det := by
    rw [← normalizedCovariance_logdet hY hX, hB.1.det_eq_prod_eigenvalues]
    exact (Real.log_prod _ _ (fun i _ => (hB.eigenvalues_pos i).ne')).symm
  have he : (Y⁻¹ * X).trace - n + Real.log Y.det - Real.log X.det =
      ∑ i, (r i - 1 - Real.log (r i)) := by
    simp only [Finset.sum_sub_distrib, ht, hl, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [gaussianBatch_klDiv hX hY, he]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ k / 2 by positivity)
  nlinarith

end DPCut
