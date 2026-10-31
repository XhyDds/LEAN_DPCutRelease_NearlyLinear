import DPCut.Lemma13
import DPCut.WitnessNormalization

/-! Masked objective discrepancies and the predictable local charge in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace DPCut

def queryMax {n : ℕ} (X Y : Mat n) : Weights n :=
  fun e => max (fractionalQuery X e) (fractionalQuery Y e)

def oracleSensitivity {n : ℕ} (ζ r : Weights n) (X Y : Mat n) : ℝ :=
  ∑ e, |ζ e| * r e * queryMax X Y e

lemma queryMax_bounds {n : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n) (e : Edge n) :
    0 ≤ queryMax X Y e ∧ queryMax X Y e ≤ 1 := by
  obtain ⟨hx, hx1⟩ := feasible_fractionalQuery_bounds hn hX e
  obtain ⟨hy, hy1⟩ := feasible_fractionalQuery_bounds hn hY e
  exact ⟨hx.le.trans (le_max_left _ _), max_le hx1 hy1⟩

lemma oracleSensitivity_bounds {n : ℕ} (hn : 2 ≤ n) {r : Weights n} (hr : IsMask r)
    (ζ : Weights n) {X Y : Mat n} (hX : X ∈ feasible n) (hY : Y ∈ feasible n) :
    0 ≤ oracleSensitivity ζ r X Y ∧ oracleSensitivity ζ r X Y ≤ l1 ζ := by
  constructor
  · exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (hr e).1) (queryMax_bounds hn hX hY e).1
  · apply Finset.sum_le_sum
    intro e _
    have hq := queryMax_bounds hn hX hY e
    calc
      |ζ e| * r e * queryMax X Y e ≤ |ζ e| * r e :=
        mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (hr e).1) hq.2
      _ ≤ |ζ e| := mul_le_of_le_one_right (abs_nonneg _) (hr e).2

lemma masked_plus_discrepancy {n : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (w w' h r : Weights n) (hr : IsMask r) (e : Edge n) :
    |plusDiscrepancy γ w' h r e - plusDiscrepancy γ w h r e| ≤
      2 * |(w - w') e| * r e := by
  have he : plusDiscrepancy γ w' h r e - plusDiscrepancy γ w h r e =
      (1 + γ) * (w e - w' e) * r e := by unfold plusDiscrepancy; ring
  rw [he, abs_mul, abs_mul, abs_of_pos (by linarith : 0 < 1 + γ), abs_of_nonneg (hr e).1]
  change (1 + γ) * |w e - w' e| * r e ≤ 2 * |w e - w' e| * r e
  nlinarith [mul_nonneg (abs_nonneg (w e - w' e)) (hr e).1]

lemma masked_minus_discrepancy {n : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (w w' h r : Weights n) (hr : IsMask r) (e : Edge n) :
    |minusDiscrepancy γ w' h r e - minusDiscrepancy γ w h r e| ≤
      2 * |(w - w') e| * r e := by
  have he : minusDiscrepancy γ w' h r e - minusDiscrepancy γ w h r e =
      -(1 - γ) * (w e - w' e) * r e := by unfold minusDiscrepancy; ring
  rw [he, abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith : 0 < 1 - γ),
    abs_of_nonneg (hr e).1]
  change (1 - γ) * |w e - w' e| * r e ≤ 2 * |w e - w' e| * r e
  nlinarith [mul_nonneg (abs_nonneg (w e - w' e)) (hr e).1]

lemma optimizer_covariance_le_charge {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (D D' ζ r : Weights n) (hr : IsMask r)
    (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e) :
    covarianceDistance (optimizer lam D) (optimizer lam D') ≤
      2 * oracleSensitivity ζ r (optimizer lam D) (optimizer lam D') / lam := by
  have hx := (optimizer_isOptimizer hn lam D).1
  have hy := (optimizer_isOptimizer hn lam D').1
  have h := (optimizer_stability hn hlam D (D' - D)).1
  rw [add_sub_cancel] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ hlam.le
  rw [oracleSensitivity, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hq := queryMax_bounds hn hx hy e
  have ha := (feasible_fractionalQuery_bounds hn hx e).1.le
  have hb := (feasible_fractionalQuery_bounds hn hy e).1.le
  have hs : Real.sqrt (fractionalQuery (optimizer lam D) e *
      fractionalQuery (optimizer lam D') e) ≤ queryMax (optimizer lam D) (optimizer lam D') e := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hq.1, ?_⟩
    exact (mul_le_mul (le_max_left _ _) (le_max_right _ _) hb hq.1).trans_eq (pow_two _).symm
  calc
    _ ≤ (2 * |ζ e| * r e) * queryMax (optimizer lam D) (optimizer lam D') e :=
      mul_le_mul (hξ e) hs (Real.sqrt_nonneg _)
        (mul_nonneg (by positivity) (hr e).1)
    _ = _ := by ring

lemma score_sensitivity_le_charge {n : ℕ} (D D' ζ r g q : Weights n)
    (hr : IsMask r) (hξ : ∀ e, |D' e - D e| ≤ 2 * |ζ e| * r e)
    (hg : ∀ e, 0 ≤ g e ∧ g e ≤ 2 * q e) :
    |pairing D g - pairing D' g| ≤ 4 * ∑ e, |ζ e| * r e * q e := by
  have he : pairing D g - pairing D' g = ∑ e, (D e - D' e) * g e := by
    simp [pairing, sub_mul, Finset.sum_sub_distrib]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  rw [abs_mul, abs_sub_comm, abs_of_nonneg (hg e).1]
  have hm := mul_le_mul (hξ e) (hg e).2 (hg e).1
    (mul_nonneg (by positivity) (hr e).1)
  nlinarith

end DPCut
