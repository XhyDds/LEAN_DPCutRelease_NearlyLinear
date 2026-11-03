import DPCut.Optimizer

/-!
Lemma 13 (`lem:stability_of_optimizer`).
Only this lemma and its immediate optimizer prerequisites are proved here.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder

namespace DPCut

lemma fractionalQuery_comparable {n : ℕ} (hn : 2 ≤ n) {X Y : Mat n}
    (hX : X ∈ feasible n) (hY : Y ∈ feasible n)
    (hsmall : covarianceDistance X Y ≤ 1 / 2) (e : Edge n) :
    fractionalQuery Y e / 2 ≤ fractionalQuery X e ∧
      fractionalQuery X e ≤ 2 * fractionalQuery Y e := by
  have ha := (feasible_fractionalQuery_bounds hn hX e).1
  have hb := (feasible_fractionalQuery_bounds hn hY e).1
  have ht := frobenius_nonneg (relativeDifference X Y)
  change 0 ≤ covarianceDistance X Y at ht
  have ht2 : covarianceDistance X Y ^ 2 ≤ 1 / 4 := by nlinarith
  have hdiff := fractionalQuery_difference_sq_le hn hX hY e
  have hmul := mul_le_mul_of_nonneg_left ht2 (mul_nonneg ha.le hb.le)
  have hd : (fractionalQuery Y e - fractionalQuery X e) ^ 2 ≤
      fractionalQuery X e * fractionalQuery Y e / 4 := by nlinarith
  constructor
  · by_contra h
    push_neg at h
    have hp := mul_nonneg
      (show 0 ≤ fractionalQuery Y e - 2 * fractionalQuery X e by linarith)
      (show 0 ≤ fractionalQuery Y e - fractionalQuery X e / 2 by linarith)
    nlinarith [mul_pos ha hb]
  · by_contra h
    push_neg at h
    have hp := mul_nonneg
      (show 0 ≤ fractionalQuery X e - 2 * fractionalQuery Y e by linarith)
      (show 0 ≤ fractionalQuery X e - fractionalQuery Y e / 2 by linarith)
    nlinarith [mul_pos ha hb]

/-- The exact optimizer stability bound and the factor-two comparison from Lemma 13. -/
theorem lemma13 : OptimizerStabilityStatement := by
  intro n hn lam hlam A₀ A₁ X₀ X₁ ξ hA hX₀ hX₁
  have ht := frobenius_nonneg (relativeDifference X₀ X₁)
  change 0 ≤ covarianceDistance X₀ X₁ at ht
  constructor
  · let S : ℝ := ∑ e, |ξ e| * Real.sqrt (fractionalQuery X₀ e * fractionalQuery X₁ e)
    have hS : 0 ≤ S := Finset.sum_nonneg fun e _ =>
      mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have henergy := matrixOptimizer_energy hn hX₀ hX₁
    have hpair : matrixPairing (A₁ - A₀) (X₁ - X₀) =
        ∑ e, ξ e * (fractionalQuery X₁ e - fractionalQuery X₀ e) := by
      rw [hA, add_sub_cancel_left, matrixPairing_sub_right,
        matrixPairing_objectiveMatrix ξ hX₀.1, matrixPairing_objectiveMatrix ξ hX₁.1]
      simp [pairing, mul_sub, Finset.sum_sub_distrib]
    have hrhs : matrixPairing (A₁ - A₀) (X₁ - X₀) ≤ S * covarianceDistance X₀ X₁ := by
      rw [hpair]
      calc
        _ ≤ ∑ e, |ξ e| * |fractionalQuery X₁ e - fractionalQuery X₀ e| := by
          apply Finset.sum_le_sum
          intro e _
          simpa only [abs_mul] using le_abs_self (ξ e *
            (fractionalQuery X₁ e - fractionalQuery X₀ e))
        _ ≤ ∑ e, |ξ e| * (Real.sqrt (fractionalQuery X₀ e * fractionalQuery X₁ e) *
            covarianceDistance X₀ X₁) := by
          apply Finset.sum_le_sum
          intro e _
          exact mul_le_mul_of_nonneg_left (fractionalQuery_difference_le hn hX₀.1 hX₁.1 e)
            (abs_nonneg _)
        _ = S * covarianceDistance X₀ X₁ := by simp only [S, Finset.sum_mul, mul_assoc]
    have he := henergy.trans hrhs
    change covarianceDistance X₀ X₁ ≤ S / lam
    apply (le_div_iff₀ hlam).mpr
    rcases eq_or_lt_of_le ht with hz | hz
    · rw [← hz, zero_mul]
      exact hS
    · apply (mul_le_mul_iff_of_pos_right hz).mp
      nlinarith [he]
  · intro hsmall e
    exact fractionalQuery_comparable hn hX₀.1 hX₁.1 hsmall e

/-- Lemma 13 specialized to the actual choices `X_D` and `X_(D+ξ)`. -/
theorem optimizer_stability {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    (D ξ : Weights n) :
    covarianceDistance (optimizer lam D) (optimizer lam (D + ξ)) ≤
      (∑ e, |ξ e| * Real.sqrt (fractionalQuery (optimizer lam D) e *
        fractionalQuery (optimizer lam (D + ξ)) e)) / lam ∧
    (covarianceDistance (optimizer lam D) (optimizer lam (D + ξ)) ≤ 1 / 2 → ∀ e,
      fractionalQuery (optimizer lam (D + ξ)) e / 2 ≤ fractionalQuery (optimizer lam D) e ∧
      fractionalQuery (optimizer lam D) e ≤ 2 * fractionalQuery (optimizer lam (D + ξ)) e) :=
  lemma13 n hn lam hlam (objectiveMatrix D) (objectiveMatrix (D + ξ))
    (optimizer lam D) (optimizer lam (D + ξ)) ξ (objectiveMatrix_add D ξ)
    ((isOptimizer_iff_matrixOptimizer lam D _).mp (optimizer_isOptimizer hn lam D))
    ((isOptimizer_iff_matrixOptimizer lam (D + ξ) _).mp (optimizer_isOptimizer hn lam (D + ξ)))

end DPCut
