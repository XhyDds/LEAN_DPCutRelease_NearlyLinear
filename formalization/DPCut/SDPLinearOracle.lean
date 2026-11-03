import DPCut.OptimizerApproximation
import DPCut.LSWStatement

/-! Matrix objective certificates and the semantic linear-algebra interface.
`VerifiedLinearAlgebra.lean` constructs this interface from scalar elimination
and proves the operation counts used by the LSW-based theorem. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped RealInnerProductSpace MatrixOrder
namespace DPCut

/-- Semantic interface for a measurable negative quadratic-form witness.
It can be supplied by a caller, or constructed by `MatrixElimination.primitives`.
`theorem1_of_lsw` uses the latter verified implementation. -/
structure LinearAlgebraPrimitives where
  psdWitness : ∀ n, Mat n → Option (Fin n → ℝ)
  measurable_psdWitness : ∀ n, Measurable (psdWitness n)
  none_iff : ∀ n (M : Mat n), M.IsHermitian →
    (psdWitness n M = none ↔ M.PosSemidef)
  witness_negative : ∀ n (M : Mat n) v, psdWitness n M = some v →
    v ⬝ᵥ (M *ᵥ v) < 0

/-- Public budget for dense PSD separation. `Counted.totalPSD_steps` proves
this bound from scalar operations. Inversion is accounted for separately in
the complete first-order oracle budget. -/
def linearAlgebraPrimitiveCost (n : ℕ) : ℕ := 100 * (n + 1) ^ 3

lemma logdet_tangent_upper {n : ℕ} {X Y : Mat n} (hX : X.PosDef) (hY : Y.PosDef) :
    Real.log Y.det - Real.log X.det ≤ (X⁻¹ * Y).trace - n := by
  let hB := normalizedCovariance_posDef hX hY
  have hl : (∑ i, Real.log (hB.1.eigenvalues i)) = Real.log Y.det - Real.log X.det := by
    rw [← normalizedCovariance_logdet hX hY, hB.1.det_eq_prod_eigenvalues]
    exact (Real.log_prod _ _ (fun i _ => (hB.eigenvalues_pos i).ne')).symm
  have ht : (∑ i, hB.1.eigenvalues i) = (X⁻¹ * Y).trace := by
    have ht0 := hB.1.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at ht0
    rw [← ht0, normalizedCovariance_trace hX]
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => Real.log_le_sub_one_of_pos (hB.eigenvalues_pos i))
  simpa [Finset.sum_sub_distrib, hl, ht] using h

lemma matrixPairing_smul_left {n : ℕ} (a : ℝ) (A X : Mat n) :
    matrixPairing (a • A) X = a * matrixPairing A X := by
  simp [matrixPairing, Finset.mul_sum, mul_assoc]

/-- A supergradient certificate for the actual log-determinant objective. -/
theorem objective_tangent_upper {n : ℕ} (hn : 2 ≤ n) {lam : ℝ} (hlam : 0 ≤ lam)
    (D : Weights n) {X Y : Mat n} (hX : X ∈ feasible n) (hY : Y ∈ feasible n) :
    objective lam D Y ≤ objective lam D X +
      matrixPairing (objectiveMatrix D + lam • X⁻¹) (Y - X) := by
  have hpX := feasible_posDef hn hX
  have hpY := feasible_posDef hn hY
  have hlog := mul_le_mul_of_nonneg_left (logdet_tangent_upper hpX hpY) hlam
  have hi : X⁻¹ * X = 1 := by letI := hpX.isUnit.invertible; simp
  have hinv : (X⁻¹)ᵀ = X⁻¹ := posDef_transpose hpX.inv
  rw [matrixPairing_add_left, matrixPairing_smul_left, matrixPairing_sub_right,
    matrixPairing_objectiveMatrix D hY, matrixPairing_objectiveMatrix D hX,
    matrixPairing_eq_trace, hinv, Matrix.mul_sub, Matrix.trace_sub, hi, Matrix.trace_one]
  unfold objective
  simp only [Fintype.card_fin] at *
  nlinarith

end DPCut
