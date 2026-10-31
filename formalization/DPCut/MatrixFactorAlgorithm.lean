import DPCut.MatrixSPDAlgorithm

/-! Recursive Cholesky factorization and determinant computation. Only scalar
field operations and scalar square root occur in the algorithms. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace DPCut.MatrixElimination

def lowerBlock {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) : Mat (n+1) :=
  Fin.cons (Fin.cons a 0) (fun i => Fin.cons (c i) (D i))

@[simp] lemma lowerBlock_zero_zero {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) :
    lowerBlock a c D 0 0 = a := rfl
@[simp] lemma lowerBlock_zero_succ {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) (j : Fin n) :
    lowerBlock a c D 0 j.succ = 0 := rfl
@[simp] lemma lowerBlock_succ_zero {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) (i : Fin n) :
    lowerBlock a c D i.succ 0 = c i := rfl
@[simp] lemma lowerBlock_succ_succ {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) (i j : Fin n) :
    lowerBlock a c D i.succ j.succ = D i j := rfl

lemma det_lowerBlock {n : ℕ} (a : ℝ) (c : Fin n → ℝ) (D : Mat n) :
    (lowerBlock a c D).det = a * D.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [Matrix.submatrix, lowerBlock]
  left; rfl

def factor : {n : ℕ} → Mat n → Mat n
  | 0, _ => 1
  | _+1, M => lowerBlock (Real.sqrt (M 0 0)) (fun i => row M i / Real.sqrt (M 0 0)) (factor (schur M))

lemma factor_correct {n : ℕ} (M : Mat n) (hM : M.PosDef) : factor M * (factor M)ᵀ = M := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    have hi := ih (schur M) (schur_posDef hM)
    have ha := pivot_pos hM
    have hs : (Real.sqrt (M 0 0))^2 = M 0 0 := Real.sq_sqrt ha.le
    have hn : Real.sqrt (M 0 0) ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simpa [factor, Matrix.mul_apply, Fin.sum_univ_succ, pow_two] using hs
      · simp only [factor, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
          lowerBlock_zero_zero, lowerBlock_zero_succ, lowerBlock_succ_zero, lowerBlock_succ_succ,
          zero_mul, Finset.sum_const_zero, add_zero]
        dsimp [row]; field_simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [factor, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
          lowerBlock_zero_zero, lowerBlock_zero_succ, lowerBlock_succ_zero, lowerBlock_succ_succ,
          mul_zero, Finset.sum_const_zero, add_zero]
        rw [div_mul_cancel₀ _ hn, row, symmetric hM.1]
      · simp only [factor, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
          lowerBlock_succ_zero, lowerBlock_succ_succ]
        change (row M i / Real.sqrt (M 0 0)) * (row M j / Real.sqrt (M 0 0)) +
          (factor (schur M) * (factor (schur M))ᵀ) i j = M i.succ j.succ
        rw [hi]
        simp only [schur, tail]
        rw [div_mul_div_comm, ← pow_two, hs]
        ring

/-- Computing the determinant through the pivots avoids the exponential
permutation formula used to specify `Matrix.det`. -/
def determinant : {n : ℕ} → Mat n → ℝ
  | 0, _ => 1
  | _+1, M => M 0 0 * determinant (schur M)

lemma determinant_correct {n : ℕ} (M : Mat n) (hM : M.PosDef) : determinant M = M.det := by
  induction n with
  | zero => simp [determinant, Matrix.det_isEmpty]
  | succ n ih =>
    have hi := ih (schur M) (schur_posDef hM)
    have hs := Real.sq_sqrt (pivot_pos hM).le
    have hm := congrArg Matrix.det (factor_correct M hM)
    have hd := congrArg Matrix.det (factor_correct (schur M) (schur_posDef hM))
    simp only [Matrix.det_mul, Matrix.det_transpose] at hm hd
    rw [factor, det_lowerBlock] at hm
    rw [determinant, hi, ← hm, ← hd]
    nlinarith [hs]

end DPCut.MatrixElimination
