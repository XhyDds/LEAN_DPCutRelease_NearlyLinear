import DPCut.MatrixElimination

/-! Positive-definite linear systems solved by scalar Schur elimination. -/
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators
namespace DPCut.MatrixElimination

lemma pivot_pos {n : ℕ} {M : Mat (n+1)} (hM : M.PosDef) : 0 < M 0 0 := by
  have h := hM.2 (Pi.single 0 1) (by intro h; have := congrFun h 0; simp at this)
  simpa [star_trivial, qform_single] using h

lemma schur_posDef {n : ℕ} {M : Mat (n+1)} (hM : M.PosDef) : (schur M).PosDef := by
  refine ⟨schur_hermitian hM.1, fun v hv => ?_⟩
  have hh := hM.2 (prepend (-(row M ⬝ᵥ v) / M 0 0) v) (by
    intro h
    apply hv
    funext i
    exact congrFun h i.succ)
  simp only [star_trivial] at hh ⊢
  change 0 < qform M _ at hh
  rwa [qform_lift hM.1 (pivot_pos hM).ne'] at hh

lemma mulVec_prepend_zero {n : ℕ} (M : Mat (n+1)) (t : ℝ) (v : Fin n → ℝ) :
    (M *ᵥ prepend t v) 0 = M 0 0*t + row M ⬝ᵥ v := by
  simp [Matrix.mulVec, dotProduct, prepend, Fin.sum_univ_succ, row]

lemma mulVec_prepend_succ {n : ℕ} {M : Mat (n+1)} (hM : M.IsHermitian)
    (t : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (M *ᵥ prepend t v) i.succ = row M i*t + (tail M *ᵥ v) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, prepend, Fin.cons_zero,
    Fin.cons_succ, row, tail]
  rw [symmetric hM 0 i.succ]

lemma schur_mulVec {n : ℕ} (M : Mat (n+1)) (v : Fin n → ℝ) (i : Fin n) :
    (schur M *ᵥ v) i = (tail M *ᵥ v) i - row M i * (row M ⬝ᵥ v) / M 0 0 := by
  simp only [Matrix.mulVec, dotProduct, schur, sub_mul, Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _; ring

/-- This total recursive function uses only field arithmetic. Correctness is
claimed on positive-definite inputs; hence every pivot used there is positive. -/
def solve : {n : ℕ} → Mat n → (Fin n → ℝ) → (Fin n → ℝ)
  | 0, _, _ => Fin.elim0
  | _+1, M, b =>
    let y := solve (schur M) (fun i => b i.succ - row M i * b 0 / M 0 0)
    prepend ((b 0 - row M ⬝ᵥ y) / M 0 0) y

lemma solve_correct {n : ℕ} (M : Mat n) (hM : M.PosDef) (b : Fin n → ℝ) :
    M *ᵥ solve M b = b := by
  induction n with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
    let y := solve (schur M) (fun i => b i.succ - row M i * b 0 / M 0 0)
    have hy := ih (schur M) (schur_posDef hM) (fun i => b i.succ - row M i * b 0 / M 0 0)
    have ha := (pivot_pos hM).ne'
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (M *ᵥ prepend ((b 0 - row M ⬝ᵥ y)/M 0 0) y) 0 = b 0
      rw [mulVec_prepend_zero]
      field_simp; ring
    · change (M *ᵥ prepend ((b 0 - row M ⬝ᵥ y)/M 0 0) y) j.succ = b j.succ
      rw [mulVec_prepend_succ hM.1]
      have hh := congrFun hy j
      change (schur M *ᵥ y) j = _ at hh
      rw [schur_mulVec] at hh
      calc
        _ = (tail M *ᵥ y) j - row M j * (row M ⬝ᵥ y) / M 0 0 + row M j * b 0 / M 0 0 := by ring
        _ = _ := by rw [hh]; ring

def inverse {n : ℕ} (M : Mat n) : Mat n := fun i j => solve M (Pi.single j 1) i

lemma mul_inverse {n : ℕ} (M : Mat n) (hM : M.PosDef) : M * inverse M = 1 := by
  ext i j
  have hh := congrFun (solve_correct M hM (Pi.single j 1)) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, inverse, Matrix.one_apply, Pi.single_apply, eq_comm] using hh

lemma inverse_eq {n : ℕ} (M : Mat n) (hM : M.PosDef) : inverse M = M⁻¹ := by
  letI := hM.isUnit.invertible
  calc
    inverse M = M⁻¹ * (M * inverse M) := by simp
    _ = M⁻¹ := by rw [mul_inverse M hM, Matrix.mul_one]

end DPCut.MatrixElimination
