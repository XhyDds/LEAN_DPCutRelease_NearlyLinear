import DPCut.MatrixArithmetic

/-! Counted scalar implementations of solves, inverses, determinants, and
covariance factors. The bounds are uniform over all real input entries. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace DPCut.MatrixElimination.Counted
open Arithmetic

def solve : {n : ℕ} → Mat n → (Fin n → ℝ) → Arithmetic (Fin n → ℝ)
  | 0, _, _ => Arithmetic.pure Fin.elim0
  | _+1, M, b => do
    let S ← schur M
    let c ← collect fun i => do
      let t ← Arithmetic.mul (row M i) (b 0)
      let t ← Arithmetic.div t (M 0 0)
      Arithmetic.sub (b i.succ) t
    let y ← solve S c
    let r ← dot (row M) y
    let r ← Arithmetic.sub (b 0) r
    let t ← Arithmetic.div r (M 0 0)
    Arithmetic.pure (prepend t y)

@[simp] lemma solve_value {n : ℕ} (M : Mat n) (b : Fin n → ℝ) :
    (solve M b).value = MatrixElimination.solve M b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [solve, Arithmetic.mul, Arithmetic.div, Arithmetic.sub, ih, MatrixElimination.solve]

lemma solve_steps {n : ℕ} (M : Mat n) (b : Fin n → ℝ) :
    (solve M b).steps ≤ 20*(n+1)^3 := by
  induction n with
  | zero => simp [solve]
  | succ n ih =>
    have h := ih (MatrixElimination.schur M) (fun i => b i.succ - row M i*b 0/M 0 0)
    simp only [solve, monad_bind_steps, monad_bind_value, schur_value, schur_steps,
      collect_value, collect_steps, Arithmetic.mul, Arithmetic.div, Arithmetic.sub,
      dot_steps, dot_value, pure_steps]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    nlinarith

def inverse {n : ℕ} (M : Mat n) : Arithmetic (Mat n) := do
  let cols ← collect (fun j => solve M (Pi.single j 1))
  Arithmetic.pure (fun i j => cols j i)

@[simp] lemma inverse_value {n : ℕ} (M : Mat n) :
    (inverse M).value = MatrixElimination.inverse M := by
  simp [inverse]
  rfl

lemma inverse_steps {n : ℕ} (M : Mat n) : (inverse M).steps ≤ 21*(n+1)^4 := by
  have h := collect_steps_le (fun j : Fin n => solve M (Pi.single j 1)) (fun j => solve_steps M _)
  simp only [inverse, monad_bind_steps, pure_steps, Nat.add_zero]
  have hp : 1 ≤ (n+1)^3 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    _ ≤ n*(20*(n+1)^3+1) := h
    _ ≤ (n+1)*(20*(n+1)^3+(n+1)^3) := Nat.mul_le_mul (Nat.le_succ n) (by omega)
    _ = _ := by ring

def factor : {n : ℕ} → Mat n → Arithmetic (Mat n)
  | 0, _ => Arithmetic.pure 1
  | _+1, M => do
    let a ← Arithmetic.sqrt (M 0 0)
    let S ← schur M
    let L ← factor S
    let c ← collect fun i => Arithmetic.div (row M i) a
    Arithmetic.pure (lowerBlock a c L)

@[simp] lemma factor_value {n : ℕ} (M : Mat n) :
    (factor M).value = MatrixElimination.factor M := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factor, Arithmetic.sqrt, Arithmetic.div, ih, MatrixElimination.factor]

lemma factor_steps {n : ℕ} (M : Mat n) : (factor M).steps ≤ 20*(n+1)^3 := by
  induction n with
  | zero => simp [factor]
  | succ n ih =>
    have h := ih (MatrixElimination.schur M)
    simp only [factor, monad_bind_steps, Arithmetic.sqrt,
      schur_value, schur_steps, collect_steps, Arithmetic.div, pure_steps]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    nlinarith

def determinant : {n : ℕ} → Mat n → Arithmetic ℝ
  | 0, _ => Arithmetic.pure 1
  | _+1, M => do
    let S ← schur M
    let d ← determinant S
    Arithmetic.mul (M 0 0) d

@[simp] lemma determinant_value {n : ℕ} (M : Mat n) :
    (determinant M).value = MatrixElimination.determinant M := by
  induction n with
  | zero => rfl
  | succ n ih => simp [determinant, Arithmetic.mul, ih, MatrixElimination.determinant]

lemma determinant_steps {n : ℕ} (M : Mat n) : (determinant M).steps ≤ 10*(n+1)^3 := by
  induction n with
  | zero => simp [determinant]
  | succ n ih =>
    have h := ih (MatrixElimination.schur M)
    simp only [determinant, monad_bind_steps, schur_value, schur_steps, Arithmetic.mul]
    nlinarith

def mulVec {n : ℕ} (M : Mat n) (v : Fin n → ℝ) : Arithmetic (Fin n → ℝ) :=
  collect fun i => dot (M i) v

@[simp] lemma mulVec_value {n : ℕ} (M : Mat n) (v : Fin n → ℝ) :
    (mulVec M v).value = M *ᵥ v := by simp [mulVec]; rfl

lemma mulVec_steps {n : ℕ} (M : Mat n) (v : Fin n → ℝ) : (mulVec M v).steps = n*(2*n+1) := by
  simp [mulVec, collect_steps]

end DPCut.MatrixElimination.Counted
