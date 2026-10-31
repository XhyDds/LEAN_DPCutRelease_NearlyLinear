import DPCut.SDPArithmeticCoordinates
import DPCut.FiniteArithmetic

/-! Scalar implementations of the remaining first-order oracle blocks. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators RealInnerProductSpace
namespace DPCut.SDPCoordinates.Counted
open Arithmetic
attribute [local instance] Classical.propDecidable

def boundedObjective {n : ℕ} (B : ℝ) (D : Weights n) : Arithmetic (Weights n) := do
  let s ← Arithmetic.sum fun e => Arithmetic.abs (D e)
  let large ← Arithmetic.lt B s
  Arithmetic.pure (if large then 0 else D)

@[simp] lemma boundedObjective_value {n : ℕ} (B : ℝ) (D : Weights n) :
    (boundedObjective B D).value = DPCut.boundedObjective B D := by
  simp only [boundedObjective, monad_bind_value, Arithmetic.sum_value, Arithmetic.abs_value,
    Arithmetic.lt, pure_value, decide_eq_true_eq, DPCut.boundedObjective, l1]
  split_ifs <;> first | rfl | linarith

lemma boundedObjective_steps {n : ℕ} (B : ℝ) (D : Weights n) :
    (boundedObjective B D).steps ≤ 3*Fintype.card (Edge n)+1 := by
  have h := sum_steps_le (fun e => Arithmetic.abs (D e)) (fun e => abs_steps (D e))
  simpa [boundedObjective, Arithmetic.lt, Nat.mul_comm] using Nat.add_le_add_right h 1

def objectiveMatrix {n : ℕ} (D : Weights n) : Arithmetic (Mat n) :=
  collect fun i => collect fun j => Arithmetic.sum fun e => do
    let d ← Arithmetic.div (D e) 4
    Arithmetic.mul d (edgeVector e i * edgeVector e j)

@[simp] lemma objectiveMatrix_value {n : ℕ} (D : Weights n) :
    (objectiveMatrix D).value = DPCut.objectiveMatrix D := by
  simp only [objectiveMatrix, collect_value, Arithmetic.sum_value, monad_bind_value,
    Arithmetic.div, Arithmetic.mul]
  ext i j
  simp [DPCut.objectiveMatrix, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]

lemma objectiveMatrix_steps {n : ℕ} (D : Weights n) :
    (objectiveMatrix D).steps = n*(n*(3*Fintype.card (Edge n)+1)+1) := by
  simp [objectiveMatrix, collect_steps, Arithmetic.sum_steps, Arithmetic.div, Arithmetic.mul,
    Nat.mul_comm]

def matrixPairing {n : ℕ} (A X : Mat n) : Arithmetic ℝ :=
  Arithmetic.sum fun ij : Fin n × Fin n => Arithmetic.mul (A ij.1 ij.2) (X ij.1 ij.2)

@[simp] lemma matrixPairing_value {n : ℕ} (A X : Mat n) :
    (matrixPairing A X).value = DPCut.matrixPairing A X := by
  simp [matrixPairing, Arithmetic.mul, DPCut.matrixPairing, Fintype.sum_prod_type]

lemma matrixPairing_steps {n : ℕ} (A X : Mat n) : (matrixPairing A X).steps = 2*n^2 := by
  simp [matrixPairing, Arithmetic.sum_steps, Arithmetic.mul, Fintype.card_prod]
  ring

def slack {n : ℕ} (X : Mat n) : Arithmetic (Mat n) := do
  let r ← Arithmetic.div 1 n
  collect fun i => collect fun j => Arithmetic.sub (X i j) (if i=j then r else 0)

@[simp] lemma slack_value {n : ℕ} (X : Mat n) :
    (slack X).value = X - (1/(n:ℝ)) • 1 := by
  simp only [slack, monad_bind_value, Arithmetic.div, collect_value, Arithmetic.sub]
  ext i j
  by_cases h : i=j <;> simp [h]

lemma slack_steps {n : ℕ} (X : Mat n) : (slack X).steps = 1+2*n^2+n := by
  simp [slack, collect_steps, Arithmetic.div, Arithmetic.sub]
  ring

def gradient {n : ℕ} (lam : ℝ) (A Xinv : Mat n) : Arithmetic (Mat n) :=
  collect fun i => collect fun j => do
    let a ← Arithmetic.mul lam (Xinv i j)
    Arithmetic.add (A i j) a

@[simp] lemma gradient_value {n : ℕ} (lam : ℝ) (A Xinv : Mat n) :
    (gradient lam A Xinv).value = A + lam • Xinv := by
  simp [gradient, Arithmetic.mul, Arithmetic.add]
  rfl

lemma gradient_steps {n : ℕ} (lam : ℝ) (A Xinv : Mat n) :
    (gradient lam A Xinv).steps = 3*n^2+n := by
  simp [gradient, collect_steps, Arithmetic.mul, Arithmetic.add]
  ring

def negativeOuter {n : ℕ} (v : Fin n → ℝ) : Arithmetic (Mat n) :=
  collect fun i => collect fun j => do
    let a ← Arithmetic.mul (v i) (v j)
    Arithmetic.neg a

@[simp] lemma negativeOuter_value {n : ℕ} (v : Fin n → ℝ) :
    (negativeOuter v).value = -(Matrix.vecMulVec v v) := by
  simp [negativeOuter, Arithmetic.mul, Arithmetic.neg, Matrix.vecMulVec]
  rfl

lemma negativeOuter_steps {n : ℕ} (v : Fin n → ℝ) :
    (negativeOuter v).steps = 3*n^2+n := by
  simp [negativeOuter, collect_steps, Arithmetic.mul, Arithmetic.neg]
  ring

def norm {n : ℕ} (x : Space n) : Arithmetic ℝ := do
  let s ← Arithmetic.sum fun ij : Fin n × Fin n => Arithmetic.mul (x ij) (x ij)
  Arithmetic.sqrt s

@[simp] lemma norm_value {n : ℕ} (x : Space n) : (norm x).value = ‖x‖ := by
  simp only [norm, monad_bind_value, Arithmetic.sum_value, Arithmetic.mul, Arithmetic.sqrt]
  have hh : (∑ ij, x ij*x ij) = ‖x‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp [PiLp.inner_apply]
  rw [hh, Real.sqrt_sq (norm_nonneg x)]

lemma norm_steps {n : ℕ} (x : Space n) : (norm x).steps = 2*n^2+1 := by
  simp [norm, Arithmetic.sum_steps, Arithmetic.mul, Arithmetic.sqrt, Fintype.card_prod]
  ring

end DPCut.SDPCoordinates.Counted
