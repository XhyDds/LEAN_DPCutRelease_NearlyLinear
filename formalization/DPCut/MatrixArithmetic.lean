import DPCut.ScalarArithmetic

/-! Scalar-operation implementations of the elimination algorithms. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace DPCut.MatrixElimination
namespace Counted
open Arithmetic

def schur {n : ℕ} (M : Mat (n+1)) : Arithmetic (Mat n) :=
  collect fun i => collect fun j => do
    let p ← Arithmetic.mul (row M i) (row M j)
    let q ← Arithmetic.div p (M 0 0)
    Arithmetic.sub (tail M i j) q

@[simp] lemma schur_value {n : ℕ} (M : Mat (n+1)) :
    (schur M).value = MatrixElimination.schur M := by
  simp [schur, Arithmetic.mul, Arithmetic.div, Arithmetic.sub]
  rfl

lemma schur_steps {n : ℕ} (M : Mat (n+1)) : (schur M).steps = 4*n^2+n := by
  simp [schur, collect_steps, Arithmetic.mul, Arithmetic.div, Arithmetic.sub]
  ring

def symmetrize {n : ℕ} (M : Mat n) : Arithmetic (Mat n) :=
  collect fun i => collect fun j => do
    let p ← Arithmetic.add (M i j) (M j i)
    Arithmetic.div p 2

@[simp] lemma symmetrize_value {n : ℕ} (M : Mat n) :
    (symmetrize M).value = MatrixElimination.symmetrize M := by
  simp [symmetrize, Arithmetic.add, Arithmetic.div]
  rfl

lemma symmetrize_steps {n : ℕ} (M : Mat n) : (symmetrize M).steps = 3*n^2+n := by
  simp [symmetrize, collect_steps, Arithmetic.add, Arithmetic.div]
  ring

def firstNonzero : {n : ℕ} → (Fin n → ℝ) → Arithmetic (Option (Fin n))
  | 0, _ => Arithmetic.pure none
  | _+1, r => do
    let z ← Arithmetic.eq (r 0) 0
    if z then
      let t ← firstNonzero (fun i => r i.succ)
      Arithmetic.pure (t.map Fin.succ)
    else Arithmetic.pure (some 0)

@[simp] lemma firstNonzero_value {n : ℕ} (r : Fin n → ℝ) :
    (firstNonzero r).value = MatrixElimination.firstNonzero r := by
  induction n with
  | zero => rfl
  | succ n ih => simp [firstNonzero, Arithmetic.eq, ih, MatrixElimination.firstNonzero]

lemma firstNonzero_steps {n : ℕ} (r : Fin n → ℝ) : (firstNonzero r).steps ≤ n := by
  induction n with
  | zero => simp [firstNonzero]
  | succ n ih =>
    simp only [firstNonzero, monad_bind_steps, Arithmetic.eq]
    split <;> simp only [monad_bind_steps, pure_steps, Nat.add_zero]
    · have h := ih (fun i => r i.succ); omega
    · omega

def psdWitness : {n : ℕ} → Mat n → Arithmetic (Option (Fin n → ℝ))
  | 0, _ => Arithmetic.pure none
  | _+1, M => do
    let negative ← Arithmetic.lt (M 0 0) 0
    if negative then Arithmetic.pure (some (prepend 1 0)) else
      let zero ← Arithmetic.eq (M 0 0) 0
      if zero then
        let j ← firstNonzero (row M)
        match j with
        | some j => do
          let a ← Arithmetic.add (tail M j j) 1
          let a ← Arithmetic.neg a
          let b ← Arithmetic.mul 2 (row M j)
          let t ← Arithmetic.div a b
          Arithmetic.pure (some (prepend t (Pi.single j 1)))
        | none => do
          let v ← psdWitness (tail M)
          Arithmetic.pure (v.map (prepend 0))
      else do
        let S ← schur M
        let v ← psdWitness S
        match v with
        | none => Arithmetic.pure none
        | some v => do
          let b ← dot (row M) v
          let b ← Arithmetic.neg b
          let t ← Arithmetic.div b (M 0 0)
          Arithmetic.pure (some (prepend t v))

@[simp] lemma psdWitness_value {n : ℕ} (M : Mat n) :
    (psdWitness M).value = MatrixElimination.psdWitness M := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [psdWitness, monad_bind_value, Arithmetic.lt, Arithmetic.eq, decide_eq_true_eq, ite_value, schur_value,
      firstNonzero_value, ih, MatrixElimination.psdWitness]
    split_ifs <;> try simp only [pure_value]
    · cases MatrixElimination.firstNonzero (row M) <;> simp [Arithmetic.add, Arithmetic.neg, Arithmetic.mul, Arithmetic.div, ih]
    · cases MatrixElimination.psdWitness (MatrixElimination.schur M) <;> simp [Arithmetic.neg, Arithmetic.div]

lemma psdWitness_steps {n : ℕ} (M : Mat n) : (psdWitness M).steps ≤ 50*(n+1)^3 := by
  induction n with
  | zero => simp [psdWitness]
  | succ n ih =>
    have htail := ih (tail M)
    have hschur := ih (MatrixElimination.schur M)
    have hscan := firstNonzero_steps (row M)
    simp only [psdWitness, monad_bind_steps, Arithmetic.lt, Arithmetic.eq, decide_eq_true_eq, ite_steps,
      schur_value, schur_steps, firstNonzero_value, psdWitness_value]
    split_ifs with hneg hzero
    · simp only [pure_steps]; nlinarith
    · cases MatrixElimination.firstNonzero (row M) <;>
        simp only [monad_bind_steps, pure_steps, Arithmetic.add, Arithmetic.neg, Arithmetic.mul, Arithmetic.div] <;>
        nlinarith
    · cases MatrixElimination.psdWitness (MatrixElimination.schur M) <;>
        simp only [monad_bind_steps, pure_steps, dot_steps, Arithmetic.neg, Arithmetic.div] <;>
        nlinarith

def totalPSD {n : ℕ} (M : Mat n) : Arithmetic (Option (Fin n → ℝ)) := do
  let S ← symmetrize M
  psdWitness S

@[simp] lemma totalPSD_value {n : ℕ} (M : Mat n) :
    (totalPSD M).value = MatrixElimination.totalPSD M := by simp [totalPSD, MatrixElimination.totalPSD]

lemma totalPSD_steps {n : ℕ} (M : Mat n) : (totalPSD M).steps ≤ linearAlgebraPrimitiveCost n := by
  have h := psdWitness_steps (MatrixElimination.symmetrize M)
  simp only [totalPSD, monad_bind_steps, symmetrize_value, symmetrize_steps, linearAlgebraPrimitiveCost]
  nlinarith

end Counted
end DPCut.MatrixElimination
