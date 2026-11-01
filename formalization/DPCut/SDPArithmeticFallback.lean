import DPCut.SDPArithmeticOracle
import DPCut.SDPDecode

/-! The optimizer's final feasibility check is implemented by the same
scalar PSD algorithm. No semantic set-membership primitive remains. -/
set_option autoImplicit false
noncomputable section
open Matrix
namespace DPCut.SDPCoordinates.Counted
open Arithmetic
attribute [local instance] Classical.propDecidable

def candidate {n : ℕ} (x : Space n) : Arithmetic (Mat n) := do
  let X ← lift x
  let S ← slack X
  let o ← MatrixElimination.Counted.totalPSD S
  Arithmetic.pure (o.elim X (fun _ => 1))

lemma candidate_value {n : ℕ} (x : Space n) :
    (candidate x).value = (MatrixElimination.totalPSD (SDPCoordinates.slack x)).elim
      (SDPCoordinates.lift x) (fun _ => 1) :=
  Arithmetic.bind3_value (lift x) slack MatrixElimination.Counted.totalPSD
    (fun X o => Arithmetic.pure (o.elim X (fun _ => 1)))
    (SDPCoordinates.lift x) (SDPCoordinates.slack x)
    (MatrixElimination.totalPSD (SDPCoordinates.slack x)) (lift_value x)
    (slack_value (SDPCoordinates.lift x)) (MatrixElimination.Counted.totalPSD_value _)

lemma candidate_steps {n : ℕ} (x : Space n) :
    (candidate x).steps ≤ linearAlgebraPrimitiveCost n + 5*n^2+2*n+1 := by
  have hL := lift_steps x
  have hP := MatrixElimination.Counted.totalPSD_steps ((slack ((lift x).value)).value)
  simp only [candidate, monad_bind_steps, pure_steps, slack_steps]
  omega

def safeMatrix {n : ℕ} (x : Space n) : Arithmetic (Mat n) := do
  let r ← norm x
  let R ← Arithmetic.mul 2 n
  let outside ← Arithmetic.lt R r
  if outside then Arithmetic.pure 1 else candidate x

lemma safeMatrix_value {n : ℕ} (hn : 2 ≤ n) (x : Space n) :
    (safeMatrix x).value = (SDPCoordinates.safeMatrix hn x).val := by
  rw [SDPCoordinates.safeMatrix_val_primitive hn MatrixElimination.primitives]
  simp only [safeMatrix, monad_bind_value, norm_value, Arithmetic.mul, Arithmetic.lt,
    ite_value, pure_value, decide_eq_true_eq, candidate_value, MatrixElimination.primitives]
  by_cases h : 2*(n:ℝ)<‖x‖
  · simp [h, not_le_of_gt h]
  · simp only [h, if_false, le_of_not_gt h, true_and]
    cases MatrixElimination.totalPSD (SDPCoordinates.slack x) <;> simp

lemma safeMatrix_steps {n : ℕ} (x : Space n) : (safeMatrix x).steps ≤ oracleCharge n := by
  have h := candidate_steps x
  simp only [safeMatrix, monad_bind_steps, norm_steps, Arithmetic.mul, Arithmetic.lt, ite_steps]
  split <;> simp only [pure_steps, oracleCharge, linearAlgebraPrimitiveCost] at h ⊢ <;>
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^4), Nat.zero_le (n^5), Nat.zero_le (n^6)]

def decode {n : ℕ} (o : Option (Space n)) : Arithmetic (Mat n) :=
  o.elim (Arithmetic.pure 1) safeMatrix

lemma decode_value {n : ℕ} (hn : 2 ≤ n) (o : Option (Space n)) :
    (decode o).value = (SDPCoordinates.decode hn o).val := by
  cases o with
  | none => rfl
  | some x => exact safeMatrix_value hn x

lemma decode_steps {n : ℕ} (o : Option (Space n)) : (decode o).steps ≤ oracleCharge n := by
  cases o with
  | none => exact Nat.zero_le _
  | some x => exact safeMatrix_steps x

end DPCut.SDPCoordinates.Counted
