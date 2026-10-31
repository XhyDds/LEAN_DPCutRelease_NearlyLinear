import DPCut.SDPArithmeticData

/-! The LSW separation/first-order oracle implemented by counted scalar
operations and verified elimination, with the existing public oracle charge. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace DPCut.SDPCoordinates.Counted
open Arithmetic
attribute [local instance] Classical.propDecidable

def insideAnswer {n : ℕ} (lam B : ℝ) (D : Weights n) (X : Mat n) :
    Arithmetic (LSW.Reply (Fin n × Fin n)) := do
  let E ← boundedObjective B D
  let A ← objectiveMatrix E
  let I ← MatrixElimination.Counted.inverse X
  let G ← gradient lam A I
  let g ← normal G
  let d ← MatrixElimination.Counted.determinant X
  let l ← Arithmetic.log d
  let p ← matrixPairing A X
  let r ← Arithmetic.mul lam l
  let f ← Arithmetic.add p r
  Arithmetic.pure (.inr (f,g))

lemma insideAnswer_value {n : ℕ} (hn : 2 ≤ n) (lam B : ℝ) (D : Weights n)
    (X : Mat n) (hX : X ∈ feasible n) :
    (insideAnswer lam B D X).value = .inr
      (objective lam (DPCut.boundedObjective B D) X,
        SDPCoordinates.normal n (DPCut.objectiveMatrix (DPCut.boundedObjective B D) + lam • X⁻¹)) := by
  simp only [insideAnswer, monad_bind_value, pure_value, boundedObjective_value,
    objectiveMatrix_value, MatrixElimination.Counted.inverse_value,
    MatrixElimination.inverse_eq X (feasible_posDef hn hX), gradient_value, normal_value,
    MatrixElimination.Counted.determinant_value,
    MatrixElimination.determinant_correct X (feasible_posDef hn hX),
    Arithmetic.log, matrixPairing_value, Arithmetic.mul, Arithmetic.add]
  rw [matrixPairing_objectiveMatrix _ hX]
  rfl

lemma insideAnswer_steps {n : ℕ} (lam B : ℝ) (D : Weights n) (X : Mat n) :
    (insideAnswer lam B D X).steps ≤ 100*(n+1)^4 := by
  have hB := boundedObjective_steps B D
  have hN := normal_steps ((gradient lam ((objectiveMatrix (DPCut.boundedObjective B D)).value)
    ((MatrixElimination.Counted.inverse X).value)).value)
  have hI := MatrixElimination.Counted.inverse_steps X
  have hDet := MatrixElimination.Counted.determinant_steps X
  have hm : Fintype.card (Edge n) ≤ n^2 := by have := twice_card_edge_le_square n; omega
  have hmn := Nat.mul_le_mul_left (n*n*3) hm
  simp only [insideAnswer, monad_bind_steps, boundedObjective_value,
    objectiveMatrix_steps, gradient_steps, matrixPairing_steps, Arithmetic.log,
    Arithmetic.mul, Arithmetic.add, pure_steps]
  ring_nf at hmn ⊢
  nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^4)]

def negativeAnswer {n : ℕ} (v : Fin n → ℝ) : Arithmetic (LSW.Reply (Fin n × Fin n)) := do
  let A ← negativeOuter v
  let g ← normal A
  Arithmetic.pure (.inl g)

lemma negativeAnswer_value {n : ℕ} (v : Fin n → ℝ) :
    (negativeAnswer v).value = .inl (SDPCoordinates.normal n (-(Matrix.vecMulVec v v))) := by
  simp [negativeAnswer, negativeOuter_value, normal_value]

lemma negativeAnswer_steps {n : ℕ} (v : Fin n → ℝ) : (negativeAnswer v).steps ≤ 6*n^2+2*n := by
  have h := normal_steps ((negativeOuter v).value)
  simp only [negativeAnswer, monad_bind_steps, pure_steps, negativeOuter_steps]
  omega

def dispatch {n : ℕ} (lam B : ℝ) (D : Weights n) (X : Mat n)
    (o : Option (Fin n → ℝ)) : Arithmetic (LSW.Reply (Fin n × Fin n)) :=
  o.elim (insideAnswer lam B D X) negativeAnswer

lemma dispatch_value {n : ℕ} (hn : 2 ≤ n) (lam B : ℝ) (D : Weights n) (X : Mat n)
    (o : Option (Fin n → ℝ)) (hX : o = none → X ∈ feasible n) :
    (dispatch lam B D X o).value = o.elim
      (.inr (objective lam (DPCut.boundedObjective B D) X,
        SDPCoordinates.normal n (DPCut.objectiveMatrix (DPCut.boundedObjective B D) + lam • X⁻¹)))
      (fun v => .inl (SDPCoordinates.normal n (-(Matrix.vecMulVec v v)))) := by
  cases o with
  | none => exact insideAnswer_value hn lam B D X (hX rfl)
  | some v => exact negativeAnswer_value v

lemma dispatch_steps {n : ℕ} (lam B : ℝ) (D : Weights n) (X : Mat n)
    (o : Option (Fin n → ℝ)) : (dispatch lam B D X o).steps ≤ 100*(n+1)^4 := by
  cases o with
  | none => exact insideAnswer_steps lam B D X
  | some v =>
    have h := negativeAnswer_steps v
    change (negativeAnswer v).steps ≤ _
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^4)]

def bodyAnswer {n : ℕ} (lam B : ℝ) (D : Weights n) (x : Space n) :
    Arithmetic (LSW.Reply (Fin n × Fin n)) := do
  let X ← lift x
  let S ← slack X
  let o ← MatrixElimination.Counted.totalPSD S
  dispatch lam B D X o

lemma bodyAnswer_value {n : ℕ} (hn : 2 ≤ n) (lam B : ℝ) (D : Weights n) (x : Space n) :
    (bodyAnswer lam B D x).value = (MatrixElimination.totalPSD (SDPCoordinates.slack x)).elim
      (.inr (objective lam (DPCut.boundedObjective B D) (SDPCoordinates.lift x),
        SDPCoordinates.normal n (DPCut.objectiveMatrix (DPCut.boundedObjective B D) + lam • (SDPCoordinates.lift x)⁻¹)))
      (fun v => .inl (SDPCoordinates.normal n (-(Matrix.vecMulVec v v)))) := by
  have he := Arithmetic.bind3_value (lift x) slack MatrixElimination.Counted.totalPSD
    (dispatch lam B D) (SDPCoordinates.lift x) (SDPCoordinates.slack x)
    (MatrixElimination.totalPSD (SDPCoordinates.slack x)) (lift_value x)
    (slack_value (SDPCoordinates.lift x)) (MatrixElimination.Counted.totalPSD_value _)
  refine he.trans (dispatch_value hn lam B D (SDPCoordinates.lift x)
    (MatrixElimination.totalPSD (SDPCoordinates.slack x)) ?_)
  intro h
  exact (slack_posSemidef_iff x).mp
    ((MatrixElimination.totalPSD_none _ (slack_hermitian x)).mp h)

lemma bodyAnswer_steps {n : ℕ} (lam B : ℝ) (D : Weights n) (x : Space n) :
    (bodyAnswer lam B D x).steps ≤ 100*(n+1)^4 + linearAlgebraPrimitiveCost n + 5*n^2+2*n+1 := by
  have hL := lift_steps x
  have hP := MatrixElimination.Counted.totalPSD_steps ((slack ((lift x).value)).value)
  have hD := dispatch_steps lam B D ((lift x).value)
    ((MatrixElimination.Counted.totalPSD ((slack ((lift x).value)).value)).value)
  simp only [bodyAnswer, monad_bind_steps, slack_steps]
  omega

def answer {n : ℕ} (lam B : ℝ) (q : Weights n × Space n) :
    Arithmetic (LSW.Reply (Fin n × Fin n)) := do
  let r ← norm q.2
  let R ← Arithmetic.mul 2 n
  let outside ← Arithmetic.lt R r
  if outside then Arithmetic.pure (.inl q.2) else bodyAnswer lam B q.1 q.2

lemma answer_value {n : ℕ} (hn : 2 ≤ n) (lam B : ℝ) (q : Weights n × Space n) :
    (answer lam B q).value = SDPCoordinates.answer MatrixElimination.primitives lam B q := by
  simp only [answer, monad_bind_value, norm_value, Arithmetic.mul, Arithmetic.lt,
    ite_value, decide_eq_true_eq, pure_value, bodyAnswer_value hn,
    SDPCoordinates.answer, MatrixElimination.primitives]

lemma answer_steps {n : ℕ} (lam B : ℝ) (q : Weights n × Space n) :
    (answer lam B q).steps ≤ oracleCharge n := by
  have hB := bodyAnswer_steps lam B q.1 q.2
  simp only [answer, monad_bind_steps, norm_steps,
    Arithmetic.mul, Arithmetic.lt, ite_steps]
  split
  · simp only [pure_steps, oracleCharge, linearAlgebraPrimitiveCost]
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^4), Nat.zero_le (n^5), Nat.zero_le (n^6)]
  · simp only [oracleCharge, linearAlgebraPrimitiveCost] at hB ⊢
    nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^4), Nat.zero_le (n^5), Nat.zero_le (n^6)]

end DPCut.SDPCoordinates.Counted
