import DPCut.SDPArithmeticFallback
import DPCut.VerifiedGaussianSampling
import DPCut.CostedArithmetic

/-! A constructed implementation certificate for every linear-algebra block
used by the LSW-based release. This is data with proved fields, not an external
contract or an additional hypothesis of Theorem 1. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace DPCut

structure LinearAlgebraImplementation where
  primitives : LinearAlgebraPrimitives
  psdProgram : ∀ n, Mat n → Arithmetic (Option (Fin n → ℝ))
  psd_value : ∀ n M, (psdProgram n M).value = primitives.psdWitness n M
  psd_cost : ∀ n M, (psdProgram n M).steps ≤ linearAlgebraPrimitiveCost n
  oracleProgram : ∀ n, ℝ → ℝ → Weights n × SDPCoordinates.Space n →
    Arithmetic (LSW.Reply (Fin n × Fin n))
  oracle_value : ∀ n, 2 ≤ n → ∀ lam B q,
    (oracleProgram n lam B q).value = SDPCoordinates.answer primitives lam B q
  oracle_cost : ∀ n lam B q, (oracleProgram n lam B q).steps ≤ SDPCoordinates.oracleCharge n
  decodeProgram : ∀ n, Option (SDPCoordinates.Space n) → Arithmetic (Mat n)
  decode_value : ∀ n (hn : 2 ≤ n) o,
    (decodeProgram n o).value = (SDPCoordinates.decode hn o).val
  decode_cost : ∀ n o, (decodeProgram n o).steps ≤ SDPCoordinates.oracleCharge n
  gaussianProgram : ∀ n, Mat n → (k : ℕ) → CostedLaw (Fin k → Fin n → ℝ)
  gaussian_law : ∀ n X, X.PosDef → ∀ k, (gaussianProgram n X k).law = gaussianBatch X k
  gaussian_cost : ∀ n X k, (gaussianProgram n X k).cost ≤ gaussianBatchCost n k

/-- Every field is discharged by the scalar algorithms and their verified
operation counts. In particular, no external matrix routine is supplied. -/
def verifiedLinearAlgebra : LinearAlgebraImplementation where
  primitives := MatrixElimination.primitives
  psdProgram _ := MatrixElimination.Counted.totalPSD
  psd_value _ := MatrixElimination.Counted.totalPSD_value
  psd_cost _ := MatrixElimination.Counted.totalPSD_steps
  oracleProgram _ := SDPCoordinates.Counted.answer
  oracle_value _ := SDPCoordinates.Counted.answer_value
  oracle_cost _ := SDPCoordinates.Counted.answer_steps
  decodeProgram _ := SDPCoordinates.Counted.decode
  decode_value _ := SDPCoordinates.Counted.decode_value
  decode_cost _ := SDPCoordinates.Counted.decode_steps
  gaussianProgram _ := verifiedGaussianBatch
  gaussian_law _ := verifiedGaussianBatch_law
  gaussian_cost _ := verifiedGaussianBatch_cost

namespace SDPCoordinates

/-- The LSW oracle executes the supplied counted implementation. Its public
charge is accepted only with the implementation's proved operation bound. -/
def oracle {n : ℕ} (hn : 2 ≤ n) {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (I : LinearAlgebraImplementation) : LSW.Oracle (problem hn hlam hB) where
  answer := I.oracleProgram n lam B
  measurable_answer := by
    simp_rw [I.oracle_value n hn]
    exact measurable_answer I.primitives lam B
  correct := by
    intro D x
    rw [I.oracle_value n hn]
    exact answer_correct hn hlam hB I.primitives D x
  charge := oracleCharge n
  cost_le := I.oracle_cost n lam B

/-- Execute the counted decoder, using semantic agreement only to certify
feasibility of its output. -/
def decodeArithmetic (I : LinearAlgebraImplementation) {n : ℕ} (hn : 2 ≤ n)
    (o : Option (Space n)) : Arithmetic (FeasibleMatrix n) :=
  ⟨⟨(I.decodeProgram n o).value, by
      rw [I.decode_value n hn]
      exact (decode hn o).property⟩, (I.decodeProgram n o).steps⟩

lemma decodeArithmetic_value (I : LinearAlgebraImplementation) {n : ℕ} (hn : 2 ≤ n)
    (o : Option (Space n)) : (decodeArithmetic I hn o).value = decode hn o :=
  Subtype.ext (I.decode_value n hn o)

lemma decodeArithmetic_cost (I : LinearAlgebraImplementation) {n : ℕ} (hn : 2 ≤ n)
    (o : Option (Space n)) : (decodeArithmetic I hn o).steps ≤ oracleCharge n :=
  I.decode_cost n o

end SDPCoordinates

end DPCut
