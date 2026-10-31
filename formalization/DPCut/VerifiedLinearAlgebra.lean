import DPCut.SDPArithmeticFallback
import DPCut.VerifiedGaussianSampling

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

end DPCut
