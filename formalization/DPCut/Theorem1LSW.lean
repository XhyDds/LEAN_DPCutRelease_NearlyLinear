import DPCut.LSWRelease
import DPCut.VerifiedLinearAlgebra

/-! Theorem 1 conditional only on Lee--Sidford--Wong in the real model.
Linear algebra is implemented by verified scalar elimination. The constructed
`verifiedLinearAlgebra` certificate proves the first-order oracle and fallback
operation counts, and refines covariance Gaussian sampling to scalar draws.
The external LSW hypothesis is a proposition argument, not an axiom. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

namespace LSWRelease

def costBound (F : CuttingPlaneFamily) (n : ℕ) (p : Parameters) : ℝ≥0∞ :=
  2 * vectorBlockCost n + OracleReplacement.fullCostBound (witnessCost F n p) n (precisionParameters p)

lemma run_cost (F : CuttingPlaneFamily) {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (w : Weights n) : (run F hn p hp w).cost ≤ costBound F n p := by
  have h := OracleReplacement.costedFullRelease_cost (witness F hn p hp) (witnessCost F n p)
    (witness_cost F hn p hp) (precisionParameters p) w
  calc
    _ ≤ vectorBlockCost n + (OracleReplacement.fullCostBound (witnessCost F n p) n (precisionParameters p) + vectorBlockCost n) :=
      add_le_add_left (add_le_add_right h _) _
    _ = _ := by unfold costBound; ring

lemma costBound_polynomial (F : CuttingPlaneFamily) : PolynomialRuntimeBound (costBound F) := by
  have h1 : PolynomialRuntimeBound (fun _ _ => (1:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 1 (by norm_num)
  have h2 : PolynomialRuntimeBound (fun _ _ => (2:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 2 (by norm_num)
  have h3 : PolynomialRuntimeBound (fun _ _ => (3:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 3 (by norm_num)
  have h100 : PolynomialRuntimeBound (fun _ _ => (100:ℝ≥0∞)) := by simpa using PolynomialRuntimeBound.constant 100 (by norm_num)
  have hB : PolynomialRuntimeBound (fun n _ => vectorBlockCost n) := h100.mul (polynomial_vertices.pow 2)
  obtain ⟨hT1,hT2,_,_⟩ := polynomial_full_parameters
  have hAggregate := polynomial_edges.mul (hB.add (h2.mul (witnessCost_polynomial F)))
  have hInner := hT2.precision.mul (hAggregate.add hB)
  have hOuter := hT1.precision.mul ((h1.add hB).add hInner)
  exact (h2.mul hB).add (((h3.mul hB).add polynomial_edges).add hOuter)

/-- A single program for every size and public parameter choice. -/
inductive Program where
  | fullRelease

def Program.run {n : ℕ} (F : CuttingPlaneFamily) (_ : Program) (p : Parameters) (w : Weights n) :
    CostedLaw (Weights n) :=
  if h : 2 ≤ n ∧ p.Valid then LSWRelease.run F h.1 p h.2 w else .pure 0

lemma Program.run_valid {n : ℕ} (F : CuttingPlaneFamily) (program : Program)
    (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    program.run F p w = LSWRelease.run F hn p hp w := by
  simp only [Program.run, dif_pos (show 2 ≤ n ∧ p.Valid from ⟨hn,hp⟩)]

/-- The cost is the supremum over all intermediate values, including timeout
branches. Gaussian/Laplace sampling, elementary real operations, and the stated
linear-algebra blocks have the explicit prices used in the costed program. -/
def model (F : CuttingPlaneFamily) : ComputationalModel where
  Program := Program
  realizes n program p M := ∀ w : Weights n, M w = (program.run F p w).law
  cost _ program p w := (program.run F p w).cost

lemma main (F : CuttingPlaneFamily) : MainTheoremStatement (model F) := by
  obtain ⟨Ctime,hCtime,d,htime⟩ := costBound_polynomial F
  refine ⟨(2:ℝ)^178,Ctime,d,Program.fullRelease,by positivity,hCtime,?_⟩
  intro n hn p hp
  refine ⟨kernel F hn p hp, ?_, inferInstance, ?_, run_private F hn p hp, ?_⟩
  · intro w
    rw [Program.run_valid F _ hn p hp w]
    rfl
  · intro w _
    exact run_nonnegative F hn p hp w
  · intro w hw
    refine ⟨?_,run_utility F hn p hp w hw⟩
    change (Program.fullRelease.run F p w).cost ≤ _
    rw [Program.run_valid F _ hn p hp w]
    exact (run_cost F hn p hp w).trans (htime n hn p hp)

end LSWRelease

/-- The real model whose optimizer is derived from LSW, rather than assumed
as a deterministic approximate-SDP primitive. -/
def realArithmeticLSWPrimitiveModel (hLSW : LSWStatement) (P : LinearAlgebraPrimitives) : ComputationalModel :=
  LSWRelease.model (cuttingPlaneFamily hLSW P)

/-- The earlier modular theorem, retained for alternative primitive implementations. -/
theorem theorem1_of_lsw_with_primitives (hLSW : LSWStatement) (P : LinearAlgebraPrimitives) :
    MainTheoremStatement (realArithmeticLSWPrimitiveModel hLSW P) :=
  LSWRelease.main (cuttingPlaneFamily hLSW P)

/-- The instantiated real model. Its linear-algebra macro charges are justified
by the constructed scalar-operation implementation certificate. -/
def realArithmeticLSWModel (hLSW : LSWStatement) : ComputationalModel :=
  realArithmeticLSWPrimitiveModel hLSW verifiedLinearAlgebra.primitives

/-- **Theorem 1, with LSW as the only external algorithmic hypothesis.**
A single program has worst-case polynomial cost, nonnegative outputs,
`(epsilon,delta)` edge-DP, and the simultaneous all-cut error bound.
The model retains exact real scalar operations and sampling. No exact SDP
optimizer, PSD separation, matrix inverse, determinant, or covariance-factor
implementation is supplied as an external assumption. -/
theorem theorem1_of_lsw (hLSW : LSWStatement) :
    MainTheoremStatement (realArithmeticLSWModel hLSW) :=
  theorem1_of_lsw_with_primitives hLSW verifiedLinearAlgebra.primitives

end DPCut
