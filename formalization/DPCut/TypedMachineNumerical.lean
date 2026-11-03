import DPCut.TypedMachineMeasurable
import DPCut.RealMachineSolverInputs
import DPCut.RealMachineFactorInputs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory

namespace DPCut.TypedMachine

abbrev weightType (n : ℕ) : ValueType := .array (Fintype.card (Edge n)) .real
abbrev matrixType (n : ℕ) : ValueType := .array n (.array n .real)

def encodeWeights {n : ℕ} (D : Weights n) : (weightType n).Value :=
  fun i => D ((Fintype.equivFin (Edge n)).symm i)

def decodeWeights {n : ℕ} (D : (weightType n).Value) : Weights n :=
  fun e => D (Fintype.equivFin (Edge n) e)

@[simp] theorem decode_encodeWeights {n : ℕ} (D : Weights n) : decodeWeights (encodeWeights D) = D := by
  funext e
  simp [decodeWeights, encodeWeights]

@[simp] theorem encode_decodeWeights {n : ℕ} (D : (weightType n).Value) : encodeWeights (decodeWeights D) = D := by
  funext i
  simp [decodeWeights, encodeWeights]

@[fun_prop] theorem measurable_encodeWeights (n : ℕ) : Measurable (encodeWeights (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

@[fun_prop] theorem measurable_decodeWeights (n : ℕ) : Measurable (decodeWeights (n := n)) := by
  apply measurable_pi_lambda
  intro e
  exact measurable_pi_apply _

/-- Public numerical parameters, not a solver contract. Both the result and
the operation count below are obtained by interpreting fixed register code. -/
structure SolverData (n : ℕ) where
  dimension : 2 ≤ n
  lambda : ℝ
  bound : ℝ
  accuracy : ℝ
  lambda_nonneg : 0 ≤ lambda
  bound_nonneg : 0 ≤ bound
  accuracy_pos : 0 < accuracy
  accuracy_half : accuracy ≤ 1/2

def SolverData.code {n : ℕ} (S : SolverData n) : RealMachine.Code :=
  RealMachine.EllipsoidCode.program S.dimension S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg

def SolverData.input {n : ℕ} (S : SolverData n) (D : Weights n) : RealMachine.State :=
  RealMachine.EllipsoidCode.solverInput n 0 S.lambda S.bound S.accuracy D

def SolverData.result {n : ℕ} (S : SolverData n) (D : Weights n) : Mat n :=
  RealMachine.EllipsoidCode.outputMatrix n 0 (S.code.execute RealMachine.Tapes.zero (S.input D))

def SolverData.operations {n : ℕ} (S : SolverData n) (D : Weights n) : ℕ :=
  (S.code.execute RealMachine.Tapes.zero (S.input D)).operations

def SolverData.operationBound {n : ℕ} (S : SolverData n) : ℕ :=
  RealMachine.EllipsoidCode.solverBound n
    (RealMachine.EllipsoidCode.iterations S.dimension S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg)
    (EllipsoidOptimization.rounds (SDPFlat.problem S.dimension S.lambda_nonneg S.bound_nonneg) S.accuracy)

theorem SolverData.result_accurate {n : ℕ} (S : SolverData n) (D : Weights n) :
    S.result D ∈ feasible n ∧
      optimum S.lambda (boundedObjective S.bound D) -
        objective S.lambda (boundedObjective S.bound D) (S.result D) ≤ S.accuracy :=
  RealMachine.EllipsoidCode.covariance_accurate S.dimension S.lambda S.bound S.accuracy
    S.lambda_nonneg S.bound_nonneg S.accuracy_pos S.accuracy_half D

theorem SolverData.operations_le {n : ℕ} (S : SolverData n) (D : Weights n) :
    S.operations D ≤ S.operationBound := by
  simpa only [SolverData.operations, SolverData.code, SolverData.input,
    RealMachine.EllipsoidCode.program, RealMachine.EllipsoidCode.solverInput, Nat.zero_add] using
      RealMachine.EllipsoidCode.solverProgram_steps n 0
        (RealMachine.EllipsoidCode.iterations S.dimension S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg)
        (EllipsoidOptimization.rounds (SDPFlat.problem S.dimension S.lambda_nonneg S.bound_nonneg) S.accuracy)
        RealMachine.Tapes.zero (S.input D)

@[fun_prop] theorem SolverData.measurable_result {n : ℕ} (S : SolverData n) : Measurable S.result :=
  RealMachine.EllipsoidCode.measurable_covariance S.dimension S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg

@[fun_prop] theorem SolverData.measurable_operations {n : ℕ} (S : SolverData n) : Measurable S.operations :=
  RealMachine.measurable_state_operations.comp
    ((RealMachine.Code.measurable_execute S.code RealMachine.Tapes.zero).comp
      (RealMachine.EllipsoidCode.measurable_solverInput n 0 S.lambda S.bound S.accuracy))

theorem SolverData.operationBound_polynomial {n : ℕ} (S : SolverData n) :
    (S.operationBound : ℝ) ≤ RealMachine.EllipsoidCode.runtimeCoefficient *
      sdpLSWScale n S.lambda S.bound S.accuracy ^ 10 := by
  apply (RealMachine.EllipsoidCode.solverBound_polynomial S.dimension S.lambda S.bound S.accuracy
    S.lambda_nonneg S.bound_nonneg S.accuracy_pos S.accuracy_half).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀
      (le_trans zero_le_one (EllipsoidOptimization.scale_bounds _ S.accuracy_pos S.accuracy_half).1)
      (RealMachine.EllipsoidCode.scale_le_lswScale S.dimension S.lambda S.bound S.accuracy S.lambda_nonneg S.bound_nonneg) 10)
    RealMachine.EllipsoidCode.runtimeCoefficient_pos.le

def releaseSolver {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) : SolverData n :=
  ⟨hn,(fullRunConfig n (precisionParameters p)).oracle.lam,
    publicObjectiveBound n (precisionParameters p),solverAccuracy n p,
    by linarith [(approxConfig_bounds hn hp).lam_lower],
    publicObjectiveBound_nonneg hn (precisionParameters_valid hp),
    (solverAccuracy_bounds hn hp).1,(solverAccuracy_bounds hn hp).2⟩

theorem polynomial_releaseSolver :
    PolynomialRuntimeBound (fun n p => ENNReal.ofReal
      (RealMachine.EllipsoidCode.runtimeCoefficient * solverScale n p ^ 10)) :=
  (PolynomialRuntimeBound.constant _ RealMachine.EllipsoidCode.runtimeCoefficient_pos).real_mul
    (polynomial_solverScale.real_pow 10 (fun n hn p hp => solverScale_nonneg hn hp))
    (fun _ _ _ _ => RealMachine.EllipsoidCode.runtimeCoefficient_pos.le)

end DPCut.TypedMachine
