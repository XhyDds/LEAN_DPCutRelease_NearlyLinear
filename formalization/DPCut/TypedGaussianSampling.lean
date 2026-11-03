import DPCut.TypedScalarSampling
import DPCut.TypedMachineErasure
import DPCut.MatrixGaussianAlgorithm
import DPCut.WitnessQuadratic

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

def gaussianCommand {Γ : List ValueType} (n k : ℕ) (X : Term Γ (matrixType n)) :
    BoundedCommand Γ (batchType n k) :=
  (BoundedCommand.factor n X).bind
    ((scalarArray true (k*n) (matrixType n :: Γ)).bind
      (.pure (batchTransformTerm n k (.read (.tail .head)) newest)))

theorem flatGaussian_curry (n k : ℕ) :
    (Measure.pi (fun _ : Fin (k*n) => gaussianReal 0 1)).map
      (fun z j i => z (finProdFinEquiv (j,i))) =
        Measure.pi (fun _ : Fin k => standardGaussian n) := by
  have hflat : (Measure.pi (fun _ : Fin (k*n) => gaussianReal 0 1)).map
      (fun (z : Fin (k*n) → ℝ) (ij : Fin k × Fin n) => z (finProdFinEquiv ij)) =
        Measure.pi (fun _ : Fin k × Fin n => gaussianReal 0 1) := by
    convert (measurePreserving_piCongrLeft (fun _ : Fin k × Fin n => gaussianReal 0 1)
      finProdFinEquiv.symm).map_eq using 1
    congr 1
    funext z ij
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k × Fin n => ℝ)
      finProdFinEquiv.symm z (finProdFinEquiv ij)).symm
  have hcurr := congrArg (fun μ : Measure (Fin k × Fin n → ℝ) =>
    μ.map (fun z j i => z (j,i))) hflat
  dsimp only at hcurr
  have hC : (Measure.pi (fun _ : Fin k × Fin n => gaussianReal 0 1)).map
      (fun z j i => z (j,i)) = Measure.pi (fun _ : Fin k => standardGaussian n) :=
    (gaussianProduct_curry n k).map_eq
  rw [Measure.map_map (by fun_prop) (by fun_prop), hC] at hcurr
  exact hcurr

theorem gaussianCommand_law {Γ : List ValueType} (n k : ℕ) (X : Term Γ (matrixType n))
    (s : Environment Γ) (hX : Matrix.PosDef (X.eval s)) :
    (gaussianCommand n k X).code.law s = gaussianBatch (X.eval s) k := by
  change (Command.bind (Command.factor n X)
    (Command.bind (scalarArray true (k*n) (matrixType n :: Γ)).code
      (Command.pure (batchTransformTerm n k (.read (.tail .head)) newest)))).law s = _
  rw [Command.law_bind, Command.law_factor]
  have hc : Measurable (fun L : (matrixType n).Value =>
      (Command.bind (scalarArray true (k*n) (matrixType n :: Γ)).code
        (Command.pure (batchTransformTerm n k (.read (.tail .head)) newest))).law (L,s)) :=
    (Command.measurable_law _).comp (measurable_id.prodMk measurable_const)
  rw [Measure.dirac_bind hc, Command.law_bind, scalarArray_law]
  simp only [Command.law_pure, eval_batchTransformTerm, newest, Term.eval, Local.read, scalarLaw]
  have ht : Measurable (fun z : Fin (k*n) → ℝ => fun j =>
      Matrix.mulVec (MatrixElimination.factor (X.eval s)) (fun l => z (finProdFinEquiv (j,l)))) := by
    fun_prop
  rw [Measure.bind_dirac_eq_map _ ht]
  have hcurr := congrArg (fun μ : Measure (Fin k → Fin n → ℝ) =>
    μ.map (fun z j => Matrix.mulVec (MatrixElimination.factor (X.eval s)) (z j))) (flatGaussian_curry n k)
  dsimp only at hcurr
  rw [Measure.map_map (by fun_prop) (by fun_prop), MatrixElimination.factor_gaussianBatch_law _ hX k] at hcurr
  exact hcurr

theorem gaussianCommand_calls {Γ : List ValueType} (n k : ℕ) (X : Term Γ (matrixType n)) :
    (gaussianCommand n k X).solverCalls = 0 := by
  simp only [gaussianCommand, BoundedCommand.bind, BoundedCommand.factor, BoundedCommand.pure,
    scalarArray_calls, Nat.zero_add]

end DPCut.TypedMachine
