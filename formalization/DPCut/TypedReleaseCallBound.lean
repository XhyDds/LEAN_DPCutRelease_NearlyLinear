import DPCut.TypedReleaseProgram

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section

namespace DPCut.TypedMachine

@[simp] theorem trialSampleCommand_calls {Γ : List ValueType} (n k : ℕ) (epsilon : Term Γ .real)
    (D : Term Γ (weightType n)) (X : Term Γ (matrixType n)) :
    (trialSampleCommand n k epsilon D X).solverCalls = 0 := by
  simp [trialSampleCommand,BoundedCommand.bind,BoundedCommand.laplace,BoundedCommand.pure,gaussianCommand_calls]

@[simp] theorem trialsCommand_calls {Γ : List ValueType} (n k K : ℕ) (epsilon tau : Term Γ .real)
    (D r : Term Γ (weightType n)) (X : Term Γ (matrixType n)) :
    (trialsCommand n k K epsilon tau D r X).solverCalls = 0 := by
  simp [trialsCommand,trialStep,BoundedCommand.iterate,BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.pure,
    trialSampleCommand_calls]

@[simp] theorem witnessCommand_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (epsilon tau B : Term Γ .real) (D r : Term Γ (weightType n)) :
    (witnessCommand S k K epsilon tau B D r).solverCalls = 1 := by
  simp [witnessCommand,BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.solver,BoundedCommand.pure,trialsCommand_calls]

@[simp] theorem aggregateStep_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n)) :
    (aggregateStep S k K o gamma w h).solverCalls = 2 := by
  simp [aggregateStep,aggregateAfterPlus,aggregateFinish,
    BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.pure,witnessCommand_calls]

@[simp] theorem aggregateCommand_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n)) :
    (aggregateCommand S k K o gamma w h).solverCalls = Fintype.card (Edge n)*2 := by
  simp [aggregateCommand,BoundedCommand.iterate,BoundedCommand.bind,BoundedCommand.pure,aggregateStep_calls]

@[simp] theorem innerStep_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (o : OracleTerms Γ) (gamma eta M : Term Γ .real) (w : Term Γ (weightType n)) :
    (innerStep S k K o gamma eta M w).solverCalls = Fintype.card (Edge n)*2 := by
  simp [innerStep,BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.pure,aggregateCommand_calls]

@[simp] theorem innerCommand_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T : ℕ)
    (o : OracleTerms Γ) (gamma eta M : Term Γ .real) (w initial : Term Γ (weightType n)) :
    (innerCommand S k K T o gamma eta M w initial).solverCalls = T*(Fintype.card (Edge n)*2) := by
  simp [innerCommand,BoundedCommand.iterate,BoundedCommand.bind,BoundedCommand.pure,innerStep_calls]

@[simp] theorem outerStep_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T2 : ℕ)
    (p : RunTerms Γ) (w : Term Γ (weightType n)) :
    (outerStep S k K T2 p w).solverCalls = T2*(Fintype.card (Edge n)*2) := by
  simp [outerStep,outerAfterNoise,outerAfterMass,outerAfterInner,BoundedCommand.branch,BoundedCommand.bind,
    BoundedCommand.pure,BoundedCommand.laplace,innerCommand_calls]

@[simp] theorem outerCommand_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T1 T2 : ℕ)
    (p : RunTerms Γ) (w : Term Γ (weightType n)) :
    (outerCommand S k K T1 T2 p w).solverCalls = T1*(T2*(Fintype.card (Edge n)*2)) := by
  simp [outerCommand,BoundedCommand.iterate,BoundedCommand.bind,BoundedCommand.pure,outerStep_calls]

@[simp] theorem preprocessCommand_calls {Γ : List ValueType} (n : ℕ) (U V epsilon : Term Γ .real)
    (w : Term Γ (weightType n)) : (preprocessCommand n U V epsilon w).solverCalls = 0 := by
  simp [preprocessCommand,BoundedCommand.bind,BoundedCommand.pure,scalarArray_calls]

theorem fullCommand_calls {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T1 T2 : ℕ)
    (p : RunTerms Γ) (U V epsilon : Term Γ .real) (w : Term Γ (weightType n)) :
    (fullCommand S k K T1 T2 p U V epsilon w).solverCalls = T1*(T2*(Fintype.card (Edge n)*2)) := by
  simp [fullCommand,BoundedCommand.bind,BoundedCommand.pure,preprocessCommand_calls,outerCommand_calls]

end DPCut.TypedMachine
