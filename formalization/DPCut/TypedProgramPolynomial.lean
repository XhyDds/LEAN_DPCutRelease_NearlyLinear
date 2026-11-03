import DPCut.TypedPolynomial

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
noncomputable section

namespace DPCut.TypedMachine

open Lean Meta Elab Tactic in
elab "instruction_poly_step" : tactic => withMainContext do
  let target ← getMainTarget
  let function := target.getAppArgs.back!
  let (literal, head) ← lambdaTelescope function fun _ body => do
    let literal := match body with
      | .lit (.natVal _) => true
      | _ => body.isAppOf ``OfNat.ofNat
    pure (literal, body.getAppFn.constName?)
  if literal then
    evalTactic (← `(tactic| exact PolynomialInstructions.constant _))
  else
    match head with
    | some ``HAdd.hAdd | some ``Nat.add =>
        evalTactic (← `(tactic| apply PolynomialInstructions.add))
    | some ``HMul.hMul | some ``Nat.mul =>
        evalTactic (← `(tactic| apply PolynomialInstructions.mul))
    | some ``HPow.hPow | some ``Nat.pow =>
        evalTactic (← `(tactic| apply PolynomialInstructions.pow))
    | some ``Max.max | some ``Nat.max =>
        evalTactic (← `(tactic| apply PolynomialInstructions.max))
    | some ``SolverData.operationBound =>
        evalTactic (← `(tactic| exact polynomial_instruction_solver))
    | some ``BoundedCommand.operations =>
        evalTactic (← `(tactic| apply PolynomialInstructions.scalarArray))
    | some ``RunConfig.T1 =>
        evalTactic (← `(tactic| exact polynomial_instruction_T1))
    | some ``RunConfig.T2 =>
        evalTactic (← `(tactic| exact polynomial_instruction_T2))
    | some ``OracleConfig.K =>
        evalTactic (← `(tactic| exact polynomial_instruction_trials))
    | some ``OracleConfig.k =>
        evalTactic (← `(tactic| exact polynomial_instruction_batch))
    | some ``Fintype.card =>
        evalTactic (← `(tactic| exact polynomial_instruction_edges))
    | none =>
        evalTactic (← `(tactic| exact polynomial_instruction_vertices))
    | _ => throwError "Unrecognized instruction-budget head: {head}"

open Lean Meta Elab Tactic in
private partial def solveInstructionPolynomial (cache : IO.Ref (Std.HashMap Expr Expr)) (goal : MVarId) :
    TacticM Unit := do
  let target ← instantiateMVars (← goal.getType)
  if let some proof := (← cache.get)[target]? then
    goal.assign proof
  else
    setGoals [goal]
    evalTactic (← `(tactic| instruction_poly_step))
    for next in ← getGoals do
      solveInstructionPolynomial cache next
    let proof ← instantiateMVars (mkMVar goal)
    cache.modify fun proofs => proofs.insert target proof

open Lean Meta Elab Tactic in
elab "instruction_poly" : tactic => do
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  for goal in ← getGoals do
    solveInstructionPolynomial cache goal
  setGoals []

theorem calibration_operations_constant (n : ℕ) :
    (calibrationCommand n).operations = (calibrationCommand 0).operations := by
  simp only [calibrationCommand,BoundedCommand.pure,publicTerm,scheduleFuel,scheduleRounds,
    publicExpressions,accuracyExpr,runExpressions,oracleExpressions,noiseShiftExpr,clipThresholdExpr,
    logFactorExpr,ParameterTerms.precision,ParameterTerms.bounded,parameterTerms,
    Term.pow,Term.operations,Local.operations,RealBinary.operations,RealUnary.operations,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]

theorem polynomial_instruction_calibration :
    PolynomialInstructions (fun n _ _ _ => (calibrationCommand n).operations) := by
  simpa only [calibration_operations_constant] using
    PolynomialInstructions.constant (calibrationCommand 0).operations

theorem releaseProgram_operations_polynomial :
    PolynomialInstructions (fun n hn p hp => (releaseProgram hn p hp).operations) := by
  simp only [releaseProgram,fullCommand,preprocessCommand,outerCommand,outerStep,outerAfterNoise,
    outerAfterMass,outerAfterInner,innerCommand,innerStep,aggregateCommand,aggregateStep,aggregateAfterPlus,
    aggregateFinish,witnessCommand,trialsCommand,trialStep,trialSampleCommand,gaussianCommand,
    BoundedCommand.bind,BoundedCommand.branch,BoundedCommand.pure,BoundedCommand.iterate,
    BoundedCommand.laplace,BoundedCommand.factor,BoundedCommand.solver,
    runTermsOf,RunTerms.weaken,OracleTerms.weaken,realPublic,dataInput,
    positiveTerm,noisyExcessTerm,clipWeightsTerm,initialEstimateTerm,productWeights,
    residualUpdateTerm,addWeights,subWeights,initialAggregate,
    noisyMassTerm,innerNextTerm,mwUpdateTerm,acceptsTerm,
    plusDiscrepancyTerm,minusDiscrepancyTerm,aggregateAddTerm,
    plusTerm,minusTerm,residualTerm,boundedObjectiveTerm,
    noWitness,allZero,l1Term,acceptTrialTerm,normalizeTerm,activeMaximumTerm,
    clippedWitnessTerm,rawWitnessTerm,batchTransformTerm,pairingTerm,massTerm,
    zeroWeights,oneWeights,weightTerms,edgeTerm,newest,Term.at,
    Term.weaken,Term.operations,Local.operations,RealBinary.operations,RealUnary.operations,
    Bool.true_eq,Bool.false_eq_true,ite_true,ite_false,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  instruction_poly

theorem implemented_operations_polynomial :
    PolynomialInstructions (fun n hn p hp => (calibrationCommand n).operations+(releaseProgram hn p hp).operations) :=
  polynomial_instruction_calibration.add releaseProgram_operations_polynomial

theorem implemented_calls_polynomial :
    PolynomialInstructions (fun n hn p hp => (releaseProgram hn p hp).solverCalls) := by
  simp only [releaseProgram,fullCommand_calls]
  exact polynomial_instruction_T1.mul
    (polynomial_instruction_T2.mul (polynomial_instruction_edges.mul (PolynomialInstructions.constant 2)))

end DPCut.TypedMachine
