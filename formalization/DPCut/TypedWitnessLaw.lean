import DPCut.TypedStoppedTrials
import DPCut.VerifiedEllipsoidWitness

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem witnessCommand_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (o : OracleConfig)
    (epsilon tau B : Term Γ .real) (D r : Term Γ (weightType n)) (s : Environment Γ)
    (he : epsilon.eval s = o.eps1) (ht : tau.eval s = o.tau1) (hepos : 0 < o.eps1) :
    ((witnessCommand S o.k o.K epsilon tau B D r).code.law s).map decodeWitness =
      approximateFindWitness o (boundedObjective (B.eval s) (decodeWeights (D.eval s)))
        (decodeWeights (r.eval s)) (S.result (decodeWeights (D.eval s))) := by
  change ((Command.branch (allZero r) (Command.pure (noWitness n))
    (Command.bind (Command.solver S D)
      (trialsCommand n o.k o.K epsilon.weaken tau.weaken (boundedObjectiveTerm B D).weaken r.weaken newest).code)).law s).map _ = _
  rw [Command.law_branch,eval_allZero]
  by_cases hr : decodeWeights (r.eval s) = 0
  · simp only [hr,decide_true,ite_true,Command.law_pure,Measure.map_dirac (measurable_decodeWitness n)]
    simp [noWitness,decodeWitness,Term.eval,approximateFindWitness]
  · simp only [hr,decide_false,Bool.false_eq_true,ite_false,Command.law_bind,Command.law_solver]
    let rest := (trialsCommand n o.k o.K epsilon.weaken tau.weaken (boundedObjectiveTerm B D).weaken r.weaken
      (newest : Term (matrixType n :: Γ) (matrixType n))).code
    have hm : Measurable (fun X : (matrixType n).Value => rest.law (X,s)) :=
      rest.measurable_law.comp (measurable_id.prodMk (measurable_const (a := s)))
    change ((Measure.dirac (S.result (decodeWeights (D.eval s)))).bind (fun X => rest.law (X,s))).map _ = _
    have hbind := congrArg (fun μ : Measure (witnessType n).Value => μ.map decodeWitness)
      (Measure.dirac_bind hm (S.result (decodeWeights (D.eval s))))
    trans (rest.law (S.result (decodeWeights (D.eval s)),s)).map decodeWitness
    · exact hbind
    · have hX := feasible_posDef S.dimension (S.result_accurate (decodeWeights (D.eval s))).1
      have htrials := trialsCommand_law n o epsilon.weaken tau.weaken (boundedObjectiveTerm B D).weaken r.weaken
        (newest : Term (matrixType n :: Γ) (matrixType n)) (S.result (decodeWeights (D.eval s)),s)
        (by simpa using he) (by simpa using ht) hepos hX
      simpa only [Term.eval_weaken_env,eval_boundedObjectiveTerm,Term.eval,newest,Local.read,
        approximateFindWitness,hr,ite_false] using htrials

theorem deterministicWitness_run_law {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (he : 0 < o.eps1)
    (S : Weights n → CostedLaw (FeasibleMatrix n)) (f : Weights n → FeasibleMatrix n)
    (hS : ∀ D, (S D).law = Measure.dirac (f D)) (B : ℝ) (D r : Weights n) :
    (RandomizedWitness.run o S B D r).law = approximateFindWitness o (boundedObjective B D) r (f D).val := by
  letI (D : Weights n) : IsProbabilityMeasure (S D).law := by rw [hS]; infer_instance
  rw [RandomizedWitness.run_law hn o he,hS]
  have hm : Measurable (fun X : FeasibleMatrix n =>
      approximateFindWitness o (boundedObjective B D) r X.val) :=
    (RandomizedWitness.measurable_witness hn o he).comp
      ((measurable_const (a := (boundedObjective B D,r))).prodMk measurable_id)
  exact Measure.dirac_bind hm (f D)

theorem releaseWitness_law {Γ : List ValueType} {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (epsilon tau B : Term Γ .real) (D r : Term Γ (weightType n)) (s : Environment Γ)
    (he : epsilon.eval s = (fullRunConfig n (precisionParameters p)).oracle.eps1)
    (ht : tau.eval s = (fullRunConfig n (precisionParameters p)).oracle.tau1)
    (hB : B.eval s = publicObjectiveBound n (precisionParameters p)) :
    ((witnessCommand (releaseSolver hn p hp) (fullRunConfig n (precisionParameters p)).oracle.k
      (fullRunConfig n (precisionParameters p)).oracle.K epsilon tau B D r).code.law s).map decodeWitness =
      VerifiedRelease.witnessKernel hn p hp (decodeWeights (D.eval s),decodeWeights (r.eval s)) := by
  rw [witnessCommand_law _ _ _ _ _ _ _ _ he ht (approxConfig_bounds hn hp).eps_pos,hB]
  change _ = (RandomizedWitness.run _ (VerifiedRelease.solve hn p hp) _ _ _).law
  exact (deterministicWitness_run_law hn _ (approxConfig_bounds hn hp).eps_pos
    (VerifiedRelease.solve hn p hp) (VerifiedRelease.solveValue hn p hp)
    (VerifiedRelease.solve_law hn p hp) _ _ _).symm

end DPCut.TypedMachine
