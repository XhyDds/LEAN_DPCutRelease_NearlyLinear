import DPCut.TypedAggregateContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem aggregateStep_halted {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K : ℕ)
    (terms : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n))
    (s : Environment Γ) (a : (aggregateType n).Value) :
    (aggregateStep S k K terms gamma w h).code.law ((true,a),s) = Measure.dirac (true,a) := by
  simp only [aggregateStep,BoundedCommand.branch,Command.law_branch,Term.eval,newest,Local.read,ite_true,
    BoundedCommand.pure,Command.law_pure]

theorem aggregateStopLoop_eq {Γ : List ValueType} {n : ℕ} (S : SolverData n) (o : OracleConfig)
    (he : 0 < o.eps1) (B : ℝ) (terms : OracleTerms Γ) (gamma : Term Γ .real)
    (w h : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches o B s)
    (rounds : ℕ) (a : (aggregateType n).Value) :
    stopLoop (guardedKernel (aggregateStep S o.k o.K terms gamma w h).code s) decodeAggregate a rounds =
      OracleReplacement.aggregateLoop (numericalWitnessKernel S o he B) (gamma.eval s)
        (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) rounds (decodeAggregate a) := by
  let K := numericalWitnessKernel S o he B
  let body := (aggregateStep S o.k o.K terms gamma w h).code
  induction rounds generalizing a with
  | zero => rfl
  | succ rounds ih =>
      change (body.law ((false,a),s)).bind (fun result =>
        if result.1 then Measure.dirac (decodeAggregate result.2)
        else stopLoop (guardedKernel (aggregateStep S o.k o.K terms gamma w h).code s) decodeAggregate result.2 rounds) = _
      simp_rw [ih]
      let R := OracleReplacement.aggregateLoop K (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) rounds
      have hR : Measurable R :=
        OracleReplacement.measurable_aggregateLoop K (gamma.eval s) rounds
          (measurable_const (a:=decodeWeights (w.eval s))) (measurable_const (a:=decodeWeights (h.eval s))) measurable_id
      have hstep := aggregateStep_continue S o he B terms gamma w h s hs a
        Measure.dirac R Measure.measurable_dirac hR
      exact hstep

theorem aggregateCommand_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (o : OracleConfig)
    (he : 0 < o.eps1) (B : ℝ) (terms : OracleTerms Γ) (gamma : Term Γ .real)
    (w h : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches o B s) :
    ((aggregateCommand S o.k o.K terms gamma w h).code.law s).map decodeAggregate =
      OracleReplacement.aggregateLaw (numericalWitnessKernel S o he B) (gamma.eval s)
        (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) := by
  let body := (aggregateStep S o.k o.K terms gamma w h).code
  simp only [aggregateCommand,BoundedCommand.bind,BoundedCommand.pure]
  rw [law_bind_pure,BoundedCommand.iterate,Command.law_iterate]
  simp only [Term.eval,newest,Local.read]
  have hproj : Measurable (fun x : (aggregateStateType n).Value => x.2) := measurable_snd
  rw [Measure.map_map (measurable_decodeAggregate n) hproj]
  have hi := guardedIteration_finish body s (aggregateStep_halted S o.k o.K terms gamma w h s)
    decodeAggregate (measurable_decodeAggregate n) ((initialAggregate n).eval s) (Fintype.card (Edge n))
  change (iterateLaw (fun state => body.law (state,s)) (false,(initialAggregate n).eval s)
    (Fintype.card (Edge n))).map (fun state => decodeAggregate state.2) = _
  rw [hi,aggregateStopLoop_eq S o he B terms gamma w h s hs]
  change OracleReplacement.aggregateLoop _ _ _ _ _ (decodeAggregate ((initialAggregate n).eval s)) = _
  have ha : decodeAggregate ((initialAggregate n).eval s) = (⟨0,0,1⟩ : Aggregate n) := by
    apply aggregate_ext <;> norm_num [initialAggregate,decodeAggregate,Term.eval,zeroWeights,oneWeights,decodeWeights] <;> rfl
  rw [ha]
  rfl

end DPCut.TypedMachine
