import DPCut.TypedReleaseTermRefinement
import DPCut.TypedWitnessKernel
import DPCut.TypedContinuation

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def aggregateContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F0 F1 : Aggregate n → Measure β) (state : (aggregateStateType n).Value) : Measure β :=
  if state.1 then F0 (decodeAggregate state.2) else F1 (decodeAggregate state.2)

theorem measurable_aggregateContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F0 F1 : Aggregate n → Measure β) (h0 : Measurable F0) (h1 : Measurable F1) :
    Measurable (aggregateContinuation F0 F1) :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    (h0.comp ((measurable_decodeAggregate n).comp measurable_snd))
    (h1.comp ((measurable_decodeAggregate n).comp measurable_snd))

theorem aggregateFinish_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (positive : Bool) (a : Term Γ (aggregateType n)) (result : Term Γ (witnessType n)) (s : Environment Γ)
    (F0 F1 : Aggregate n → Measure β) (h0 : Measurable F0) (h1 : Measurable F1) :
    ((aggregateFinish positive a result).code.law s).bind (aggregateContinuation F0 F1) =
      if (result.eval s).1 then
        F1 ((if positive then aggregatePlusStep else aggregateMinusStep) (decodeAggregate (a.eval s))
          (decodeWeights (result.eval s).2)) else F0 (decodeAggregate (a.eval s)) := by
  have hC := measurable_aggregateContinuation F0 F1 h0 h1
  simp only [aggregateFinish,BoundedCommand.branch,BoundedCommand.pure,Command.law_branch,Term.eval]
  split
  · rw [law_pure_continue _ _ _ hC]
    cases positive <;>
      simp [aggregateContinuation,Term.eval,eval_aggregateAddTrue,eval_aggregateAddFalse]
  · rw [law_pure_continue _ _ _ hC]
    rfl

theorem aggregateAfterPlus_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (S : SolverData n) (o : OracleConfig) (he : 0 < o.eps1) (B : ℝ)
    (terms : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n))
    (a : Term Γ (aggregateType n)) (result : Term Γ (witnessType n)) (s : Environment Γ)
    (hs : terms.Matches o B s)
    (F0 F1 : Aggregate n → Measure β) (h0 : Measurable F0) (h1 : Measurable F1) :
    ((aggregateAfterPlus S o.k o.K terms gamma w h a result).code.law s).bind (aggregateContinuation F0 F1) =
      if (result.eval s).1 then
        F1 (aggregatePlusStep (decodeAggregate (a.eval s)) (decodeWeights (result.eval s).2))
      else (numericalWitnessKernel S o he B
          (minusDiscrepancy (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) (decodeAggregate (a.eval s)).residual,
            (decodeAggregate (a.eval s)).residual)).bind
          (fun state => state.elim (F0 (decodeAggregate (a.eval s)))
            (fun g => F1 (aggregateMinusStep (decodeAggregate (a.eval s)) g))) := by
  have hC := measurable_aggregateContinuation F0 F1 h0 h1
  simp only [aggregateAfterPlus,BoundedCommand.branch,BoundedCommand.pure,BoundedCommand.bind,
    Command.law_branch,Term.eval]
  split
  · rw [law_pure_continue _ _ _ hC]
    simp [aggregateContinuation,Term.eval]
  · rw [law_bind_continue _ _ _ _ hC]
    have heval (x : (witnessType n).Value) :
        ((aggregateFinish false a.weaken newest).code.law (x,s)).bind (aggregateContinuation F0 F1) =
          if x.1 then F1 (aggregateMinusStep (decodeAggregate (a.eval s)) (decodeWeights x.2))
          else F0 (decodeAggregate (a.eval s)) := by
      simpa only [Term.eval_weaken_env,newest,Term.eval,Local.read,Bool.false_eq_true,ite_false] using
        aggregateFinish_continue false a.weaken newest (x,s) F0 F1 h0 h1
    simp_rw [heval]
    have hyes : Measurable (fun g : Weights n => F1 (aggregateMinusStep (decodeAggregate (a.eval s)) g)) :=
      h1.comp (measurable_aggregateMinusStep _)
    rw [witness_elim_bind _ _ _ hyes,
      witnessCommand_kernel S o he B terms _ _ s hs]
    simp only [eval_minusDiscrepancy,eval_residualTerm]

theorem aggregateStep_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (S : SolverData n) (o : OracleConfig) (he : 0 < o.eps1) (B : ℝ)
    (terms : OracleTerms Γ) (gamma : Term Γ .real) (w h : Term Γ (weightType n))
    (s : Environment Γ) (hs : terms.Matches o B s) (a : (aggregateType n).Value)
    (F0 F1 : Aggregate n → Measure β) (h0 : Measurable F0) (h1 : Measurable F1) :
    ((aggregateStep S o.k o.K terms gamma w h).code.law ((false,a),s)).bind (aggregateContinuation F0 F1) =
      if (decodeAggregate a).residual = 0 then F0 (decodeAggregate a) else
      (numericalWitnessKernel S o he B
        (plusDiscrepancy (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) (decodeAggregate a).residual,
          (decodeAggregate a).residual)).bind fun gp => gp.elim
        ((numericalWitnessKernel S o he B
          (minusDiscrepancy (gamma.eval s) (decodeWeights (w.eval s)) (decodeWeights (h.eval s)) (decodeAggregate a).residual,
            (decodeAggregate a).residual)).bind fun gm =>
              gm.elim (F0 (decodeAggregate a)) (fun g => F1 (aggregateMinusStep (decodeAggregate a) g)))
        (fun g => F1 (aggregatePlusStep (decodeAggregate a) g)) := by
  have hC := measurable_aggregateContinuation F0 F1 h0 h1
  simp only [aggregateStep,BoundedCommand.branch,BoundedCommand.pure,BoundedCommand.bind,
    Command.law_branch,Term.eval,newest,Local.read,
    Bool.false_eq_true,ite_false,eval_allZero,eval_residualTerm,decide_eq_true_eq]
  by_cases hz : (decodeAggregate a).residual = 0
  · simp only [hz,ite_true]
    rw [law_pure_continue _ _ _ hC]
    rfl
  · simp only [hz,ite_false]
    rw [law_bind_continue _ _ _ _ hC]
    have hs0 : (terms.weaken : OracleTerms (aggregateStateType n :: Γ)).Matches o B ((false,a),s) :=
      OracleTerms.Matches.weaken (a := aggregateStateType n) terms o B s hs (false,a)
    have heval (x : (witnessType n).Value) := aggregateAfterPlus_continue S o he B
      terms.weaken.weaken gamma.weaken.weaken w.weaken.weaken h.weaken.weaken
      ((Term.snd newest : Term (aggregateStateType n :: Γ) (aggregateType n)).weaken)
      newest (x,(false,a),s)
      (OracleTerms.Matches.weaken (a := witnessType n)
        (terms.weaken : OracleTerms (aggregateStateType n :: Γ)) o B ((false,a),s) hs0 x)
      F0 F1 h0 h1
    simp only [Term.eval_weaken_env,Term.eval,newest,Local.read] at heval
    simp_rw [heval]
    have hyes : Measurable (fun g : Weights n => F1 (aggregatePlusStep (decodeAggregate a) g)) :=
      h1.comp (measurable_aggregatePlusStep (decodeAggregate a))
    rw [witness_elim_bind _ _ _ hyes]
    let residual : Term (aggregateStateType n :: Γ) (weightType n) := residualTerm (.snd newest)
    have hplus := witnessCommand_kernel S o he B
      (terms.weaken : OracleTerms (aggregateStateType n :: Γ))
      (plusDiscrepancyTerm gamma.weaken w.weaken h.weaken residual) residual ((false,a),s) hs0
    simp only [OracleTerms.weaken,Term.eval_weaken_env,eval_plusDiscrepancy,eval_residualTerm,
      residual,Term.eval,newest,Local.read] at hplus
    rw [hplus]

end DPCut.TypedMachine
