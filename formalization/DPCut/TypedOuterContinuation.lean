import DPCut.TypedInnerLaw

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def RunTerms.Matches {Γ : List ValueType} (terms : RunTerms Γ) (p : Parameters) (c : RunConfig)
    (B : ℝ) (s : Environment Γ) : Prop :=
  terms.oracle.Matches c.oracle B s ∧ terms.gamma.eval s = p.gamma ∧ terms.eta.eval s = c.eta ∧
    terms.epsilon.eval s = c.eps2 ∧ terms.tau.eval s = c.tau2 ∧
    terms.massCap.eval s = c.massCap ∧ terms.stop.eval s = c.stop

theorem RunTerms.Matches.weaken {Γ : List ValueType} {a : ValueType}
    (terms : RunTerms Γ) (p : Parameters) (c : RunConfig) (B : ℝ) (s : Environment Γ)
    (h : terms.Matches p c B s) (x : a.Value) :
    terms.weaken.Matches p c B (x,s) := by
  simpa only [RunTerms.Matches,RunTerms.weaken,OracleTerms.Matches,OracleTerms.weaken,Term.eval_weaken_env]
    using h

def outerContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (state : (outerStateType n).Value) : Measure β :=
  if state.1 then F0 (decodeWeights state.2.2)
    else F1 (decodeWeights state.2.1,decodeWeights state.2.2)

theorem measurable_outerContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h0 : Measurable F0) (h1 : Measurable F1) : Measurable (outerContinuation F0 F1) :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    (h0.comp ((measurable_decodeWeights n).comp (measurable_snd.comp measurable_snd)))
    (h1.comp (((measurable_decodeWeights n).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_decodeWeights n).comp (measurable_snd.comp measurable_snd))))

theorem outerAfterInner_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (a output : Term Γ (weightType n)) (result : Term Γ (innerResultType n)) (s : Environment Γ)
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h0 : Measurable F0) (h1 : Measurable F1) :
    ((outerAfterInner a output result).code.law s).bind (outerContinuation F0 F1) =
      if (result.eval s).1 then
        F1 (residualUpdate (decodeWeights (a.eval s)) (decodeWeights (result.eval s).2.2),
          decodeWeights (output.eval s)+hadamard (decodeWeights (result.eval s).2.1) (decodeWeights (result.eval s).2.2))
      else F1 (decodeWeights (a.eval s),decodeWeights (output.eval s)) := by
  have hC := measurable_outerContinuation F0 F1 h0 h1
  simp only [outerAfterInner,BoundedCommand.branch,BoundedCommand.pure,Command.law_branch,Term.eval]
  split
  · rw [law_pure_continue _ _ _ hC]
    simp [outerContinuation,Term.eval]
  · rw [law_pure_continue _ _ _ hC]
    rfl

theorem inner_elim_bind {n : ℕ} {β : Type*} [MeasurableSpace β] (μ : Measure (innerResultType n).Value)
    (no : Measure β) (yes : Weights n × Weights n → Measure β) (hy : Measurable yes) :
    μ.bind (fun x => if x.1 then yes (decodeWeights x.2.1,decodeWeights x.2.2) else no) =
      (μ.map decodeInner).bind (fun state => state.elim no yes) := by
  rw [bind_map_eq (measurable_decodeInner n) (measurable_option_elim no hy)]
  congr 1
  funext x
  cases h : x.1 <;> simp [decodeInner,h]

def outerInnerContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F1 : Weights n × Weights n → Measure β) (a output : Weights n)
    (result : Option (Weights n × Weights n)) : Measure β :=
  result.elim (F1 (a,output)) (fun hr => F1 (residualUpdate a hr.2,output+hadamard hr.1 hr.2))

theorem measurable_outerInnerContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (F1 : Weights n × Weights n → Measure β) (h1 : Measurable F1) (a output : Weights n) :
    Measurable (outerInnerContinuation F1 a output) := by
  apply measurable_option_elim
  apply h1.comp
  unfold residualUpdate hadamard
  fun_prop

theorem outerAfterMass_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (S : SolverData n) (p : Parameters) (c : RunConfig) (he : 0 < c.oracle.eps1) (B : ℝ)
    (terms : RunTerms Γ) (w a output : Term Γ (weightType n)) (M : Term Γ .real)
    (s : Environment Γ) (hs : terms.Matches p c B s)
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h0 : Measurable F0) (h1 : Measurable F1) :
    ((outerAfterMass S c.oracle.k c.oracle.K c.T2 terms w a output M).code.law s).bind (outerContinuation F0 F1) =
      if decodeWeights (a.eval s) = 0 ∨ M.eval s ≤ c.stop then F0 (decodeWeights (output.eval s)) else
      (OracleReplacement.innerLoop (numericalWitnessKernel S c.oracle he B) p c
        (hadamard (decodeWeights (a.eval s)) (decodeWeights (w.eval s))) (M.eval s) c.T2
        (initialEstimate (M.eval s) (decodeWeights (a.eval s)))).bind
          (outerInnerContinuation F1 (decodeWeights (a.eval s)) (decodeWeights (output.eval s))) := by
  have hC := measurable_outerContinuation F0 F1 h0 h1
  simp only [outerAfterMass,BoundedCommand.branch,BoundedCommand.pure,BoundedCommand.bind,
    Command.law_branch,Term.eval,Comparison.real,Bool.or_eq_true,decide_eq_true_eq,eval_allZero,hs.2.2.2.2.2.2]
  split
  · rw [law_pure_continue _ _ _ hC]
    rfl
  · rw [law_bind_continue _ _ _ _ hC]
    have heval (result : (innerResultType n).Value) :=
      outerAfterInner_continue (Γ := innerResultType n :: Γ)
        a.weaken output.weaken newest (result,s) F0 F1 h0 h1
    simp only [Term.eval_weaken_env,newest,Term.eval,Local.read] at heval
    simp only [newest]
    simp_rw [heval]
    have hy : Measurable (fun hr : Weights n × Weights n =>
        F1 (residualUpdate (decodeWeights (a.eval s)) hr.2,
          decodeWeights (output.eval s)+hadamard hr.1 hr.2)) := by
      apply h1.comp
      unfold residualUpdate hadamard
      fun_prop
    rw [inner_elim_bind _ _ _ hy,
      innerCommand_law S p c he B terms.oracle terms.gamma terms.eta M (productWeights a w) (initialEstimateTerm M a)
        s hs.1 hs.2.1 hs.2.2.1]
    simp only [eval_productWeights,eval_initialEstimateTerm]
    rfl

end DPCut.TypedMachine
