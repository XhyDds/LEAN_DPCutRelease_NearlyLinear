import DPCut.TypedOuterNoise

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem outerStep_halted {Γ : List ValueType} {n : ℕ} (S : SolverData n) (k K T2 : ℕ)
    (terms : RunTerms Γ) (w : Term Γ (weightType n)) (s : Environment Γ)
    (state : (weightType n).Value × (weightType n).Value) :
    (outerStep S k K T2 terms w).code.law ((true,state),s) = Measure.dirac (true,state) := by
  simp only [outerStep,BoundedCommand.branch,Command.law_branch,Term.eval,newest,Local.read,ite_true,
    BoundedCommand.pure,Command.law_pure]

theorem outerStopLoop_eq {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (he2 : 0 < c.eps2) (B : ℝ) (terms : RunTerms Γ)
    (w : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches p c B s)
    (rounds : ℕ) (a output : (weightType n).Value) :
    stopLoop (guardedKernel (outerStep S c.oracle.k c.oracle.K c.T2 terms w).code s)
      (fun state => decodeWeights state.2) (a,output) rounds =
      OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
        (decodeWeights (w.eval s)) rounds (decodeWeights a) (decodeWeights output) := by
  let K := numericalWitnessKernel S c.oracle he B
  let body := (outerStep S c.oracle.k c.oracle.K c.T2 terms w).code
  let loop := guardedKernel body s
  have hfinish : Measurable (fun state : (weightType n).Value × (weightType n).Value => decodeWeights state.2) :=
    (measurable_decodeWeights n).comp measurable_snd
  induction rounds generalizing a output with
  | zero => rfl
  | succ rounds ih =>
      have ih' (state : (weightType n).Value × (weightType n).Value) :
          stopLoop (guardedKernel body s) (fun state => decodeWeights state.2) state rounds =
            OracleReplacement.outerLoop K p c (decodeWeights (w.eval s)) rounds
              (decodeWeights state.1) (decodeWeights state.2) := by
        rcases state with ⟨a,output⟩
        exact ih a output
      change (body.law ((false,(a,output)),s)).bind (fun result =>
        if result.1 then Measure.dirac (decodeWeights result.2.2)
        else stopLoop (guardedKernel body s) (fun state => decodeWeights state.2) result.2 rounds) = _
      simp_rw [ih']
      let R := fun state : Weights n × Weights n =>
        OracleReplacement.outerLoop K p c (decodeWeights (w.eval s)) rounds state.1 state.2
      have hR : Measurable R :=
        OracleReplacement.measurable_outerLoop K p c he2 rounds measurable_const measurable_fst measurable_snd
      exact outerStep_continue S p c he he2 B terms w s hs a output
        Measure.dirac R Measure.measurable_dirac hR

theorem outerCommand_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (he2 : 0 < c.eps2) (B : ℝ) (terms : RunTerms Γ)
    (w : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches p c B s) :
    ((outerCommand S c.oracle.k c.oracle.K c.T1 c.T2 terms w).code.law s).map decodeWeights =
      OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
        (decodeWeights (w.eval s)) c.T1 1 0 := by
  let body := (outerStep S c.oracle.k c.oracle.K c.T2 terms w).code
  simp only [outerCommand,BoundedCommand.bind,BoundedCommand.pure]
  rw [law_bind_pure,BoundedCommand.iterate,Command.law_iterate]
  simp only [Term.eval,newest,Local.read]
  have hproj : Measurable (fun x : (outerStateType n).Value => x.2.2) :=
    measurable_snd.comp measurable_snd
  rw [Measure.map_map (measurable_decodeWeights n) hproj]
  have hfinish : Measurable (fun state : (weightType n).Value × (weightType n).Value => decodeWeights state.2) :=
    (measurable_decodeWeights n).comp measurable_snd
  have hi := guardedIteration_finish body s (outerStep_halted S c.oracle.k c.oracle.K c.T2 terms w s)
    (fun state => decodeWeights state.2) hfinish ((oneWeights n).eval s,(zeroWeights n).eval s) c.T1
  change (iterateLaw (fun state => body.law (state,s)) (false,((oneWeights n).eval s,(zeroWeights n).eval s))
    c.T1).map (fun state => decodeWeights state.2.2) = _
  rw [hi,outerStopLoop_eq S p c he he2 B terms w s hs]
  rw [eval_oneWeights,eval_zeroWeights]

end DPCut.TypedMachine
