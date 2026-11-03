import DPCut.TypedMachineSimulation
import DPCut.TypedStoppedTrials

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def stoppedStep {α : Type*} [MeasurableSpace α] (K : Kernel α (Bool × α)) :
    Kernel (Bool × α) (Bool × α) :=
  ⟨fun state => if state.1 then Measure.dirac state else K state.2,
    Measurable.ite (measurable_fst (measurableSet_singleton true)) Measure.measurable_dirac
      (K.measurable.comp measurable_snd)⟩

instance stoppedStep_markov {α : Type*} [MeasurableSpace α]
    (K : Kernel α (Bool × α)) [IsMarkovKernel K] : IsMarkovKernel (stoppedStep K) := by
  constructor
  intro state
  change IsProbabilityMeasure (if state.1 then Measure.dirac state else K state.2)
  split <;> infer_instance

def stopLoop {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α (Bool × α)) (finish : α → β) (initial : α) : ℕ → Measure β
  | 0 => Measure.dirac (finish initial)
  | n+1 => (K initial).bind fun result =>
      if result.1 then Measure.dirac (finish result.2) else stopLoop K finish result.2 n

theorem stopLoop_measurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α (Bool × α)) [IsMarkovKernel K] (finish : α → β) (hf : Measurable finish)
    (rounds : ℕ) : Measurable (fun x => stopLoop K finish x rounds) := by
  induction rounds with
  | zero => exact Measure.measurable_dirac.comp hf
  | succ n ih =>
      exact measurable_bind_kernel K.measurable
        (Measurable.ite ((measurable_fst.comp measurable_snd) (measurableSet_singleton true))
          (Measure.measurable_dirac.comp (hf.comp (measurable_snd.comp measurable_snd)))
          (ih.comp (measurable_snd.comp measurable_snd)))

theorem stoppedIteration_finish {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (K : Kernel α (Bool × α)) [IsMarkovKernel K] (finish : α → β) (hf : Measurable finish)
    (rounds : ℕ) (state : Bool × α) :
    (iterateKernel (stoppedStep K) state rounds).map (fun r => finish r.2) =
      if state.1 then Measure.dirac (finish state.2) else stopLoop K finish state.2 rounds := by
  have hm : Measurable (fun r : Bool × α => finish r.2) := hf.comp measurable_snd
  induction rounds generalizing state with
  | zero =>
      rw [iterateKernel,Measure.map_dirac hm,stopLoop]
      split <;> rfl
  | succ n ih =>
      by_cases h : state.1 = true
      · rw [iterateKernel_fixed _ state (by simp [stoppedStep,h]) (n+1),Measure.map_dirac hm]
        simp only [h,ite_true]
      · rw [iterateKernel,map_bind_eq (iterateKernel_measurable _ n) hm]
        simp only [stoppedStep,Kernel.coe_mk,h,ite_false,stopLoop]
        congr 1
        funext result
        exact ih result

theorem command_stoppedLoop {Γ : List ValueType} {a : ValueType} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (body : Command (.pair .boolean a :: Γ) (.pair .boolean a)) (s : Environment Γ)
    (decode : a.Value → α) (hd : Measurable decode)
    (K : Kernel α (Bool × α)) [IsMarkovKernel K]
    (hstep : ∀ state : Bool × a.Value,
      (body.law (state,s)).map (fun r => (r.1,decode r.2)) = stoppedStep K (state.1,decode state.2))
    (finish : α → β) (hf : Measurable finish) (initial : a.Value) (rounds : ℕ) :
    (iterateLaw (fun state => body.law (state,s)) (false,initial) rounds).map (fun state => finish (decode state.2)) =
      stopLoop K finish (decode initial) rounds := by
  have hdecode : Measurable (fun r : Bool × a.Value => (r.1,decode r.2)) :=
    measurable_fst.prodMk (hd.comp measurable_snd)
  have hi := iteration_simulation (fun state => body.law (state,s))
    (body.measurable_law.comp (measurable_id.prodMk (measurable_const (a:=s))))
    (fun state => Command.law_probability body (state,s)) (stoppedStep K) _ hdecode hstep rounds (false,initial)
  have hmap := congrArg (fun μ : Measure (Bool × α) => μ.map (fun r => finish r.2)) hi
  dsimp only at hmap
  have hfinish : Measurable (fun r : Bool × α => finish r.2) := hf.comp measurable_snd
  rw [Measure.map_map hfinish hdecode,stoppedIteration_finish K finish hf] at hmap
  exact hmap

end DPCut.TypedMachine
