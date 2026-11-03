import DPCut.TypedMachineSimulation
import DPCut.TypedWitnessTrialLaw

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def stoppedKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → Option β) (hf : Measurable f) :
    Kernel (Option β) (Option β) :=
  ⟨fun state => state.elim (μ.map f) (fun y => Measure.dirac (some y)),
    measurable_option_elim _ (Measure.measurable_dirac.comp measurable_some)⟩

instance stoppedKernel_markov {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → Option β) (hf : Measurable f) :
    IsMarkovKernel (stoppedKernel μ f hf) := by
  constructor
  intro state
  cases state
  · exact Measure.isProbabilityMeasure_map hf.aemeasurable
  · change IsProbabilityMeasure (Measure.dirac _)
    infer_instance

theorem iterateKernel_fixed {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K]
    (x : α) (hx : K x = Measure.dirac x) (rounds : ℕ) :
    iterateKernel K x rounds = Measure.dirac x := by
  induction rounds with
  | zero => rfl
  | succ n ih =>
      rw [iterateKernel,hx,Measure.dirac_bind (iterateKernel_measurable K n),ih]

theorem stoppedKernel_repeat {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → Option β) (hf : Measurable f) (rounds : ℕ) :
    iterateKernel (stoppedKernel μ f hf) none rounds = repeatUntil μ f rounds := by
  induction rounds with
  | zero => rfl
  | succ n ih =>
      change (μ.map f).bind (fun x => iterateKernel (stoppedKernel μ f hf) x n) = _
      rw [bind_map_eq hf (iterateKernel_measurable _ n),repeatUntil]
      congr 1
      funext z
      cases h : f z with
      | none => exact ih
      | some y => exact iterateKernel_fixed _ (some y) rfl n

theorem trialStep_law {Γ : List ValueType} (n : ℕ) (o : OracleConfig)
    (epsilon tau : Term Γ .real) (D r : Term Γ (weightType n)) (X : Term Γ (matrixType n))
    (s : Environment Γ) (he : epsilon.eval s = o.eps1) (ht : tau.eval s = o.tau1)
    (hepos : 0 < o.eps1) (hX : Matrix.PosDef (X.eval s)) (state : (witnessType n).Value) :
    ((trialStep n o.k epsilon tau D r X).code.law (state,s)).map decodeWitness =
      stoppedKernel (approximateTrialLaw o (decodeWeights (D.eval s)) (X.eval s))
        (acceptTrial o (decodeWeights (r.eval s))) (measurable_acceptTrial_fixed o _) (decodeWitness state) := by
  change ((Command.branch (.fst newest) (Command.pure newest)
    (Command.bind (trialSampleCommand n o.k epsilon.weaken D.weaken X.weaken).code
      (Command.pure (acceptTrialTerm n o.k tau.weaken.weaken r.weaken.weaken newest)))).law (state,s)).map _ = _
  rw [Command.law_branch]
  simp only [Term.eval,newest,Local.read]
  cases hf : state.1 with
  | true =>
      simp only [hf,ite_true,Command.law_pure]
      rw [Measure.map_dirac (measurable_decodeWitness n)]
      simp only [decodeWitness,Term.eval,Local.read,hf,ite_true,stoppedKernel,Kernel.coe_mk,Option.elim_some]
  | false =>
      simp only [hf,Bool.false_eq_true,ite_false,Command.law_bind]
      rw [trialSampleCommand_law n o epsilon.weaken D.weaken X.weaken (state,s)
        (by simpa using he) hepos (by simpa using hX)]
      simp only [Term.eval_weaken_env]
      simp only [Command.law_pure]
      let accepted : Term (trialType n o.k :: witnessType n :: Γ) (witnessType n) :=
        acceptTrialTerm n o.k tau.weaken.weaken r.weaken.weaken newest
      let accept : TrialSample n o.k → (witnessType n).Value :=
        fun sample => accepted.eval (sample,state,s)
      have hsample : Measurable accept :=
        accepted.measurable_eval.comp
          (measurable_id.prodMk (measurable_const (a := (state,s))))
      change ((approximateTrialLaw o (decodeWeights (D.eval s)) (X.eval s)).bind
        (fun sample => Measure.dirac (accept sample))).map decodeWitness = _
      rw [Measure.bind_dirac_eq_map _ hsample,Measure.map_map (measurable_decodeWitness n) hsample]
      have heval (sample : TrialSample n o.k) :
          decodeWitness ((acceptTrialTerm n o.k tau.weaken.weaken r.weaken.weaken newest).eval (sample,state,s)) =
            acceptTrial o (decodeWeights (r.eval s)) sample := by
        simpa [Term.eval,newest,Local.read] using
          eval_acceptTrialTerm n o.k tau.weaken.weaken r.weaken.weaken newest (sample,state,s) o rfl (by simpa using ht)
      have hfunc : decodeWitness ∘ accept = acceptTrial o (decodeWeights (r.eval s)) := funext heval
      rw [hfunc]
      simp only [decodeWitness,hf,Bool.false_eq_true,ite_false,stoppedKernel,Kernel.coe_mk,Option.elim_none]

theorem trialsCommand_law {Γ : List ValueType} (n : ℕ) (o : OracleConfig)
    (epsilon tau : Term Γ .real) (D r : Term Γ (weightType n)) (X : Term Γ (matrixType n))
    (s : Environment Γ) (he : epsilon.eval s = o.eps1) (ht : tau.eval s = o.tau1)
    (hepos : 0 < o.eps1) (hX : Matrix.PosDef (X.eval s)) :
    ((trialsCommand n o.k o.K epsilon tau D r X).code.law s).map decodeWitness =
      repeatUntil (approximateTrialLaw o (decodeWeights (D.eval s)) (X.eval s))
        (acceptTrial o (decodeWeights (r.eval s))) o.K := by
  let body := (trialStep n o.k epsilon tau D r X).code
  letI := approximateTrialLaw_probability o hepos (decodeWeights (D.eval s)) (X.eval s)
  let K := stoppedKernel (approximateTrialLaw o (decodeWeights (D.eval s)) (X.eval s))
    (acceptTrial o (decodeWeights (r.eval s))) (measurable_acceptTrial_fixed o _)
  rw [trialsCommand,BoundedCommand.iterate,Command.law_iterate]
  have hi := iteration_simulation (fun x => body.law (x,s))
    (body.measurable_law.comp (measurable_id.prodMk measurable_const)) (fun x => Command.law_probability body (x,s))
    K decodeWitness (measurable_decodeWitness n)
    (trialStep_law n o epsilon tau D r X s he ht hepos hX) o.K ((noWitness n).eval s)
  change (iterateLaw (fun x => body.law (x,s)) ((noWitness n).eval s) o.K).map decodeWitness = _
  exact hi.trans (stoppedKernel_repeat _ _ _ _)

end DPCut.TypedMachine
