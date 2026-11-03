import DPCut.TypedStoppedIteration

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def guardedKernel {Γ : List ValueType} {a : ValueType}
    (body : Command (.pair .boolean a :: Γ) (.pair .boolean a)) (s : Environment Γ) :
    Kernel a.Value (Bool × a.Value) :=
  ⟨fun x => body.law ((false,x),s),
    body.measurable_law.comp
      ((measurable_const.prodMk measurable_id).prodMk (measurable_const (a:=s)))⟩

instance guardedKernel_markov {Γ : List ValueType} {a : ValueType}
    (body : Command (.pair .boolean a :: Γ) (.pair .boolean a)) (s : Environment Γ) :
    IsMarkovKernel (guardedKernel body s) := ⟨fun x => Command.law_probability body ((false,x),s)⟩

theorem guardedKernel_step {Γ : List ValueType} {a : ValueType}
    (body : Command (.pair .boolean a :: Γ) (.pair .boolean a)) (s : Environment Γ)
    (htrue : ∀ x : a.Value, body.law ((true,x),s) = Measure.dirac (true,x))
    (state : Bool × a.Value) :
    body.law (state,s) = stoppedStep (guardedKernel body s) state := by
  rcases state with ⟨flag,x⟩
  cases flag
  · rfl
  · exact htrue x

theorem guardedIteration_finish {Γ : List ValueType} {a : ValueType} {β : Type*} [MeasurableSpace β]
    (body : Command (.pair .boolean a :: Γ) (.pair .boolean a)) (s : Environment Γ)
    (htrue : ∀ x : a.Value, body.law ((true,x),s) = Measure.dirac (true,x))
    (finish : a.Value → β) (hf : Measurable finish) (initial : a.Value) (rounds : ℕ) :
    (iterateLaw (fun state => body.law (state,s)) (false,initial) rounds).map (fun state => finish state.2) =
      stopLoop (guardedKernel body s) finish initial rounds := by
  apply command_stoppedLoop body s id measurable_id (guardedKernel body s) _ finish hf initial rounds
  intro state
  have hmap : (fun r : Bool × a.Value => (r.1,id r.2)) = id := by funext r; exact Prod.eta r
  rw [hmap,Measure.map_id]
  exact guardedKernel_step body s htrue state

theorem law_bind_pure {Γ : List ValueType} {a b : ValueType}
    (first : Command Γ a) (value : Term (a :: Γ) b) (s : Environment Γ) :
    (Command.bind first (.pure value)).law s =
      (first.law s).map (fun x => value.eval (x,s)) := by
  rw [Command.law_bind]
  simp only [Command.law_pure]
  exact Measure.bind_dirac_eq_map _
    (value.measurable_eval.comp (measurable_id.prodMk (measurable_const (a:=s))))

theorem law_bind_pure_first {Γ : List ValueType} {a b : ValueType}
    (value : Term Γ a) (next : Command (a :: Γ) b) (s : Environment Γ) :
    (Command.bind (.pure value) next).law s = next.law (value.eval s,s) := by
  rw [Command.law_bind,Command.law_pure]
  exact Measure.dirac_bind
    (next.measurable_law.comp (measurable_id.prodMk (measurable_const (a:=s)))) _

end DPCut.TypedMachine
