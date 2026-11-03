import DPCut.TypedGuardedKernel

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

theorem law_bind_continue {Γ : List ValueType} {a b : ValueType} {β : Type*} [MeasurableSpace β]
    (first : Command Γ a) (next : Command (a :: Γ) b) (s : Environment Γ)
    (F : b.Value → Measure β) (hF : Measurable F) :
    ((Command.bind first next).law s).bind F =
      (first.law s).bind (fun x => (next.law (x,s)).bind F) := by
  rw [Command.law_bind]
  exact Measure.bind_bind
    (next.measurable_law.comp (measurable_id.prodMk (measurable_const (a:=s)))).aemeasurable hF.aemeasurable

theorem law_pure_continue {Γ : List ValueType} {a : ValueType} {β : Type*} [MeasurableSpace β]
    (value : Term Γ a) (s : Environment Γ) (F : a.Value → Measure β) (hF : Measurable F) :
    ((Command.pure value).law s).bind F = F (value.eval s) := by
  rw [Command.law_pure]
  exact Measure.dirac_bind hF _

theorem map_continue {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (decode : α → β) (hd : Measurable decode)
    (F : β → Measure γ) (hF : Measurable F) :
    μ.bind (fun x => F (decode x)) = (μ.map decode).bind F :=
  (bind_map_eq hd hF).symm

theorem witness_elim_bind {n : ℕ} {β : Type*} [MeasurableSpace β] (μ : Measure (witnessType n).Value)
    (no : Measure β) (yes : Weights n → Measure β) (hy : Measurable yes) :
    μ.bind (fun x => if x.1 then yes (decodeWeights x.2) else no) =
      (μ.map decodeWitness).bind (fun state => state.elim no yes) := by
  rw [bind_map_eq (measurable_decodeWitness n) (measurable_option_elim no hy)]
  congr 1
  funext x
  cases h : x.1 <;> simp [decodeWitness,h]

end DPCut.TypedMachine
