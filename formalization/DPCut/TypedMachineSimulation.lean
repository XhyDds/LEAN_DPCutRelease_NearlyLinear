import DPCut.TypedMachineErasure

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

def iterateKernel {α : Type*} [MeasurableSpace α] (K : Kernel α α) (initial : α) : ℕ → Measure α
  | 0 => Measure.dirac initial
  | n+1 => (K initial).bind fun x => iterateKernel K x n

theorem iterateKernel_measurable {α : Type*} [MeasurableSpace α] (K : Kernel α α) [IsMarkovKernel K]
    (n : ℕ) : Measurable (fun x => iterateKernel K x n) := by
  induction n with
  | zero => exact Measure.measurable_dirac
  | succ n ih =>
      exact measurable_bind_kernel K.measurable (ih.comp measurable_snd)

theorem iteration_simulation {a : ValueType} {α : Type*} [MeasurableSpace α]
    (body : a.Value → Measure a.Value) (hb : Measurable body) (hp : ∀ x, IsProbabilityMeasure (body x))
    (K : Kernel α α) [IsMarkovKernel K] (decode : a.Value → α) (hd : Measurable decode)
    (hstep : ∀ x, (body x).map decode = K (decode x)) (rounds : ℕ) (initial : a.Value) :
    (iterateLaw body initial rounds).map decode = iterateKernel K (decode initial) rounds := by
  induction rounds generalizing initial with
  | zero => rw [iterateLaw, Measure.map_dirac hd]; rfl
  | succ n ih =>
      rw [iterateLaw, map_bind_eq (iterateLaw_properties body hb hp n).1 hd]
      have heq : (fun x => (iterateLaw body x n).map decode) =
          fun x => iterateKernel K (decode x) n := funext ih
      rw [heq, ← bind_map_eq hd (iterateKernel_measurable K n),hstep]
      rfl

theorem iterateKernel_congr {α : Type*} [MeasurableSpace α] (K L : Kernel α α)
    (h : ∀ x, K x = L x) (rounds : ℕ) (initial : α) :
    iterateKernel K initial rounds = iterateKernel L initial rounds := by
  induction rounds generalizing initial with
  | zero => rfl
  | succ n ih =>
      simp only [iterateKernel,h]
      congr 1
      funext x
      exact ih x

end DPCut.TypedMachine
