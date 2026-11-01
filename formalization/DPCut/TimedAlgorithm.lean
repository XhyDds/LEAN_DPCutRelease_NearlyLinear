import DPCut.CostedProgram
import DPCut.RepeatUntil
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Completion-time labels and compatible timeout laws for a random procedure.
`run_law` relates truncation to the reported completion time, and `run_cost`
bounds an assigned cost. Neither field derives time from execution steps or
requires oracle calls. Any measurable function can be represented with time
zero. Thus this interface supports timeout/probability and cost-accounting
arguments, but does not certify operational runtime of the cutting-plane solver. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

variable {Θ α : Type} [MeasurableSpace Θ] [MeasurableSpace α]

lemma measurable_option_elim_vary {β : Type*} [MeasurableSpace β] [Inhabited α]
    {f : Θ → β} {g : α → β} {o : Θ → Option α}
    (hf : Measurable f) (hg : Measurable g) (ho : Measurable o) :
    Measurable (fun θ => (o θ).elim (f θ) g) := by
  classical
  have h : Measurable (fun θ => if o θ = none then f θ else g ((o θ).getD default)) :=
    Measurable.ite (ho measurableSet_option_none) hf
    (hg.comp ((measurable_option_getD default).comp ho))
  convert h using 1
  funext θ
  cases o θ <;> simp

def timeoutResult (fuel : ℕ) (z : ℕ × α) : Option α :=
  if z.1 ≤ fuel then some z.2 else none

@[fun_prop] lemma measurable_timeoutResult (fuel : ℕ) :
    Measurable (timeoutResult (α := α) fuel) := by
  unfold timeoutResult
  exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (measurable_some.comp measurable_snd) measurable_const

structure TimedAlgorithm (Θ α : Type) [MeasurableSpace Θ] [MeasurableSpace α] where
  completed : Kernel Θ (ℕ × α)
  completed_markov : IsMarkovKernel completed
  run : ℕ → Θ → CostedLaw (Option α)
  run_law : ∀ fuel θ, (run fuel θ).law =
    (completed θ).map (timeoutResult fuel)
  run_cost : ∀ fuel θ, (run fuel θ).cost ≤ fuel + 1

attribute [instance] TimedAlgorithm.completed_markov

namespace TimedAlgorithm

variable (A : TimedAlgorithm Θ α)

def expectedCost (θ : Θ) : ℝ≥0∞ := ∫⁻ z, (z.1 : ℝ≥0∞) ∂A.completed θ

lemma measurable_run (fuel : ℕ) : Measurable (fun θ => (A.run fuel θ).law) := by
  simp_rw [A.run_law]
  exact (Measure.measurable_map _ (measurable_timeoutResult fuel)).comp A.completed.measurable

instance run_probability (fuel : ℕ) (θ : Θ) : IsProbabilityMeasure (A.run fuel θ).law := by
  rw [A.run_law]
  exact Measure.isProbabilityMeasure_map (measurable_timeoutResult fuel).aemeasurable

lemma timeout_failure (fuel : ℕ) (θ : Θ) :
    (A.run fuel θ).law {none} = A.completed θ {z | fuel < z.1} := by
  rw [A.run_law, Measure.map_apply (measurable_timeoutResult fuel) measurableSet_option_none]
  congr 1
  ext z
  simp [timeoutResult]

/-- Markov's inequality converts the expected reported-time bound into a timeout
failure probability at most one half. -/
theorem timeout_failure_le_half {fuel : ℕ} (hfuel : 0 < fuel) (θ : Θ)
    (hmean : A.expectedCost θ ≤ (fuel : ℝ≥0∞) / 2) :
    (A.run fuel θ).law {none} ≤ (1 / 2 : ℝ≥0∞) := by
  rw [A.timeout_failure]
  have h0 : (fuel : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfuel.ne'
  have htop : (fuel : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top fuel
  have hm : Measurable (fun z : ℕ × α => (z.1 : ℝ≥0∞)) := by fun_prop
  calc
    _ ≤ A.completed θ {z | (fuel : ℝ≥0∞) ≤ (z.1 : ℝ≥0∞)} := by
      apply measure_mono
      intro z hz
      change fuel < z.1 at hz
      change (fuel : ℝ≥0∞) ≤ (z.1 : ℝ≥0∞)
      exact_mod_cast hz.le
    _ ≤ A.expectedCost θ / fuel := meas_ge_le_lintegral_div hm.aemeasurable h0 htop
    _ ≤ ((fuel : ℝ≥0∞) / 2) / fuel := mul_le_mul_right' hmean _
    _ = 1 / 2 := by
      simp only [div_eq_mul_inv]
      rw [mul_right_comm, ENNReal.mul_inv_cancel h0 htop, one_mul]

end TimedAlgorithm

/-- Independent bounded attempts, stopping at the first completed execution. -/
def costedRestart (attempt : CostedLaw (Option α)) : ℕ → CostedLaw (Option α)
  | 0 => .pure none
  | t + 1 => attempt.bind fun result => result.elim (costedRestart attempt t)
      (fun x => .pure (some x))

lemma costedRestart_law (attempt : CostedLaw (Option α)) (t : ℕ) :
    (costedRestart attempt t).law = repeatUntil attempt.law id t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [costedRestart, CostedLaw.bind_law, repeatUntil]
    congr 1
    funext o
    cases o <;> simp [ih]

lemma costedRestart_cost (attempt : CostedLaw (Option α)) {B : ℝ≥0∞}
    (hB : attempt.cost ≤ B) (t : ℕ) : (costedRestart attempt t).cost ≤ t * B := by
  induction t with
  | zero => simp [costedRestart, CostedLaw.pure]
  | succ t ih =>
    calc
      _ ≤ B + t * B := CostedLaw.bind_cost_le _ _ hB (fun o => by
        cases o
        · exact ih
        · exact zero_le _)
      _ = _ := by push_cast; ring

lemma repeatUntil_id_failure (μ : Measure (Option α)) (t : ℕ) :
    repeatUntil μ id t {none} = (μ {none}) ^ t := by
  induction t with
  | zero => simp [repeatUntil, Measure.dirac_apply' _ measurableSet_option_none]
  | succ t ih =>
    rw [repeatUntil, Measure.bind_apply measurableSet_option_none
      (measurable_repeat_continuation _ measurable_id).aemeasurable]
    have heq : (fun o : Option α =>
        (o.elim (repeatUntil μ id t) (fun y => Measure.dirac (some y))) {none}) =
        ({none} : Set (Option α)).indicator (fun _ => (μ {none}) ^ t) := by
      funext o
      cases o <;> simp [ih, Measure.dirac_apply' _ measurableSet_option_none]
    change (∫⁻ o, (o.elim (repeatUntil μ id t) (fun y => Measure.dirac (some y))) {none} ∂μ) = _
    rw [heq, lintegral_indicator measurableSet_option_none]
    simp [pow_succ, mul_comm]

theorem TimedAlgorithm.restart_failure_le (A : TimedAlgorithm Θ α) {fuel : ℕ}
    (hfuel : 0 < fuel) (θ : Θ)
    (hmean : A.expectedCost θ ≤ (fuel : ℝ≥0∞) / 2) (t : ℕ) :
    (costedRestart (A.run fuel θ) t).law {none} ≤ (1 / 2 : ℝ≥0∞) ^ t := by
  rw [costedRestart_law, repeatUntil_id_failure]
  exact pow_le_pow_left' (A.timeout_failure_le_half hfuel θ hmean) t

end DPCut
