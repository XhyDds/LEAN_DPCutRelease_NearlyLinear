import DPCut.TypedMachineTerms
import DPCut.RealMachineMeasurable

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open MeasureTheory

namespace DPCut.TypedMachine

def ValueType.measurableSpace : (a : ValueType) → MeasurableSpace a.Value
  | .real => inferInstance
  | .natural => inferInstance
  | .boolean => inferInstance
  | .unit => inferInstance
  | .pair a b =>
      letI := a.measurableSpace
      letI := b.measurableSpace
      inferInstance
  | .array _ a =>
      letI := a.measurableSpace
      inferInstance

instance (priority := low) (a : ValueType) : MeasurableSpace a.Value := a.measurableSpace

def environmentMeasurableSpace : (Γ : List ValueType) → MeasurableSpace (Environment Γ)
  | [] => inferInstance
  | a :: Γ =>
      letI := a.measurableSpace
      letI := environmentMeasurableSpace Γ
      inferInstance

instance (priority := low) (Γ : List ValueType) : MeasurableSpace (Environment Γ) := environmentMeasurableSpace Γ

theorem Local.measurable_read {Γ : List ValueType} {a : ValueType} (v : Local Γ a) :
    Measurable v.read := by
  induction v with
  | head => exact measurable_fst
  | tail old ih => exact ih.comp measurable_snd

theorem RealBinary.measurable_eval (op : RealBinary) :
    Measurable (fun p : ℝ × ℝ => op.eval p.1 p.2) := by
  cases op <;> simp only [RealBinary.eval] <;> fun_prop

theorem RealUnary.measurable_eval (op : RealUnary) : Measurable op.eval := by
  change Measurable (fun x => op.eval x)
  cases op <;> simp only [RealUnary.eval] <;> fun_prop

theorem Comparison.measurable_real (op : Comparison) :
    Measurable (fun p : ℝ × ℝ => op.real p.1 p.2) := by
  cases op
  · exact RealMachine.measurable_decision _ (measurableSet_le measurable_fst measurable_snd)
  · exact RealMachine.measurable_decision _ (measurableSet_lt measurable_fst measurable_snd)
  · exact RealMachine.measurable_decision _ (measurableSet_eq_fun measurable_fst measurable_snd)

theorem measurable_array_get {a : ValueType} (n : ℕ) :
    Measurable (fun p : (Fin n → a.Value) × ℕ =>
      if h : p.2 < n then p.1 ⟨p.2,h⟩ else a.zero) := by
  apply measurable_from_prod_countable_left
  intro index
  dsimp only
  split
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_maximum {α : Type*} [MeasurableSpace α] {n : ℕ}
    (values : α → Fin n → ℝ) (hv : Measurable values) (indices : List (Fin n))
    (initial : α → ℝ) (hi : Measurable initial) :
    Measurable (fun s => indices.foldl (fun old i => max old (values s i)) (initial s)) := by
  induction indices generalizing initial with
  | nil => exact hi
  | cons i indices ih => exact ih _ (hi.max (hv.eval))

@[fun_prop] theorem Term.measurable_eval {Γ : List ValueType} {a : ValueType} (term : Term Γ a) :
    Measurable (fun s => term.eval s) := by
  induction term with
  | rational q => exact measurable_const
  | natural n => exact measurable_const
  | boolean b => exact measurable_const
  | unit => exact measurable_const
  | read v => exact v.measurable_read
  | pair a b ha hb => exact ha.prodMk hb
  | fst a ha => exact measurable_fst.comp ha
  | snd a ha => exact measurable_snd.comp ha
  | array values ih => exact measurable_pi_lambda _ ih
  | get values index hv hi => exact (measurable_array_get _).comp (hv.prodMk hi)
  | realBinary op a b ha hb => exact op.measurable_eval.comp (ha.prodMk hb)
  | realUnary op a ha => exact op.measurable_eval.comp ha
  | naturalBinary op a b ha hb =>
      exact (measurable_of_countable (fun p : ℕ × ℕ => op.eval p.1 p.2)).comp (ha.prodMk hb)
  | cast a ha => exact (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp ha
  | ceil a ha => exact Nat.measurable_ceil.comp ha
  | floor a ha => exact Nat.measurable_floor.comp ha
  | realCompare op a b ha hb => exact op.measurable_real.comp (ha.prodMk hb)
  | naturalCompare op a b ha hb =>
      exact (measurable_of_countable (fun p : ℕ × ℕ => op.natural p.1 p.2)).comp (ha.prodMk hb)
  | and a b ha hb => exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp (ha.prodMk hb)
  | or a b ha hb => exact (measurable_of_countable (fun p : Bool × Bool => p.1 || p.2)).comp (ha.prodMk hb)
  | not a ha => exact (measurable_of_countable (fun b : Bool => !b)).comp ha
  | select c a b hc ha hb => exact Measurable.ite (hc (measurableSet_singleton true)) ha hb
  | sum values hv => exact Finset.measurable_sum _ (fun i _ => hv.eval)
  | maximum values hv => exact measurable_maximum _ hv _ _ measurable_const

@[simp] theorem Term.eval_weaken {Γ : List ValueType} {a b : ValueType}
    (term : Term Γ a) (s : Environment Γ) (x : b.Value) :
    term.weaken.eval (x,s) = term.eval s := by
  induction term with
  | rational | natural | boolean | unit | read => rfl
  | pair a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | fst a ha => simp only [Term.weaken, Term.eval, ha]
  | snd a ha => simp only [Term.weaken, Term.eval, ha]
  | array values ih => funext i; exact ih i
  | get values index hv hi => simp only [Term.weaken, Term.eval, hv,hi]
  | realBinary op a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | realUnary op a ha => simp only [Term.weaken, Term.eval, ha]
  | naturalBinary op a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | cast a ha => simp only [Term.weaken, Term.eval, ha]
  | ceil a ha => simp only [Term.weaken, Term.eval, ha]
  | floor a ha => simp only [Term.weaken, Term.eval, ha]
  | realCompare op a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | naturalCompare op a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | and a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | or a b ha hb => simp only [Term.weaken, Term.eval, ha,hb]
  | not a ha => simp only [Term.weaken, Term.eval, ha]
  | select c a b hc ha hb => simp only [Term.weaken, Term.eval, hc,ha,hb]
  | sum values hv => simp only [Term.weaken, Term.eval, hv]
  | maximum values hv => simp only [Term.weaken, Term.eval, hv]

@[simp] theorem Term.eval_weaken_env {Γ : List ValueType} {a b : ValueType}
    (term : Term Γ a) (s : Environment (b :: Γ)) :
    term.weaken.eval s = term.eval s.2 :=
  Term.eval_weaken term s.2 s.1

end DPCut.TypedMachine
