import DPCut.RealMachineBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory

namespace DPCut.RealMachine

instance (priority := low) (sort : RegisterType) : MeasurableSpace sort.Value :=
  match sort with
  | .real => inferInstance
  | .natural => inferInstance
  | .boolean => inferInstance

instance : MeasurableSpace Memory :=
  .comap (fun s : Memory => (s.real,s.natural,s.boolean)) inferInstance

instance : MeasurableSpace State :=
  .comap (fun s : State => (s.memory,s.normalIndex,s.laplaceIndex,s.operations)) inferInstance

@[fun_prop] theorem measurable_memory_real : Measurable Memory.real :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] theorem measurable_memory_natural : Measurable Memory.natural :=
  (measurable_fst.comp measurable_snd).comp (comap_measurable _)

@[fun_prop] theorem measurable_memory_boolean : Measurable Memory.boolean :=
  (measurable_snd.comp measurable_snd).comp (comap_measurable _)

@[fun_prop] theorem measurable_state_memory : Measurable State.memory :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] theorem measurable_state_normalIndex : Measurable State.normalIndex :=
  (measurable_fst.comp measurable_snd).comp (comap_measurable _)

@[fun_prop] theorem measurable_state_laplaceIndex : Measurable State.laplaceIndex :=
  ((measurable_fst.comp measurable_snd).comp measurable_snd).comp (comap_measurable _)

@[fun_prop] theorem measurable_state_operations : Measurable State.operations :=
  ((measurable_snd.comp measurable_snd).comp measurable_snd).comp (comap_measurable _)

theorem measurable_memory {α : Type*} [MeasurableSpace α] (f : α → Memory)
    (hr : Measurable (fun x => (f x).real)) (hn : Measurable (fun x => (f x).natural))
    (hb : Measurable (fun x => (f x).boolean)) : Measurable f := by
  apply Measurable.of_comap_le
  change (MeasurableSpace.comap (fun s : Memory => (s.real,s.natural,s.boolean)) inferInstance).comap f ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (hr.prodMk (hn.prodMk hb)).comap_le

theorem measurable_state {α : Type*} [MeasurableSpace α] (f : α → State)
    (hm : Measurable (fun x => (f x).memory)) (hn : Measurable (fun x => (f x).normalIndex))
    (hl : Measurable (fun x => (f x).laplaceIndex)) (ho : Measurable (fun x => (f x).operations)) :
    Measurable f := by
  apply Measurable.of_comap_le
  change (MeasurableSpace.comap (fun s : State => (s.memory,s.normalIndex,s.laplaceIndex,s.operations)) inferInstance).comap f ≤ _
  rw [MeasurableSpace.comap_comp]
  exact (hm.prodMk (hn.prodMk (hl.prodMk ho))).comap_le

theorem measurable_eval_nat {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → ℕ → β} {i : α → ℕ} (hf : Measurable f) (hi : Measurable i) :
    Measurable (fun x => f x (i x)) := by
  have he : Measurable (fun p : (ℕ → β) × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left (fun k : ℕ => measurable_pi_apply k)
  exact he.comp (hf.prodMk hi)

theorem measurable_decision {α : Type*} [MeasurableSpace α] (P : α → Prop)
    [DecidablePred P] (h : MeasurableSet {x | P x}) : Measurable (fun x => decide (P x)) := by
  convert (Measurable.ite h (measurable_const (a := true)) (measurable_const (a := false))) using 1

@[fun_prop] theorem measurable_writeReal :
    Measurable (fun p : Memory × ℕ × ℝ => p.1.writeReal p.2.1 p.2.2) := by
  apply measurable_memory
  · apply measurable_pi_lambda
    intro i
    simp only [Memory.writeReal, Function.update_apply]
    exact Measurable.ite (measurableSet_eq_fun_of_countable measurable_const (measurable_fst.comp measurable_snd))
      (measurable_snd.comp measurable_snd) ((measurable_pi_apply i).comp (measurable_memory_real.comp measurable_fst))
  · simpa only [Memory.writeReal] using measurable_memory_natural.comp measurable_fst
  · simpa only [Memory.writeReal] using measurable_memory_boolean.comp measurable_fst

@[fun_prop] theorem measurable_writeNatural :
    Measurable (fun p : Memory × ℕ × ℕ => p.1.writeNatural p.2.1 p.2.2) := by
  apply measurable_memory
  · simpa only [Memory.writeNatural] using measurable_memory_real.comp measurable_fst
  · apply measurable_pi_lambda
    intro i
    simp only [Memory.writeNatural, Function.update_apply]
    exact Measurable.ite (measurableSet_eq_fun_of_countable measurable_const (measurable_fst.comp measurable_snd))
      (measurable_snd.comp measurable_snd) ((measurable_pi_apply i).comp (measurable_memory_natural.comp measurable_fst))
  · simpa only [Memory.writeNatural] using measurable_memory_boolean.comp measurable_fst

@[fun_prop] theorem measurable_writeBoolean :
    Measurable (fun p : Memory × ℕ × Bool => p.1.writeBoolean p.2.1 p.2.2) := by
  apply measurable_memory
  · simpa only [Memory.writeBoolean] using measurable_memory_real.comp measurable_fst
  · simpa only [Memory.writeBoolean] using measurable_memory_natural.comp measurable_fst
  · apply measurable_pi_lambda
    intro i
    simp only [Memory.writeBoolean, Function.update_apply]
    exact Measurable.ite (measurableSet_eq_fun_of_countable measurable_const (measurable_fst.comp measurable_snd))
      (measurable_snd.comp measurable_snd) ((measurable_pi_apply i).comp (measurable_memory_boolean.comp measurable_fst))

@[fun_prop] theorem Expr.measurable_eval {sort : RegisterType} (e : Expr sort) :
    Measurable (fun s : Memory => e.eval s) := by
  induction e with
  | rational q => exact measurable_const
  | natural n => exact measurable_const
  | boolean b => exact measurable_const
  | readReal address ih => exact measurable_eval_nat measurable_memory_real ih
  | readNatural address ih => exact measurable_eval_nat measurable_memory_natural ih
  | readBoolean address ih => exact measurable_eval_nat measurable_memory_boolean ih
  | cast value ih => exact (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp ih
  | ceil value ih => exact Nat.measurable_ceil.comp ih
  | floor value ih => exact Nat.measurable_floor.comp ih
  | natAdd a b ha hb => exact (measurable_of_countable (fun p : ℕ × ℕ => p.1+p.2)).comp (ha.prodMk hb)
  | natSub a b ha hb => exact (measurable_of_countable (fun p : ℕ × ℕ => p.1-p.2)).comp (ha.prodMk hb)
  | natMul a b ha hb => exact (measurable_of_countable (fun p : ℕ × ℕ => p.1*p.2)).comp (ha.prodMk hb)
  | natDiv a b ha hb => exact (measurable_of_countable (fun p : ℕ × ℕ => p.1/p.2)).comp (ha.prodMk hb)
  | add a b ha hb => exact ha.add hb
  | sub a b ha hb => exact ha.sub hb
  | mul a b ha hb => exact ha.mul hb
  | div a b ha hb => exact ha.div hb
  | neg value ih => exact ih.neg
  | sqrt value ih => exact ih.sqrt
  | log value ih => exact ih.log
  | exp value ih => exact ih.exp
  | select c a b hc ha hb =>
      exact Measurable.ite (hc (measurableSet_singleton true)) ha hb
  | le a b ha hb => exact measurable_decision _ (measurableSet_le ha hb)
  | lt a b ha hb => exact measurable_decision _ (measurableSet_lt ha hb)
  | eq a b ha hb => exact measurable_decision _ (measurableSet_eq_fun ha hb)
  | natLe a b ha hb => exact measurable_decision _ (measurableSet_le ha hb)
  | natLt a b ha hb => exact measurable_decision _ (measurableSet_lt ha hb)
  | natEq a b ha hb => exact measurable_decision _ (measurableSet_eq_fun_of_countable ha hb)
  | and a b ha hb => exact (measurable_of_countable (fun p : Bool × Bool => p.1 && p.2)).comp (ha.prodMk hb)
  | or a b ha hb => exact (measurable_of_countable (fun p : Bool × Bool => p.1 || p.2)).comp (ha.prodMk hb)
  | not a ha => exact (measurable_of_countable (fun b : Bool => !b)).comp ha

end DPCut.RealMachine
