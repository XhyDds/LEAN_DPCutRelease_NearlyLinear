import DPCut.RealMachineMeasurable

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory

namespace DPCut.RealMachine

def Tapes.zero : Tapes := ⟨fun _ => 0,fun _ => 0⟩

@[fun_prop] theorem measurable_tick (amount : ℕ) : Measurable (fun s : State => s.tick amount) := by
  apply measurable_state
  · exact measurable_state_memory
  · exact measurable_state_normalIndex
  · exact measurable_state_laplaceIndex
  · exact measurable_state_operations.add_const _

@[fun_prop] theorem Code.measurable_execute (code : Code) (tapes : Tapes) :
    Measurable (fun s => code.execute tapes s) := by
  induction code with
  | skip => exact measurable_id
  | real address value =>
      apply measurable_state
      · exact measurable_writeReal.comp (measurable_state_memory.prodMk
          ((address.measurable_eval.comp measurable_state_memory).prodMk
            (value.measurable_eval.comp measurable_state_memory)))
      · exact measurable_state_normalIndex
      · exact measurable_state_laplaceIndex
      · exact ((measurable_state_operations.add_const _).add_const _).add_const _
  | natural address value =>
      apply measurable_state
      · exact measurable_writeNatural.comp (measurable_state_memory.prodMk
          ((address.measurable_eval.comp measurable_state_memory).prodMk
            (value.measurable_eval.comp measurable_state_memory)))
      · exact measurable_state_normalIndex
      · exact measurable_state_laplaceIndex
      · exact ((measurable_state_operations.add_const _).add_const _).add_const _
  | boolean address value =>
      apply measurable_state
      · exact measurable_writeBoolean.comp (measurable_state_memory.prodMk
          ((address.measurable_eval.comp measurable_state_memory).prodMk
            (value.measurable_eval.comp measurable_state_memory)))
      · exact measurable_state_normalIndex
      · exact measurable_state_laplaceIndex
      · exact ((measurable_state_operations.add_const _).add_const _).add_const _
  | normal address =>
      apply measurable_state
      · exact measurable_writeReal.comp (measurable_state_memory.prodMk
          ((address.measurable_eval.comp measurable_state_memory).prodMk
            ((measurable_of_countable tapes.normal).comp measurable_state_normalIndex)))
      · exact measurable_state_normalIndex.add_const _
      · exact measurable_state_laplaceIndex
      · exact (measurable_state_operations.add_const _).add_const _
  | laplace address =>
      apply measurable_state
      · exact measurable_writeReal.comp (measurable_state_memory.prodMk
          ((address.measurable_eval.comp measurable_state_memory).prodMk
            ((measurable_of_countable tapes.laplace).comp measurable_state_laplaceIndex)))
      · exact measurable_state_normalIndex
      · exact measurable_state_laplaceIndex.add_const _
      · exact (measurable_state_operations.add_const _).add_const _
  | seq first next hf hn => exact hn.comp hf
  | branch condition yes no hy hn =>
      exact Measurable.ite ((condition.measurable_eval.comp measurable_state_memory) (measurableSet_singleton true))
        (hy.comp (measurable_tick _)) (hn.comp (measurable_tick _))
  | loop count index body ih =>
      have hstep (i : ℕ) : Measurable (fun s : State => body.execute tapes
          { s with memory := s.memory.writeNatural index i, operations := s.operations + 2 }) := by
        apply ih.comp
        apply measurable_state
        · exact measurable_writeNatural.comp
            (measurable_state_memory.prodMk (measurable_const.prodMk measurable_const))
        · exact measurable_state_normalIndex
        · exact measurable_state_laplaceIndex
        · exact measurable_state_operations.add_const _
      have hfold (indices : List ℕ) : Measurable (fun s : State => indices.foldl
          (fun old i => body.execute tapes { old with
            memory := old.memory.writeNatural index i, operations := old.operations + 2 }) s) := by
        induction indices with
        | nil => exact measurable_id
        | cons i indices hi => exact hi.comp (hstep i)
      have hchoose : Measurable (fun p : ℕ × State => (List.range p.1).foldl
          (fun old i => body.execute tapes { old with
            memory := old.memory.writeNatural index i, operations := old.operations + 2 }) p.2) :=
        measurable_from_prod_countable_right (fun i => hfold (List.range i))
      exact hchoose.comp ((count.measurable_eval.comp measurable_state_memory).prodMk (measurable_tick _))

def Code.NoSamples : Code → Prop
  | .normal .. | .laplace .. => False
  | .seq first next => first.NoSamples ∧ next.NoSamples
  | .branch _ yes no => yes.NoSamples ∧ no.NoSamples
  | .loop _ _ body => body.NoSamples
  | _ => True

theorem Code.noSamples_execute (code : Code) (h : code.NoSamples) (a b : Tapes) (s : State) :
    code.execute a s = code.execute b s := by
  induction code generalizing s with
  | skip | real | natural | boolean => rfl
  | normal | laplace => cases h
  | seq first next hf hn =>
      change next.execute a (first.execute a s) = next.execute b (first.execute b s)
      rw [hf h.1]
      exact hn h.2 _
  | branch condition yes no hy hn =>
      simp only [Code.execute]
      split
      · exact hy h.1 _
      · exact hn h.2 _
  | loop count index body ih =>
      have hfold (indices : List ℕ) (initial : State) :
          indices.foldl (fun old i => body.execute a { old with
              memory := old.memory.writeNatural index i, operations := old.operations + 2 }) initial =
            indices.foldl (fun old i => body.execute b { old with
              memory := old.memory.writeNatural index i, operations := old.operations + 2 }) initial := by
        induction indices generalizing initial with
        | nil => rfl
        | cons i indices hi =>
            simp only [List.foldl_cons]
            rw [ih h]
            exact hi _
      exact hfold _ _

end DPCut.RealMachine
