import DPCut.RealMachineBounds

set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

def writeNatural (address : ℕ) (value : Expr .natural) : Code := .natural (.natural address) value
def writeBoolean (address : ℕ) (value : Expr .boolean) : Code := .boolean (.natural address) value

theorem writeNatural_value (tapes : Tapes) (s : State) (address : ℕ) (value : Expr .natural) :
    ((writeNatural address value).execute tapes s).memory.natural address = value.eval s.memory := by
  simp [writeNatural, Code.execute, Expr.eval, Memory.writeNatural]

theorem writeBoolean_value (tapes : Tapes) (s : State) (address : ℕ) (value : Expr .boolean) :
    ((writeBoolean address value).execute tapes s).memory.boolean address = value.eval s.memory := by
  simp [writeBoolean, Code.execute, Expr.eval, Memory.writeBoolean]

def Code.ControlOnly : Code → Prop
  | .skip => True
  | .natural .. | .boolean .. => True
  | .seq first next => first.ControlOnly ∧ next.ControlOnly
  | .branch _ yes no => yes.ControlOnly ∧ no.ControlOnly
  | .loop _ _ body => body.ControlOnly
  | _ => False

theorem Code.controlOnly_real (code : Code) (h : code.ControlOnly) (tapes : Tapes) (s : State) :
    (code.execute tapes s).memory.real = s.memory.real := by
  induction code generalizing s with
  | skip => rfl
  | real | normal | laplace => cases h
  | natural => rfl
  | boolean => rfl
  | seq first next ih₁ ih₂ =>
      change (next.execute tapes (first.execute tapes s)).memory.real = _
      rw [ih₂ h.2, ih₁ h.1]
  | branch condition yes no ih₁ ih₂ =>
      simp only [Code.execute]
      split
      · exact ih₁ h.1 (s.tick (condition.operations + 1))
      · exact ih₂ h.2 (s.tick (condition.operations + 1))
  | loop count index body ih =>
      have hf (indices : List ℕ) (old : State) :
          (indices.foldl (fun state i => body.execute tapes
            { state with
              memory := state.memory.writeNatural index i
              operations := state.operations + 2 }) old).memory.real = old.memory.real := by
        induction indices generalizing old with
        | nil => rfl
        | cons i indices ih' =>
            rw [List.foldl_cons, ih']
            exact ih h _
      exact hf _ _

def Code.RealOnly : Code → Prop
  | .skip | .real .. => True
  | .seq first next => first.RealOnly ∧ next.RealOnly
  | .branch _ yes no => yes.RealOnly ∧ no.RealOnly
  | _ => False

theorem Code.realOnly_control (code : Code) (h : code.RealOnly) (tapes : Tapes) (s : State) :
    (code.execute tapes s).memory.natural = s.memory.natural ∧
      (code.execute tapes s).memory.boolean = s.memory.boolean := by
  induction code generalizing s with
  | skip | real => exact ⟨rfl, rfl⟩
  | natural | boolean | normal | laplace | loop => cases h
  | seq first next ih₁ ih₂ =>
      have hf := ih₁ h.1 s
      have hn := ih₂ h.2 (first.execute tapes s)
      exact ⟨hn.1.trans hf.1, hn.2.trans hf.2⟩
  | branch condition yes no ih₁ ih₂ =>
      simp only [Code.execute]
      split
      · exact ih₁ h.1 _
      · exact ih₂ h.2 _

end DPCut.RealMachine
