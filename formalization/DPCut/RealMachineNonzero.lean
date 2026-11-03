import DPCut.RealMachineControl
import DPCut.MatrixElimination

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def firstNonzeroProgram : {n : ℕ} → (Fin n → ℕ) → ℕ → ℕ → Code
  | 0, _, flag, index =>
      .seq (writeBoolean flag (.boolean false)) (writeNatural index (.natural 0))
  | n + 1, addresses, flag, index =>
      .branch (.eq (readReal (addresses 0)) (.rational 0))
        (.seq (firstNonzeroProgram (fun i : Fin n => addresses i.succ) flag index)
          (writeNatural index (.natAdd (readNatural index) (.natural 1))))
        (.seq (writeBoolean flag (.boolean true)) (writeNatural index (.natural 0)))

theorem firstNonzero_control {n : ℕ} (addresses : Fin n → ℕ) (flag index : ℕ) :
    (firstNonzeroProgram addresses flag index).ControlOnly := by
  induction n with
  | zero => exact ⟨trivial, trivial⟩
  | succ n ih => exact ⟨⟨ih _, trivial⟩, ⟨trivial, trivial⟩⟩

theorem firstNonzeroProgram_steps {n : ℕ} (addresses : Fin n → ℕ) (flag index : ℕ) :
    Steps (firstNonzeroProgram addresses flag index) (20 * (n + 1)) := by
  induction n with
  | zero =>
      exact ((Steps.boolean (.natural flag) (.boolean false)).seq
        (Steps.natural (.natural index) (.natural 0))).mono (by norm_num [Expr.operations])
  | succ n ih =>
      have hy := (ih (fun i => addresses i.succ)).seq
        (Steps.natural (.natural index) (.natAdd (readNatural index) (.natural 1)))
      have hn := (Steps.boolean (.natural flag) (.boolean true)).seq
        (Steps.natural (.natural index) (.natural 0))
      exact (Steps.branch _ hy hn).mono (by simp only [Expr.operations, readReal, readNatural]; omega)

def nonzeroEncoding {n : ℕ} : Option (Fin n) → Bool × ℕ
  | none => (false, n)
  | some i => (true, i.val)

theorem firstNonzeroProgram_value (tapes : Tapes) (s : State) {n : ℕ}
    (addresses : Fin n → ℕ) (flag index : ℕ) :
    let result := (firstNonzeroProgram addresses flag index).execute tapes s
    (result.memory.boolean flag, result.memory.natural index) =
      nonzeroEncoding (MatrixElimination.firstNonzero (fun i => s.memory.real (addresses i))) := by
  induction n generalizing s with
  | zero =>
      simp [firstNonzeroProgram, writeBoolean, writeNatural, Code.execute, Expr.eval,
        Memory.writeBoolean, Memory.writeNatural, MatrixElimination.firstNonzero, nonzeroEncoding]
  | succ n ih =>
      by_cases hz : s.memory.real (addresses 0) = 0
      · let first := (firstNonzeroProgram (fun i : Fin n => addresses i.succ) flag index).execute tapes
          (s.tick ((Expr.eq (readReal (addresses 0)) (.rational 0)).operations + 1))
        have he := ih (s.tick ((Expr.eq (readReal (addresses 0)) (.rational 0)).operations + 1))
          (fun i : Fin n => addresses i.succ)
        change (first.memory.boolean flag, first.memory.natural index) =
          nonzeroEncoding (MatrixElimination.firstNonzero (fun i : Fin n => s.memory.real (addresses i.succ))) at he
        have hstep :
            let result := (firstNonzeroProgram addresses flag index).execute tapes s
            (result.memory.boolean flag, result.memory.natural index) =
              (first.memory.boolean flag, first.memory.natural index + 1) := by
          simp [firstNonzeroProgram, Code.execute, readReal, readNatural, Expr.eval,
            Rat.cast_zero, hz, writeNatural, Memory.writeNatural, first]
        dsimp only at hstep ⊢
        rw [hstep]
        cases hv : MatrixElimination.firstNonzero (fun i : Fin n => s.memory.real (addresses i.succ)) with
        | none =>
            have h := congrArg (fun pair : Bool × ℕ => (pair.1, pair.2 + 1)) he
            simpa [MatrixElimination.firstNonzero, hz, hv, nonzeroEncoding] using h
        | some i =>
            have h := congrArg (fun pair : Bool × ℕ => (pair.1, pair.2 + 1)) he
            simpa [MatrixElimination.firstNonzero, hz, hv, nonzeroEncoding] using h
      · simp [firstNonzeroProgram, Code.execute, readReal, readNatural, Expr.eval, hz,
          writeBoolean, writeNatural, Memory.writeBoolean, Memory.writeNatural,
          MatrixElimination.firstNonzero, nonzeroEncoding]

end DPCut.RealMachine
