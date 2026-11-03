import DPCut.RealMachineArrays
import DPCut.RealMachineControl
import DPCut.RealMachineSchur

set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

theorem arrayLoop_realOnly {n : ℕ} (addresses : Fin n → ℕ) (values : Fin n → Expr .real)
    (indices : List (Fin n)) : (arrayLoop addresses values indices).RealOnly := by
  induction indices with
  | nil => trivial
  | cons i indices ih => exact ⟨trivial, ih⟩

theorem arrayProgram_realOnly {n : ℕ} (addresses : Fin n → ℕ) (values : Fin n → Expr .real) :
    (arrayProgram addresses values).RealOnly := arrayLoop_realOnly _ _ _

theorem matrixMap_realOnly (n output : ℕ) (values : Fin n × Fin n → Expr .real) :
    (matrixMapProgram n output values).RealOnly := arrayProgram_realOnly _ _

theorem dotLoop_realOnly {n : ℕ} (left right : Fin n → ℕ) (output : ℕ) (indices : List (Fin n)) :
    (dotLoop left right output indices).RealOnly := by
  induction indices with
  | nil => trivial
  | cons i indices ih => exact ⟨trivial, ih⟩

theorem dotProgram_realOnly {n : ℕ} (left right : Fin n → ℕ) (output : ℕ) :
    (dotProgram left right output).RealOnly := ⟨trivial, dotLoop_realOnly _ _ _ _⟩

end DPCut.RealMachine
