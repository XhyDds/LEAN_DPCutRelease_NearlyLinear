import DPCut.RealMachineFactor
import DPCut.RealMachineExecutionMeasurable

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open MeasureTheory

namespace DPCut.RealMachine

def matrixMemory (n : ℕ) (X : DPCut.Mat n) : Memory :=
  ⟨fun address => ∑ ij : Fin n × Fin n, if address = matrixAddress 0 ij then X ij.1 ij.2 else 0,
    fun _ => 0,fun _ => false⟩

def factorInput (n : ℕ) (X : DPCut.Mat n) : State := ⟨matrixMemory n X,0,0,0⟩

def factorCode (n : ℕ) : Code := factorProgram n 0 (n*n) (2*n*n)

def factorValue (n : ℕ) (X : DPCut.Mat n) : DPCut.Mat n :=
  readMatrix n (n*n) ((factorCode n).execute Tapes.zero (factorInput n X)).memory

def factorOperations (n : ℕ) (X : DPCut.Mat n) : ℕ :=
  ((factorCode n).execute Tapes.zero (factorInput n X)).operations

theorem matrixMemory_value (n : ℕ) (X : DPCut.Mat n) : readMatrix n 0 (matrixMemory n X) = X := by
  funext i j
  change (∑ ij : Fin n × Fin n, if matrixAddress 0 (i,j) = matrixAddress 0 ij then X ij.1 ij.2 else 0) = X i j
  simp [(matrixAddress_injective 0).eq_iff]

theorem factorValue_eq (n : ℕ) (X : DPCut.Mat n) : factorValue n X = MatrixElimination.factor X := by
  conv_rhs => rw [← matrixMemory_value n X]
  exact factorProgram_value Tapes.zero (factorInput n X) n 0 (n*n) (2*n*n)
    (by
      intro ij
      have h := (finProdFinEquiv ij).isLt
      unfold matrixAddress
      ring_nf at h ⊢
      omega)
    (by
      intro ij
      have h := (finProdFinEquiv ij).isLt
      unfold matrixAddress
      ring_nf at h ⊢
      omega)
    (by
      intro ij kl
      have h := (finProdFinEquiv ij).isLt
      unfold matrixAddress
      omega)

theorem factorOperations_le (n : ℕ) (X : DPCut.Mat n) : factorOperations n X ≤ 100*(n+1)^3 := by
  simpa only [factorOperations, factorCode, factorInput, Nat.zero_add] using
    factorProgram_steps n 0 (n*n) (2*n*n) Tapes.zero (factorInput n X)

@[fun_prop] theorem measurable_factorInput (n : ℕ) : Measurable (factorInput n) := by
  apply measurable_state
  · apply measurable_memory
    · apply measurable_pi_lambda
      intro address
      apply Finset.measurable_sum
      intro ij _
      split_ifs
      · exact (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
      · exact measurable_const
    · exact measurable_const
    · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const

@[fun_prop] theorem measurable_readMatrix (n base : ℕ) :
    Measurable (fun s : State => readMatrix n base s.memory) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (matrixAddress base (i,j))).comp
    (measurable_memory_real.comp measurable_state_memory)

@[fun_prop] theorem measurable_factorValue (n : ℕ) : Measurable (factorValue n) :=
  (measurable_readMatrix n (n*n)).comp
    ((Code.measurable_execute (factorCode n) Tapes.zero).comp (measurable_factorInput n))

@[fun_prop] theorem measurable_factorOperations (n : ℕ) : Measurable (factorOperations n) :=
  measurable_state_operations.comp
    ((Code.measurable_execute (factorCode n) Tapes.zero).comp (measurable_factorInput n))

end DPCut.RealMachine
