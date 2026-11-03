import DPCut.RealMachineArrays
import DPCut.RealMachineMatrices
import DPCut.MatrixPSDAlgorithm

/-! The Schur-complement array computation as a literal real-machine program. -/
set_option autoImplicit false
noncomputable section

namespace DPCut.RealMachine

variable {n : ℕ}

def matrixMapProgram (n output : ℕ) (values : Fin n × Fin n → Expr .real) : Code :=
  arrayProgram (fun i : Fin (n * n) => matrixAddress output (finProdFinEquiv.symm i))
    (fun i => values (finProdFinEquiv.symm i))

theorem matrixMap_steps (n output c : ℕ) (values : Fin n × Fin n → Expr .real)
    (h : ∀ i, (values i).operations ≤ c) :
    Steps (matrixMapProgram n output values) (n * n * (c + 2)) :=
  arrayProgram_steps _ _ _ (fun i => h (finProdFinEquiv.symm i))

theorem matrixMap_value (tapes : Tapes) (s : State) (n output : ℕ)
    (values : Fin n × Fin n → Expr .real)
    (h : ∀ i j : Fin n × Fin n, (values i).RealFrame (matrixAddress output j)) :
    ∀ i j : Fin n,
      (readMatrix n output ((matrixMapProgram n output values).execute tapes s).memory) i j =
        (values (i, j)).eval s.memory := by
  intro i j
  have hi : Function.Injective (fun k : Fin (n * n) => matrixAddress output (finProdFinEquiv.symm k)) :=
    (matrixAddress_injective output).comp finProdFinEquiv.symm.injective
  have hv := arrayProgram_value tapes s
    (fun k : Fin (n * n) => matrixAddress output (finProdFinEquiv.symm k))
    (fun k => values (finProdFinEquiv.symm k)) hi
    (fun a b => h (finProdFinEquiv.symm a) (finProdFinEquiv.symm b))
    (finProdFinEquiv (i, j))
  simpa only [finProdFinEquiv.symm_apply_apply, matrixMapProgram, readMatrix] using hv

theorem matrixMap_frame (tapes : Tapes) (s : State) (n output address : ℕ)
    (values : Fin n × Fin n → Expr .real) (h : ∀ ij : Fin n × Fin n, address ≠ matrixAddress output ij) :
    ((matrixMapProgram n output values).execute tapes s).memory.real address = s.memory.real address :=
  arrayLoop_frame _ _ _ _ _ _ (fun i _ => h (finProdFinEquiv.symm i))

theorem matrixMap_below (tapes : Tapes) (s : State) (n output address : ℕ)
    (values : Fin n × Fin n → Expr .real) (h : address < output) :
    ((matrixMapProgram n output values).execute tapes s).memory.real address = s.memory.real address := by
  apply matrixMap_frame _ _ _ _ _ _
  intro ij
  unfold matrixAddress
  omega

def schurExpr (input : ℕ) (i j : Fin n) : Expr .real :=
  .sub (readReal (matrixAddress (n := n + 1) input (i.succ, j.succ)))
    (.div (.mul (readReal (matrixAddress (n := n + 1) input (0, i.succ)))
      (readReal (matrixAddress (n := n + 1) input (0, j.succ))))
      (readReal (matrixAddress (n := n + 1) input (0, 0))))

def schurProgram (n input output : ℕ) : Code :=
  matrixMapProgram n output (fun ij => schurExpr input ij.1 ij.2)

theorem schurProgram_steps (n input output : ℕ) :
    Steps (schurProgram n input output) (13 * n * n) := by
  have h := matrixMap_steps n output 11 (fun ij => schurExpr input ij.1 ij.2) (by intro ij; rfl)
  simpa only [schurProgram, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem schurProgram_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ i : Fin (n + 1) × Fin (n + 1), ∀ j : Fin n × Fin n,
      matrixAddress input i ≠ matrixAddress output j) :
    readMatrix n output ((schurProgram n input output).execute tapes s).memory =
      DPCut.MatrixElimination.schur (readMatrix (n + 1) input s.memory) := by
  have hframe : ∀ i j : Fin n × Fin n,
      (schurExpr input i.1 i.2).RealFrame (matrixAddress output j) := by
    intro i j
    apply realFrame_sub (realFrame_read _ _ (h (i.1.succ, i.2.succ) j))
    apply realFrame_div
    · exact realFrame_mul (realFrame_read _ _ (h (0, i.1.succ) j))
        (realFrame_read _ _ (h (0, i.2.succ) j))
    · exact realFrame_read _ _ (h (0, 0) j)
  funext i j
  have hv := matrixMap_value tapes s n output (fun ij => schurExpr input ij.1 ij.2) hframe i j
  exact hv.trans (by
    simp only [schurExpr, Expr.eval, readReal, readMatrix, MatrixElimination.schur,
      MatrixElimination.tail, MatrixElimination.row])

end DPCut.RealMachine
