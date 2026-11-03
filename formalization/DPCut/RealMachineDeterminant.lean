import DPCut.RealMachineSchur
import DPCut.MatrixFactorAlgorithm

/-! Determinants are computed by scalar pivots and Schur complements. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def determinantProgram : ℕ → ℕ → ℕ → ℕ → Code
  | 0, _, output, _ => writeReal output (.rational 1)
  | n + 1, input, output, scratch =>
      .seq (schurProgram n input scratch)
        (.seq (determinantProgram n scratch output (scratch + n * n))
          (writeReal output (.mul (readReal (matrixAddress (n := n + 1) input (0, 0))) (readReal output))))

theorem determinantProgram_steps (n input output scratch : ℕ) :
    Steps (determinantProgram n input output scratch) (100 * (n + 1) ^ 3) := by
  induction n generalizing input output scratch with
  | zero => exact (Steps.real (.natural output) (.rational 1)).mono (by norm_num [Expr.operations])
  | succ n ih =>
      have hs := schurProgram_steps n input scratch
      have hc := ih scratch output (scratch + n * n)
      have hm := Steps.real (.natural output) (.mul (readReal (matrixAddress (n := n + 1) input (0, 0))) (readReal output))
      exact (hs.seq (hc.seq hm)).mono (by simp only [Expr.operations, readReal]; nlinarith)

theorem determinantProgram_frame (tapes : Tapes) (s : State) (n input output scratch address : ℕ)
    (hout : address ≠ output) (hscratch : address < scratch) :
    ((determinantProgram n input output scratch).execute tapes s).memory.real address = s.memory.real address := by
  induction n generalizing s input scratch with
  | zero => exact writeReal_frame _ _ _ _ _ hout
  | succ n ih =>
      simp only [determinantProgram, Code.execute]
      rw [writeReal_frame _ _ _ _ _ hout]
      rw [ih _ _ _ (by omega)]
      unfold schurProgram
      exact matrixMap_below _ _ _ _ _ _ hscratch

theorem determinantProgram_value (tapes : Tapes) (s : State) (n input output scratch : ℕ)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (hout : output < scratch)
    (hdisjoint : ∀ ij : Fin n × Fin n, matrixAddress input ij ≠ output) :
    ((determinantProgram n input output scratch).execute tapes s).memory.real output =
      MatrixElimination.determinant (readMatrix n input s.memory) := by
  induction n generalizing s input scratch with
  | zero => simpa only [determinantProgram, MatrixElimination.determinant, Expr.eval, Rat.cast_one] using
      writeReal_value tapes s output (.rational 1)
  | succ n ih =>
      let first := (schurProgram n input scratch).execute tapes s
      let second := (determinantProgram n scratch output (scratch + n * n)).execute tapes first
      have hS : readMatrix n scratch first.memory = MatrixElimination.schur (readMatrix (n + 1) input s.memory) :=
        schurProgram_value _ _ _ _ _ (by intro i j; have h := hM i; unfold matrixAddress at *; omega)
      have hC : second.memory.real output = MatrixElimination.determinant (readMatrix n scratch first.memory) := by
        apply ih
        · intro ij; have h := (finProdFinEquiv ij).isLt; unfold matrixAddress; omega
        · omega
        · intro ij; unfold matrixAddress; omega
      have hmatrix : readMatrix (n + 1) input second.memory = readMatrix (n + 1) input s.memory := by
        funext i j
        change ((determinantProgram n scratch output (scratch + n * n)).execute tapes first).memory.real _ = _
        rw [determinantProgram_frame _ _ _ _ _ _ _ (hdisjoint (i, j)) (by have h := hM (i, j); omega)]
        exact matrixMap_below _ _ _ _ _ _ (hM (i, j))
      change ((writeReal output (.mul (readReal (matrixAddress (n := n + 1) input (0, 0))) (readReal output))).execute tapes second).memory.real output = _
      rw [writeReal_value]
      simp only [Expr.eval, readReal, MatrixElimination.determinant]
      rw [hC, hS]
      exact congrArg (fun x => x * MatrixElimination.determinant (MatrixElimination.schur (readMatrix (n + 1) input s.memory)))
        (congrFun (congrFun hmatrix 0) 0)

end DPCut.RealMachine
