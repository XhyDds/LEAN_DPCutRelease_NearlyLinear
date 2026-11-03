import DPCut.RealMachineSchur
import DPCut.MatrixFactorAlgorithm

/-! Recursive Cholesky is a concrete register program. The recursive call has
one public smaller dimension, and all matrix work uses scalar expression code. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def factorOutput (n input pivot child : ℕ) (ij : Fin (n + 1) × Fin (n + 1)) : Expr .real :=
  Fin.cases
    (Fin.cases (readReal pivot) (fun _ => .rational 0) ij.2)
    (fun i => Fin.cases
      (.div (readReal (matrixAddress (n := n + 1) input (0, i.succ))) (readReal pivot))
      (fun j => readReal (matrixAddress (n := n) child (i, j))) ij.2) ij.1

def factorProgram : ℕ → ℕ → ℕ → ℕ → Code
  | 0, _, _, _ => .skip
  | n + 1, input, output, scratch =>
      .seq (writeReal scratch (.sqrt (readReal (matrixAddress (n := n + 1) input (0, 0)))))
        (.seq (schurProgram n input (scratch + 1))
          (.seq (factorProgram n (scratch + 1) (scratch + 1 + n * n) (scratch + 1 + 2 * n * n))
            (matrixMapProgram (n + 1) output (factorOutput n input scratch (scratch + 1 + n * n)))))

theorem factorOutput_steps (n input pivot child : ℕ) (ij : Fin (n + 1) × Fin (n + 1)) :
    (factorOutput n input pivot child ij).operations ≤ 5 := by
  rcases ij with ⟨i, j⟩
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> norm_num [factorOutput, readReal, Expr.operations]
  · refine Fin.cases ?_ (fun j => ?_) j <;> norm_num [factorOutput, readReal, Expr.operations]

theorem factorProgram_steps (n input output scratch : ℕ) :
    Steps (factorProgram n input output scratch) (100 * (n + 1) ^ 3) := by
  induction n generalizing input output scratch with
  | zero => exact Steps.skip.mono (Nat.zero_le _)
  | succ n ih =>
      have hp : Steps (writeReal scratch (.sqrt (readReal (matrixAddress (n := n + 1) input (0, 0))))) 5 :=
        Steps.real _ _
      have hs := schurProgram_steps n input (scratch + 1)
      have hc := ih (scratch + 1) (scratch + 1 + n * n) (scratch + 1 + 2 * n * n)
      have ho := matrixMap_steps (n + 1) output 5 (factorOutput n input scratch (scratch + 1 + n * n))
        (factorOutput_steps _ _ _ _)
      exact (hp.seq (hs.seq (hc.seq ho))).mono (by nlinarith)

theorem factorProgram_below (tapes : Tapes) (s : State) (n input output scratch address : ℕ)
    (hout : address < output) (hscratch : address < scratch) :
    ((factorProgram n input output scratch).execute tapes s).memory.real address = s.memory.real address := by
  induction n generalizing s input output scratch with
  | zero => rfl
  | succ n ih =>
      simp only [factorProgram, Code.execute]
      rw [matrixMap_below _ _ _ _ _ _ hout]
      rw [ih _ _ _ _ (by omega) (by omega)]
      unfold schurProgram
      rw [matrixMap_below _ _ _ _ _ _ (by omega)]
      exact writeReal_frame _ _ _ _ _ (by omega)

theorem factorProgram_value (tapes : Tapes) (s : State) (n input output scratch : ℕ)
    (hinput : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (houtput : ∀ ij : Fin n × Fin n, matrixAddress output ij < scratch)
    (hdisjoint : ∀ i j : Fin n × Fin n, matrixAddress input i ≠ matrixAddress output j) :
    readMatrix n output ((factorProgram n input output scratch).execute tapes s).memory =
      MatrixElimination.factor (readMatrix n input s.memory) := by
  induction n generalizing s input output scratch with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
      let first := (writeReal scratch (.sqrt (readReal (matrixAddress (n := n + 1) input (0, 0))))).execute tapes s
      let second := (schurProgram n input (scratch + 1)).execute tapes first
      let third := (factorProgram n (scratch + 1) (scratch + 1 + n * n) (scratch + 1 + 2 * n * n)).execute tapes second
      have hMfirst : readMatrix (n + 1) input first.memory = readMatrix (n + 1) input s.memory := by
        funext i j
        exact writeReal_frame _ _ _ _ _ (by have h := hinput (i, j); omega)
      have hMsecond : readMatrix (n + 1) input second.memory = readMatrix (n + 1) input first.memory := by
        funext i j
        exact matrixMap_below _ _ _ _ _ _ (by have h := hinput (i, j); omega)
      have hMthird : readMatrix (n + 1) input third.memory = readMatrix (n + 1) input second.memory := by
        funext i j
        exact factorProgram_below _ _ _ _ _ _ _ (by have h := hinput (i, j); omega)
          (by have h := hinput (i, j); omega)
      have hS : readMatrix n (scratch + 1) second.memory = MatrixElimination.schur (readMatrix (n + 1) input first.memory) :=
        schurProgram_value _ _ _ _ _ (by
          intro i j
          have h := hinput i
          unfold matrixAddress at *
          omega)
      have hL : readMatrix n (scratch + 1 + n * n) third.memory =
          MatrixElimination.factor (readMatrix n (scratch + 1) second.memory) := by
        apply ih
        · intro ij
          have h := (finProdFinEquiv ij).isLt
          unfold matrixAddress
          rw [show 2 * n * n = 2 * (n * n) by ring]
          omega
        · intro ij
          have h := (finProdFinEquiv ij).isLt
          unfold matrixAddress
          rw [show 2 * n * n = 2 * (n * n) by ring]
          omega
        · intro i j
          have hi := (finProdFinEquiv i).isLt
          have hj := (finProdFinEquiv j).isLt
          unfold matrixAddress
          omega
      have hpivot : third.memory.real scratch = Real.sqrt ((readMatrix (n + 1) input s.memory) 0 0) := by
        have ht : third.memory.real scratch = second.memory.real scratch :=
          factorProgram_below _ _ _ _ _ _ _ (by omega) (by omega)
        have hs : second.memory.real scratch = first.memory.real scratch :=
          matrixMap_below _ _ _ _ _ _ (by omega)
        rw [ht, hs]
        change ((writeReal scratch (.sqrt (readReal (matrixAddress (n := n + 1) input (0, 0))))).execute tapes s).memory.real scratch = _
        rw [writeReal_value]
        rfl
      have hframe : ∀ i j : Fin (n + 1) × Fin (n + 1),
          (factorOutput n input scratch (scratch + 1 + n * n) i).RealFrame (matrixAddress output j) := by
        intro i j
        have ho := houtput j
        rcases i with ⟨a, b⟩
        refine Fin.cases ?_ (fun a => ?_) a
        · refine Fin.cases ?_ (fun b => ?_) b
          · exact realFrame_read _ _ (by omega)
          · exact realFrame_rational 0 _
        · refine Fin.cases ?_ (fun b => ?_) b
          · exact realFrame_div (realFrame_read _ _ (hdisjoint (0, a.succ) j)) (realFrame_read _ _ (by omega))
          · apply realFrame_read
            unfold matrixAddress at *
            omega
      have hv := matrixMap_value tapes third (n + 1) output
        (factorOutput n input scratch (scratch + 1 + n * n)) hframe
      change readMatrix (n + 1) output ((matrixMapProgram (n + 1) output
        (factorOutput n input scratch (scratch + 1 + n * n))).execute tapes third).memory = _
      funext i j
      rw [hv]
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simpa only [factorOutput, Expr.eval, readReal, MatrixElimination.factor,
            Fin.cases_zero, Fin.cases_succ, MatrixElimination.lowerBlock_zero_zero] using hpivot
        · simp [factorOutput, Expr.eval, readReal, MatrixElimination.factor]
      · refine Fin.cases ?_ (fun j => ?_) j
        · have hrow := congrFun (congrFun (hMthird.trans (hMsecond.trans hMfirst)) 0) i.succ
          simp only [factorOutput, Expr.eval, readReal, MatrixElimination.factor,
            Fin.cases_zero, Fin.cases_succ, MatrixElimination.lowerBlock_succ_zero]
          rw [hpivot]
          exact congrArg (fun x => x / Real.sqrt ((readMatrix (n + 1) input s.memory) 0 0)) hrow
        · have htail := congrFun (congrFun hL i) j
          rw [hS, hMfirst] at htail
          simpa only [factorOutput, Expr.eval, readReal, MatrixElimination.factor,
            Fin.cases_zero, Fin.cases_succ, MatrixElimination.lowerBlock_succ_succ] using htail

end DPCut.RealMachine
