import DPCut.RealMachinePSDSpecial
import DPCut.MatrixPSDAlgorithm

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
open Matrix

namespace DPCut.RealMachine

theorem preparePSD_frame (tapes : Tapes) (s : State) (n input matrix address : ℕ)
    (h : address < matrix) :
    ((preparePSDProgram n input matrix).execute tapes s).memory.real address = s.memory.real address := by
  simp only [preparePSDProgram, Code.execute]
  split
  · exact tailProgram_frame _ _ _ _ _ _ h
  · exact matrixMap_below _ _ _ _ _ _ h

theorem preparePSD_value (tapes : Tapes) (s : State) (n input matrix : ℕ)
    (h : ∀ i : Fin (n + 1) × Fin (n + 1), ∀ j : Fin n × Fin n,
      matrixAddress input i ≠ matrixAddress matrix j) :
    readMatrix n matrix ((preparePSDProgram n input matrix).execute tapes s).memory =
      if (readMatrix (n + 1) input s.memory) 0 0 = 0
      then MatrixElimination.tail (readMatrix (n + 1) input s.memory)
      else MatrixElimination.schur (readMatrix (n + 1) input s.memory) := by
  by_cases hz : (readMatrix (n + 1) input s.memory) 0 0 = 0
  · have hc : (Expr.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)).eval s.memory = true := by
      simpa [Expr.eval, readReal, readMatrix] using hz
    simp only [preparePSDProgram, Code.execute, hc, Bool.true_eq, ite_true, if_pos hz]
    exact tailProgram_value _ _ _ _ _ h
  · have hc : (Expr.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)).eval s.memory = false := by
      simpa [Expr.eval, readReal, readMatrix] using hz
    simp only [preparePSDProgram, Code.execute, hc, Bool.false_eq_true, ite_false, if_neg hz]
    exact schurProgram_value _ _ _ _ _ h

theorem psdProgram_frame (tapes : Tapes) (s : State) (n input output flag scratch address : ℕ)
    (hout : address < output) (hscratch : address < scratch) :
    ((psdProgram n input output flag scratch).execute tapes s).memory.real address = s.memory.real address := by
  induction n generalizing s input output scratch with
  | zero => rfl
  | succ n ih =>
      simp only [psdProgram, Code.execute]
      split
      · unfold negativePSDProgram
        simp only [Code.execute]
        unfold arrayProgram
        rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)]
        rfl
      · split
        · unfold specialPSDProgram
          simp only [Code.execute]
          unfold arrayProgram
          rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)]
          change ((writeReal (scratch + 1) (specialPivotExpr n input scratch)).execute tapes _).memory.real address = _
          rw [writeReal_frame _ _ _ _ _ (by omega)]
          exact congrFun (Code.controlOnly_real _ (firstNonzero_control _ _ _) tapes _) address
        · rw [liftPSD_frame tapes _ n input output flag (scratch + 1) (scratch + 2 + n * n) address
            (by omega) (by intro i; unfold vectorAddress; omega)]
          rw [ih _ _ _ _ (by omega) (by omega)]
          rw [preparePSD_frame _ _ _ _ _ _ (by omega)]
          exact congrFun (Code.controlOnly_real _ (firstNonzero_control _ _ _) tapes _) address

theorem psdProgram_value (tapes : Tapes) (s : State) (n input output flag scratch : ℕ)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (ho : ∀ i : Fin n, vectorAddress output i < scratch)
    (hdisjoint : ∀ ij : Fin n × Fin n, ∀ i : Fin n, matrixAddress input ij ≠ vectorAddress output i) :
    psdResult n output flag ((psdProgram n input output flag scratch).execute tapes s) =
      MatrixElimination.psdWitness (readMatrix n input s.memory) := by
  induction n generalizing s input output scratch with
  | zero => simp [psdProgram, psdResult, MatrixElimination.psdWitness, writeBoolean,
      Code.execute, Memory.writeBoolean, Expr.eval]
  | succ n ih =>
      let M := readMatrix (n + 1) input s.memory
      let condition := Expr.lt (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)
      change psdResult (n + 1) output flag ((psdProgram (n + 1) input output flag scratch).execute tapes s) =
        MatrixElimination.psdWitness M
      by_cases hnegative : M 0 0 < 0
      · have hc : condition.eval s.memory = true := by simpa [condition, Expr.eval, readReal, M, readMatrix] using hnegative
        dsimp only [condition] at hc
        simp only [psdProgram, Code.execute, hc, Bool.true_eq, ite_true,
          MatrixElimination.psdWitness, hnegative, dite_true, if_pos hnegative]
        exact negativePSD_result _ _ _ _ _
      · let first := (firstNonzeroProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ)) scratch scratch).execute tapes
          (s.tick (condition.operations + 1))
        let test := Expr.and (.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0))
          (readBoolean scratch)
        let second := first.tick (test.operations + 1)
        let third := (preparePSDProgram n input (scratch + 2)).execute tapes second
        let fourth := (psdProgram n (scratch + 2) (scratch + 2 + n * n) flag (scratch + 2 + n * n + n)).execute tapes third
        have hc : condition.eval s.memory = false := by simpa [condition, Expr.eval, readReal, M, readMatrix] using hnegative
        dsimp only [condition] at hc
        have hscan := firstNonzeroProgram_value tapes (s.tick (condition.operations + 1))
          (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ)) scratch scratch
        change (first.memory.boolean scratch, first.memory.natural scratch) =
          nonzeroEncoding (MatrixElimination.firstNonzero (MatrixElimination.row M)) at hscan
        have hfirst : first.memory.real = s.memory.real :=
          Code.controlOnly_real _ (firstNonzero_control _ _ _) tapes _
        have hsecond : readMatrix (n + 1) input second.memory = M := by
          funext i j
          exact congrFun hfirst _
        have hprepared : readMatrix n (scratch + 2) third.memory =
            if M 0 0 = 0 then MatrixElimination.tail M else MatrixElimination.schur M := by
          have hp := preparePSD_value tapes second n input (scratch + 2) (by
            intro ij kl
            have h := hM ij
            unfold matrixAddress at *
            omega)
          rw [hsecond] at hp
          exact hp
        have hchild : psdResult n (scratch + 2 + n * n) flag fourth =
            MatrixElimination.psdWitness (readMatrix n (scratch + 2) third.memory) := by
          apply ih
          · intro ij
            have h := (finProdFinEquiv ij).isLt
            unfold matrixAddress
            omega
          · intro i
            have h := i.isLt
            unfold vectorAddress
            omega
          · intro ij i
            have h := (finProdFinEquiv ij).isLt
            unfold matrixAddress vectorAddress
            omega
        have hMfourth : readMatrix (n + 1) input fourth.memory = M := by
          funext i j
          have h := hM (i, j)
          change ((psdProgram n (scratch + 2) (scratch + 2 + n * n) flag
            (scratch + 2 + n * n + n)).execute tapes third).memory.real _ = _
          rw [psdProgram_frame _ _ _ _ _ _ _ _ (by omega) (by omega)]
          rw [preparePSD_frame _ _ _ _ _ _ (by omega)]
          exact congrFun hfirst _
        have hlift := liftPSD_result tapes fourth n input output flag (scratch + 1) (scratch + 2 + n * n)
          (by intro ij; have h := hM ij; omega)
          (by intro i; unfold vectorAddress; omega)
          (by intro i; have h := ho i; omega)
          (by intro i j; have h := ho j; unfold vectorAddress at *; omega)
        rw [hchild, hprepared, hMfourth] at hlift
        have hrun : (psdProgram (n + 1) input output flag scratch).execute tapes s =
            if test.eval first.memory then (specialPSDProgram n input output flag scratch).execute tapes second
            else (liftPSDProgram n input output flag (scratch + 1) (scratch + 2 + n * n)).execute tapes fourth := by
          simp only [psdProgram, Code.execute, hc, Bool.false_eq_true, ite_false]
          rfl
        rw [hrun]
        by_cases hz : M 0 0 = 0
        · cases hnonzero : MatrixElimination.firstNonzero (MatrixElimination.row M) with
          | none =>
              have hflag : first.memory.boolean scratch = false := by
                simpa only [hnonzero, nonzeroEncoding] using congrArg Prod.fst hscan
              have htest : test.eval first.memory = false := by
                simp [test, readReal, readBoolean, Expr.eval, hflag]
              simp only [htest, Bool.false_eq_true, ite_false]
              rw [hlift]
              simp [MatrixElimination.psdWitness, hnegative, hz, hnonzero]
          | some j =>
              have hflag : first.memory.boolean scratch = true := by
                simpa only [hnonzero, nonzeroEncoding] using congrArg Prod.fst hscan
              have hindex : second.memory.natural scratch = j.val := by
                simpa only [hnonzero, nonzeroEncoding] using congrArg Prod.snd hscan
              have hzero : first.memory.real (matrixAddress (n := n + 1) input (0, 0)) = 0 := by
                rw [hfirst]
                exact hz
              have htest : test.eval first.memory = true := by
                simp [test, readReal, readBoolean, Expr.eval, hflag, hzero]
              simp only [htest, Bool.true_eq, ite_true]
              rw [specialPSD_result _ _ _ _ _ _ _ j hindex ho]
              rw [hsecond]
              simp [MatrixElimination.psdWitness, hnegative, hz, hnonzero]
        · have hzero : first.memory.real (matrixAddress (n := n + 1) input (0, 0)) ≠ 0 := by
            rw [hfirst]
            exact hz
          have htest : test.eval first.memory = false := by
            simp [test, readReal, readBoolean, Expr.eval, hzero]
          simp only [htest, Bool.false_eq_true, ite_false]
          rw [hlift]
          simp only [MatrixElimination.psdWitness, hnegative, if_false, hz]

theorem psdProgram_correct (tapes : Tapes) (s : State) (n input output flag scratch : ℕ)
    (hM : ∀ ij : Fin n × Fin n, matrixAddress input ij < scratch)
    (ho : ∀ i : Fin n, vectorAddress output i < scratch)
    (hdisjoint : ∀ ij : Fin n × Fin n, ∀ i : Fin n, matrixAddress input ij ≠ vectorAddress output i)
    (hermitian : (readMatrix n input s.memory).IsHermitian) :
    match psdResult n output flag ((psdProgram n input output flag scratch).execute tapes s) with
    | none => (readMatrix n input s.memory).PosSemidef
    | some v => v ⬝ᵥ ((readMatrix n input s.memory) *ᵥ v) < 0 := by
  rw [psdProgram_value _ _ _ _ _ _ _ hM ho hdisjoint]
  exact MatrixElimination.psdWitness_correct _ hermitian

end DPCut.RealMachine
