import DPCut.RealMachineSchur
import DPCut.MatrixSPDAlgorithm

/-! The recursive linear solve is lowered to scalar register instructions.
There is no matrix-inverse primitive in this implementation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def vectorAddress (base : ℕ) {n : ℕ} (i : Fin n) : ℕ := base + i.val
def readVector (n base : ℕ) (memory : Memory) : Fin n → ℝ := fun i => memory.real (vectorAddress base i)

def rhsExpr (n input rhs : ℕ) (i : Fin n) : Expr .real :=
  .sub (readReal (vectorAddress rhs i.succ))
    (.div (.mul (readReal (matrixAddress (n := n + 1) input (0, i.succ))) (readReal rhs))
      (readReal (matrixAddress (n := n + 1) input (0, 0))))

def rhsProgram (n input rhs output : ℕ) : Code :=
  arrayProgram (fun i : Fin n => vectorAddress output i) (rhsExpr n input rhs)

theorem rhsProgram_steps (n input rhs output : ℕ) : Steps (rhsProgram n input rhs output) (13 * n) := by
  have h := arrayProgram_steps (fun i : Fin n => vectorAddress output i) (rhsExpr n input rhs) 11 (by intro i; rfl)
  simpa only [rhsProgram, Nat.mul_comm] using h

def solveOutput (n input rhs child sum : ℕ) (i : Fin (n + 1)) : Expr .real :=
  Fin.cases (.div (.sub (readReal rhs) (readReal sum)) (readReal (matrixAddress (n := n + 1) input (0, 0))))
    (fun j => readReal (vectorAddress child j)) i

def solveProgram : ℕ → ℕ → ℕ → ℕ → ℕ → Code
  | 0, _, _, _, _ => .skip
  | n + 1, input, rhs, output, scratch =>
      .seq (schurProgram n input scratch)
        (.seq (rhsProgram n input rhs (scratch + n * n))
          (.seq (solveProgram n scratch (scratch + n * n) (scratch + n * n + n) (scratch + n * n + 2 * n))
            (.seq (dotProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
              (fun i => vectorAddress (scratch + n * n + n) i) scratch)
              (arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
                (solveOutput n input rhs (scratch + n * n + n) scratch)))))

theorem solveOutput_steps (n input rhs child sum : ℕ) (i : Fin (n + 1)) :
    (solveOutput n input rhs child sum i).operations ≤ 8 := by
  refine Fin.cases ?_ (fun i => ?_) i <;>
    norm_num [solveOutput, Expr.operations, readReal]

theorem solveProgram_steps (n input rhs output scratch : ℕ) :
    Steps (solveProgram n input rhs output scratch) (100 * (n + 1) ^ 3) := by
  induction n generalizing input rhs output scratch with
  | zero => exact Steps.skip.mono (Nat.zero_le _)
  | succ n ih =>
      have hs := schurProgram_steps n input scratch
      have hr := rhsProgram_steps n input rhs (scratch + n * n)
      have hc := ih scratch (scratch + n * n) (scratch + n * n + n) (scratch + n * n + 2 * n)
      have hd := dotProgram_steps (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
        (fun i => vectorAddress (scratch + n * n + n) i) scratch
      have ho := arrayProgram_steps (fun i : Fin (n + 1) => vectorAddress output i)
        (solveOutput n input rhs (scratch + n * n + n) scratch) 8 (solveOutput_steps _ _ _ _ _)
      exact (hs.seq (hr.seq (hc.seq (hd.seq ho)))).mono (by nlinarith)

theorem solveProgram_below (tapes : Tapes) (s : State) (n input rhs output scratch address : ℕ)
    (hout : address < output) (hscratch : address < scratch) :
    ((solveProgram n input rhs output scratch).execute tapes s).memory.real address = s.memory.real address := by
  induction n generalizing s input rhs output scratch with
  | zero => rfl
  | succ n ih =>
      simp only [solveProgram, Code.execute]
      unfold arrayProgram
      rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)]
      rw [dotProgram_frame _ _ _ _ _ _ (by omega)]
      rw [ih _ _ _ _ _ (by omega) (by omega)]
      unfold rhsProgram arrayProgram
      rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)]
      unfold schurProgram
      exact matrixMap_below _ _ _ _ _ _ hscratch

theorem vectorAddress_injective (base : ℕ) {n : ℕ} : Function.Injective (vectorAddress base : Fin n → ℕ) := by
  intro i j h
  apply Fin.ext
  unfold vectorAddress at h
  omega

theorem rhsProgram_value (tapes : Tapes) (s : State) (n input rhs output : ℕ)
    (hM : ∀ i : Fin (n + 1) × Fin (n + 1), ∀ j : Fin n,
      matrixAddress input i ≠ vectorAddress output j)
    (hb : ∀ i : Fin (n + 1), ∀ j : Fin n, vectorAddress rhs i ≠ vectorAddress output j) :
    readVector n output ((rhsProgram n input rhs output).execute tapes s).memory =
      (fun i => (readVector (n + 1) rhs s.memory) i.succ -
        MatrixElimination.row (readMatrix (n + 1) input s.memory) i *
          (readVector (n + 1) rhs s.memory) 0 / (readMatrix (n + 1) input s.memory) 0 0) := by
  have hf : ∀ i j : Fin n, (rhsExpr n input rhs i).RealFrame (vectorAddress output j) := by
    intro i j
    exact realFrame_sub (realFrame_read _ _ (hb i.succ j))
      (realFrame_div (realFrame_mul (realFrame_read _ _ (hM (0, i.succ) j))
        (realFrame_read _ _ (by simpa only [vectorAddress, Fin.val_zero, Nat.add_zero] using hb 0 j)))
        (realFrame_read _ _ (hM (0, 0) j)))
  funext i
  have h := arrayProgram_value tapes s (fun j : Fin n => vectorAddress output j) (rhsExpr n input rhs)
    (vectorAddress_injective output) hf i
  exact h.trans (by simp only [rhsExpr, Expr.eval, readReal, readVector, vectorAddress,
    Fin.val_zero, Nat.add_zero, readMatrix, MatrixElimination.row])

theorem solveProgram_value (tapes : Tapes) (s : State) (n input rhs output scratch : ℕ)
    (hM : ∀ i : Fin n × Fin n, matrixAddress input i < scratch)
    (hb : ∀ i : Fin n, vectorAddress rhs i < scratch)
    (ho : ∀ i : Fin n, vectorAddress output i < scratch)
    (hMO : ∀ i : Fin n × Fin n, ∀ j : Fin n, matrixAddress input i ≠ vectorAddress output j)
    (hbO : ∀ i j : Fin n, vectorAddress rhs i ≠ vectorAddress output j) :
    readVector n output ((solveProgram n input rhs output scratch).execute tapes s).memory =
      MatrixElimination.solve (readMatrix n input s.memory) (readVector n rhs s.memory) := by
  induction n generalizing s input rhs output scratch with
  | zero => ext i; exact Fin.elim0 i
  | succ n ih =>
      let first := (schurProgram n input scratch).execute tapes s
      let second := (rhsProgram n input rhs (scratch + n * n)).execute tapes first
      let third := (solveProgram n scratch (scratch + n * n) (scratch + n * n + n) (scratch + n * n + 2 * n)).execute tapes second
      let fourth := (dotProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
        (fun i => vectorAddress (scratch + n * n + n) i) scratch).execute tapes third
      have matrixFrame (memory : State) (h : ∀ address < scratch, memory.memory.real address = s.memory.real address) :
          readMatrix (n + 1) input memory.memory = readMatrix (n + 1) input s.memory := by
        funext i j
        exact h _ (hM (i, j))
      have vectorFrame (memory : State) (h : ∀ address < scratch, memory.memory.real address = s.memory.real address) :
          readVector (n + 1) rhs memory.memory = readVector (n + 1) rhs s.memory := by
        funext i
        exact h _ (hb i)
      have hfirst (address : ℕ) (ha : address < scratch) : first.memory.real address = s.memory.real address :=
        matrixMap_below _ _ _ _ _ _ ha
      have hsecond (address : ℕ) (ha : address < scratch) : second.memory.real address = s.memory.real address := by
        change ((arrayProgram (fun i : Fin n => vectorAddress (scratch + n * n) i) (rhsExpr n input rhs)).execute tapes first).memory.real address = _
        unfold arrayProgram
        rw [arrayLoop_frame _ _ _ _ _ _ (by intro i _; unfold vectorAddress; omega)]
        exact hfirst address ha
      have hthird (address : ℕ) (ha : address < scratch) : third.memory.real address = s.memory.real address := by
        rw [solveProgram_below _ _ _ _ _ _ _ _ (by omega) (by omega)]
        exact hsecond address ha
      have hfourth (address : ℕ) (ha : address < scratch) : fourth.memory.real address = s.memory.real address := by
        rw [dotProgram_frame _ _ _ _ _ _ (by omega)]
        exact hthird address ha
      have hSfirst : readMatrix n scratch first.memory = MatrixElimination.schur (readMatrix (n + 1) input s.memory) :=
        schurProgram_value _ _ _ _ _ (by
          intro i j
          have h := hM i
          unfold matrixAddress at *
          omega)
      have hSsecond : readMatrix n scratch second.memory = readMatrix n scratch first.memory := by
        funext i j
        change ((arrayProgram (fun k : Fin n => vectorAddress (scratch + n * n) k) (rhsExpr n input rhs)).execute tapes first).memory.real _ = _
        unfold arrayProgram
        apply arrayLoop_frame
        intro k _
        have h := (finProdFinEquiv (i, j)).isLt
        unfold matrixAddress vectorAddress
        omega
      have hC : readVector n (scratch + n * n) second.memory =
          (fun i => (readVector (n + 1) rhs s.memory) i.succ -
            MatrixElimination.row (readMatrix (n + 1) input s.memory) i *
              (readVector (n + 1) rhs s.memory) 0 / (readMatrix (n + 1) input s.memory) 0 0) := by
        have h := rhsProgram_value tapes first n input rhs (scratch + n * n) (by
          intro i j
          have h := hM i
          unfold vectorAddress
          omega) (by intro i j; have h := hb i; unfold vectorAddress at h ⊢; omega)
        rw [matrixFrame first hfirst, vectorFrame first hfirst] at h
        exact h
      have hY : readVector n (scratch + n * n + n) third.memory =
          MatrixElimination.solve (readMatrix n scratch second.memory) (readVector n (scratch + n * n) second.memory) := by
        apply ih
        · intro ij; have h := (finProdFinEquiv ij).isLt; unfold matrixAddress; omega
        · intro i; have h := i.isLt; unfold vectorAddress; omega
        · intro i; have h := i.isLt; unfold vectorAddress; omega
        · intro ij j; have h := (finProdFinEquiv ij).isLt; unfold matrixAddress vectorAddress; omega
        · intro i j; have h := i.isLt; unfold vectorAddress; omega
      rw [hSsecond, hSfirst, hC] at hY
      have hYfourth : readVector n (scratch + n * n + n) fourth.memory =
          readVector n (scratch + n * n + n) third.memory := by
        funext i
        exact dotProgram_frame _ _ _ _ _ _ (by unfold vectorAddress; have h := i.isLt; omega)
      have hsum : fourth.memory.real scratch = MatrixElimination.row (readMatrix (n + 1) input s.memory) ⬝ᵥ
          readVector n (scratch + n * n + n) third.memory := by
        have h := dotProgram_value tapes third (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
          (fun i => vectorAddress (scratch + n * n + n) i) scratch
          (by intro i; exact (hM (0, i.succ)).ne)
          (by intro i; change scratch + n * n + n + i.val ≠ scratch; have h := i.isLt; omega)
        change fourth.memory.real scratch = _ at h
        have hm := matrixFrame third hthird
        change _ = ∑ i, _ at h ⊢
        rw [← hm]
        exact h
      have hframe : ∀ i j : Fin (n + 1),
          (solveOutput n input rhs (scratch + n * n + n) scratch i).RealFrame (vectorAddress output j) := by
        intro i j
        have hout := ho j
        refine Fin.cases ?_ (fun i => ?_) i
        · exact realFrame_div (realFrame_sub
            (realFrame_read _ _ (by simpa only [vectorAddress, Fin.val_zero, Nat.add_zero] using hbO 0 j))
            (realFrame_read _ _ (by omega))) (realFrame_read _ _ (hMO (0, 0) j))
        · apply realFrame_read
          unfold vectorAddress at *
          omega
      change readVector (n + 1) output ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
        (solveOutput n input rhs (scratch + n * n + n) scratch)).execute tapes fourth).memory = _
      funext i
      change ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
        (solveOutput n input rhs (scratch + n * n + n) scratch)).execute tapes fourth).memory.real (vectorAddress output i) = _
      rw [arrayProgram_value _ _ _ _ (vectorAddress_injective output) hframe i]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp only [solveOutput, Fin.cases_zero, Expr.eval, readReal, MatrixElimination.solve,
          MatrixElimination.prepend, Fin.cases_succ]
        rw [hsum]
        have hm := matrixFrame fourth hfourth
        have hv := vectorFrame fourth hfourth
        have hb0 := congrFun hv 0
        have hm0 := congrFun (congrFun hm 0) 0
        change fourth.memory.real rhs = s.memory.real rhs at hb0
        change fourth.memory.real (matrixAddress (n := n + 1) input (0, 0)) =
          s.memory.real (matrixAddress (n := n + 1) input (0, 0)) at hm0
        simp only [readVector, vectorAddress, Fin.val_zero, Nat.add_zero, readMatrix] at ⊢
        rw [hb0, hm0, hY]
        rfl
      · have h := congrFun (hYfourth.trans hY) i
        simpa only [solveOutput, Fin.cases_succ, Expr.eval, readReal,
          MatrixElimination.solve, MatrixElimination.prepend, readVector] using h

end DPCut.RealMachine
