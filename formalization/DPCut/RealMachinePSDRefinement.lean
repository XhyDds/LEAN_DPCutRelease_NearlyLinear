import DPCut.RealMachinePSD

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped BigOperators

namespace DPCut.RealMachine

theorem tailProgram_frame (tapes : Tapes) (s : State) (n input output address : ℕ)
    (h : address < output) :
    ((tailProgram n input output).execute tapes s).memory.real address = s.memory.real address :=
  matrixMap_below _ _ _ _ _ _ h

theorem tailProgram_value (tapes : Tapes) (s : State) (n input output : ℕ)
    (h : ∀ i : Fin (n + 1) × Fin (n + 1), ∀ j : Fin n × Fin n,
      matrixAddress input i ≠ matrixAddress output j) :
    readMatrix n output ((tailProgram n input output).execute tapes s).memory =
      MatrixElimination.tail (readMatrix (n + 1) input s.memory) := by
  funext i j
  exact matrixMap_value _ _ _ _ _ (fun ij kl => realFrame_read _ _ (h (ij.1.succ, ij.2.succ) kl)) i j

theorem liftPivot_realOnly (n input pivot child : ℕ) : (liftPivotProgram n input pivot child).RealOnly :=
  ⟨trivial, ⟨dotProgram_realOnly _ _ _, trivial⟩⟩

theorem liftPSD_realOnly (n input output flag pivot child : ℕ) :
    (liftPSDProgram n input output flag pivot child).RealOnly :=
  ⟨⟨liftPivot_realOnly _ _ _ _, arrayProgram_realOnly _ _⟩, trivial⟩

theorem liftPivot_frame (tapes : Tapes) (s : State) (n input pivot child address : ℕ) (h : address ≠ pivot) :
    ((liftPivotProgram n input pivot child).execute tapes s).memory.real address = s.memory.real address := by
  unfold liftPivotProgram
  simp only [Code.execute]
  split
  · exact writeReal_frame _ _ _ _ _ h
  · rw [writeReal_frame _ _ _ _ _ h]
    exact dotProgram_frame _ _ _ _ _ _ h

theorem liftPivot_value (tapes : Tapes) (s : State) (n input pivot child : ℕ)
    (hM : ∀ i : Fin (n + 1) × Fin (n + 1), matrixAddress input i ≠ pivot)
    (hchild : ∀ i : Fin n, vectorAddress child i ≠ pivot) :
    ((liftPivotProgram n input pivot child).execute tapes s).memory.real pivot =
      if (readMatrix (n + 1) input s.memory) 0 0 = 0 then 0 else
        -(MatrixElimination.row (readMatrix (n + 1) input s.memory) ⬝ᵥ readVector n child s.memory) /
          (readMatrix (n + 1) input s.memory) 0 0 := by
  by_cases hz : (readMatrix (n + 1) input s.memory) 0 0 = 0
  · change s.memory.real (matrixAddress (n := n + 1) input (0, 0)) = 0 at hz
    simp [liftPivotProgram, Code.execute, writeReal, readReal, Expr.eval, Memory.writeReal, hz, readMatrix, State.tick]
  · let next := (dotProgram (fun i : Fin n => matrixAddress (n := n + 1) input (0, i.succ))
        (fun i => vectorAddress child i) pivot).execute tapes
        (s.tick ((Expr.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)).operations + 1))
    have hp : next.memory.real pivot =
        MatrixElimination.row (readMatrix (n + 1) input s.memory) ⬝ᵥ readVector n child s.memory := by
      exact dotProgram_value _ _ _ _ _ (fun i => hM (0, i.succ)) hchild
    have hm : next.memory.real (matrixAddress (n := n + 1) input (0, 0)) =
        s.memory.real (matrixAddress (n := n + 1) input (0, 0)) := dotProgram_frame _ _ _ _ _ _ (hM (0, 0))
    have hcond : (Expr.eq (readReal (matrixAddress (n := n + 1) input (0, 0))) (.rational 0)).eval s.memory = false := by
      simp [Expr.eval, readReal, readMatrix] at hz ⊢
      exact hz
    simp only [liftPivotProgram, Code.execute, hcond, Bool.false_eq_true, ite_false, hz] at ⊢
    change ((writeReal pivot (.div (.neg (readReal pivot))
      (readReal (matrixAddress (n := n + 1) input (0, 0))))).execute tapes next).memory.real pivot = _
    rw [writeReal_value]
    simp only [Expr.eval, readReal, hp, hm, if_neg hz, readMatrix]

theorem liftPSD_frame (tapes : Tapes) (s : State) (n input output flag pivot child address : ℕ)
    (hp : address ≠ pivot) (ho : ∀ i : Fin (n + 1), address ≠ vectorAddress output i) :
    ((liftPSDProgram n input output flag pivot child).execute tapes s).memory.real address = s.memory.real address := by
  unfold liftPSDProgram
  simp only [Code.execute]
  split
  · unfold arrayProgram
    rw [arrayLoop_frame _ _ _ _ _ _ (fun i _ => ho i)]
    exact liftPivot_frame _ _ _ _ _ _ _ hp
  · rfl

theorem liftPSD_result (tapes : Tapes) (s : State) (n input output flag pivot child : ℕ)
    (hM : ∀ i : Fin (n + 1) × Fin (n + 1), matrixAddress input i ≠ pivot)
    (hchild : ∀ i : Fin n, vectorAddress child i ≠ pivot)
    (hp : ∀ i : Fin (n + 1), pivot ≠ vectorAddress output i)
    (hdisjoint : ∀ i : Fin n, ∀ j : Fin (n + 1), vectorAddress child i ≠ vectorAddress output j) :
    psdResult (n + 1) output flag ((liftPSDProgram n input output flag pivot child).execute tapes s) =
      (psdResult n child flag s).map (fun v => MatrixElimination.prepend
        (if (readMatrix (n + 1) input s.memory) 0 0 = 0 then 0 else
          -(MatrixElimination.row (readMatrix (n + 1) input s.memory) ⬝ᵥ v) /
            (readMatrix (n + 1) input s.memory) 0 0) v) := by
  have hflag := (Code.realOnly_control _ (liftPSD_realOnly n input output flag pivot child) tapes s).2
  by_cases hf : s.memory.boolean flag = true
  · let first := (liftPivotProgram n input pivot child).execute tapes
      (s.tick ((readBoolean flag).operations + 1))
    have hvector : readVector n child first.memory = readVector n child s.memory := by
      funext i
      exact liftPivot_frame _ _ _ _ _ _ _ (hchild i)
    have hvalue := liftPivot_value tapes (s.tick ((readBoolean flag).operations + 1)) n input pivot child hM hchild
    change first.memory.real pivot = _ at hvalue
    have hv := arrayProgram_value tapes first (fun i : Fin (n + 1) => vectorAddress output i)
      (liftOutputExpr n pivot child) (vectorAddress_injective output) (by
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · exact realFrame_read _ _ (hp j)
        · exact realFrame_read _ _ (hdisjoint i j))
    simp only [psdResult, hflag, hf, Bool.true_eq, ite_true, Option.map_some]
    congr 1
    funext i
    simp only [liftPSDProgram, Code.execute, readBoolean, Expr.eval, hf, Bool.true_eq, ite_true]
    change ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
      (liftOutputExpr n pivot child)).execute tapes first).memory.real (vectorAddress output i) = _
    rw [hv i]
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa only [liftOutputExpr, Fin.cases_zero, Expr.eval, readReal, MatrixElimination.prepend, Fin.cons_zero,
        State.tick] using hvalue
    · simpa only [liftOutputExpr, Fin.cases_succ, Expr.eval, readReal, MatrixElimination.prepend, Fin.cons_succ]
        using congrFun hvector i
  · have hf' : s.memory.boolean flag = false := Bool.eq_false_of_not_eq_true hf
    simp only [psdResult, hflag, hf', Bool.false_eq_true, ite_false, Option.map_none]

end DPCut.RealMachine
