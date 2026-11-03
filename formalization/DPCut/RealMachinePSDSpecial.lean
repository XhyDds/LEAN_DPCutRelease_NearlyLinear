import DPCut.RealMachinePSDRefinement

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

theorem negativePSD_result (tapes : Tapes) (s : State) (n output flag : ℕ) :
    psdResult (n + 1) output flag ((negativePSDProgram n output flag).execute tapes s) =
      some (MatrixElimination.prepend 1 0) := by
  let first := (writeBoolean flag (.boolean true)).execute tapes s
  have hf : first.memory.boolean flag = true := writeBoolean_value _ _ _ _
  have hc := (Code.realOnly_control _ (arrayProgram_realOnly
    (fun i : Fin (n + 1) => vectorAddress output i)
    (fun i => .rational (if i = 0 then 1 else 0))) tapes first).2
  change psdResult (n + 1) output flag ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
    (fun i => .rational (if i = 0 then 1 else 0))).execute tapes first) = _
  simp only [psdResult, hc, hf, Bool.true_eq, ite_true]
  congr 1
  funext i
  have h := arrayProgram_value tapes first (fun i : Fin (n + 1) => vectorAddress output i)
    (fun i => Expr.rational (if i = 0 then 1 else 0)) (vectorAddress_injective output)
    (fun _ _ => realFrame_rational _ _) i
  refine h.trans ?_
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [Expr.eval, MatrixElimination.prepend]

theorem specialPivot_value (s : State) (n input index : ℕ) (j : Fin n)
    (hj : s.memory.natural index = j.val) :
    (specialPivotExpr n input index).eval s.memory =
      -(MatrixElimination.tail (readMatrix (n + 1) input s.memory) j j + 1) /
        (2 * MatrixElimination.row (readMatrix (n + 1) input s.memory) j) := by
  have hdiag : input + (n + 2) * (j.val + 1) =
      matrixAddress (n := n + 1) input (j.succ, j.succ) := by
    simp only [matrixAddress, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_succ]
    ring
  have hrow : input + (j.val + 1) = matrixAddress (n := n + 1) input (0, j.succ) := by
    simp [matrixAddress, finProdFinEquiv]
  simp only [specialPivotExpr, Expr.eval, readNatural, hj, hdiag, hrow,
    readMatrix, MatrixElimination.tail, MatrixElimination.row, Rat.cast_one, Rat.cast_ofNat]

theorem specialPSD_result (tapes : Tapes) (s : State) (n input output flag scratch : ℕ) (j : Fin n)
    (hj : s.memory.natural scratch = j.val)
    (ho : ∀ i : Fin (n + 1), vectorAddress output i < scratch) :
    psdResult (n + 1) output flag ((specialPSDProgram n input output flag scratch).execute tapes s) =
      some (MatrixElimination.prepend
        (-(MatrixElimination.tail (readMatrix (n + 1) input s.memory) j j + 1) /
          (2 * MatrixElimination.row (readMatrix (n + 1) input s.memory) j)) (Pi.single j 1)) := by
  let first := (writeReal (scratch + 1) (specialPivotExpr n input scratch)).execute tapes s
  let second := (writeBoolean flag (.boolean true)).execute tapes first
  have hf : second.memory.boolean flag = true := writeBoolean_value _ _ _ _
  have hpivot : second.memory.real (scratch + 1) = (specialPivotExpr n input scratch).eval s.memory :=
    writeReal_value tapes s (scratch + 1) _
  have hindex : second.memory.natural scratch = j.val := hj
  have hframe : ∀ i k : Fin (n + 1),
      (specialOutputExpr n (scratch + 1) scratch i).RealFrame (vectorAddress output k) := by
    intro i k
    refine Fin.cases ?_ (fun i => ?_) i
    · exact realFrame_read _ _ (by have h := ho k; omega)
    · exact realFrame_select (realFrame_natEq (realFrame_natural _ _) (realFrame_readNatural _ _))
        (realFrame_rational _ _) (realFrame_rational _ _)
  have hcontrol := (Code.realOnly_control _ (arrayProgram_realOnly
    (fun i : Fin (n + 1) => vectorAddress output i) (specialOutputExpr n (scratch + 1) scratch)) tapes second).2
  change psdResult (n + 1) output flag ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
    (specialOutputExpr n (scratch + 1) scratch)).execute tapes second) = _
  simp only [psdResult, hcontrol, hf, Bool.true_eq, ite_true]
  congr 1
  funext i
  change ((arrayProgram (fun i : Fin (n + 1) => vectorAddress output i)
    (specialOutputExpr n (scratch + 1) scratch)).execute tapes second).memory.real (vectorAddress output i) = _
  rw [arrayProgram_value _ _ _ _ (vectorAddress_injective output) hframe i]
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa only [specialOutputExpr, Fin.cases_zero, Expr.eval, readReal, MatrixElimination.prepend,
      Fin.cons_zero] using hpivot.trans (specialPivot_value s n input scratch j hj)
  · simp only [specialOutputExpr, Fin.cases_succ, Expr.eval, readNatural, hindex, Rat.cast_one,
      Rat.cast_zero, MatrixElimination.prepend, Fin.cons_succ, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · have hi : i.val ≠ j.val := fun he => h (Fin.ext he)
      simp [h, hi]

end DPCut.RealMachine
