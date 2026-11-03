import DPCut.RealMachineTargetFrames

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped RealInnerProductSpace

namespace DPCut.RealMachine.TargetCode

open SDP EllipsoidCode

def Prepared (n base : ℕ) (hm : 1 ≤ n*n) (threshold : ℝ) (s : State) :
    LSW.Reply (Fin (n*n)) → Prop
  | .inl g => s.memory.boolean (slot (n*n) base 14) = false ∧ EllipsoidCode.normal (n*n) base s = g
  | .inr (value,g) =>
      if threshold ≤ value then s.memory.boolean (slot (n*n) base 14) = true else
        s.memory.boolean (slot (n*n) base 14) = false ∧ EllipsoidCode.normal (n*n) base s =
          if g = 0 then EllipsoidOptimization.fixedNormal hm else -g

theorem gradientReject_value (tapes : Tapes) (s : State) (n base : ℕ) (hm : 1 ≤ n*n) :
    let result := (gradientReject n base).execute tapes s
    result.memory.boolean (slot (n*n) base 14) = false ∧ EllipsoidCode.normal (n*n) base result =
      if SDPFlat.equiv n (readCoordinates n (slot n (workspace n base) 3) s.memory) = 0
      then EllipsoidOptimization.fixedNormal hm
      else -(SDPFlat.equiv n (readCoordinates n (slot n (workspace n base) 3) s.memory)) := by
  let first := (coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).execute tapes s
  let condition := Expr.eq (readReal (slot n (workspace n base) 11 + 1)) (.rational 0)
  let next := first.tick (condition.operations + 1)
  let g := readCoordinates n (slot n (workspace n base) 3) s.memory
  have hnorm : first.memory.real (slot n (workspace n base) 11 + 1) = ‖g‖ :=
    coordinateNorm_value _ _ _ _ _ (by intro ij; have h := matrix_before_slot n (workspace n base) 3 11 (by decide) ij; omega)
  have hgNext : readCoordinates n (slot n (workspace n base) 3) next.memory = g := by
    ext ij
    have ha := matrix_before_slot n (workspace n base) 3 11 (by decide) ij
    change first.memory.real (matrixAddress (slot n (workspace n base) 3) ij) = _
    have hfloor : (coordinateNormProgram n (slot n (workspace n base) 3) (slot n (workspace n base) 11 + 1)).RealWriteFloor
        (slot n (workspace n base) 11) :=
      ⟨floor_sum _ _ _ (Nat.le_add_right _ _), floor_writeReal _ _ _ (Nat.le_add_right _ _)⟩
    exact Code.realWriteFloor_frame _ _ hfloor tapes s _ ha
  have hflat : SDPFlat.equiv n g = 0 ↔ g = 0 := by
    constructor
    · intro h; exact (SDPFlat.equiv n).injective (by simpa using h)
    · intro h; simp [h]
  have hrun : (gradientReject n base).execute tapes s =
      (reject n base).execute tapes
        (if condition.eval first.memory then (fixedNormalProgram n base).execute tapes next
        else (copyNormal n base true).execute tapes next) := rfl
  dsimp only
  rw [hrun]
  by_cases hg : g = 0
  · have hc : condition.eval first.memory = true := by simp [condition, Expr.eval, readReal, hnorm, hg]
    rw [hc]
    simp only [Bool.true_eq, ite_true]
    change ((reject n base).execute tapes ((fixedNormalProgram n base).execute tapes next)).memory.boolean _ = false ∧
      EllipsoidCode.normal (n*n) base ((reject n base).execute tapes ((fixedNormalProgram n base).execute tapes next)) = _
    have hg0 : SDPFlat.equiv n g = 0 := hflat.mpr hg
    refine ⟨writeBoolean_value _ _ _ _, ?_⟩
    change EllipsoidCode.normal (n*n) base ((fixedNormalProgram n base).execute tapes next) = _
    rw [fixedNormal_value _ _ _ _ hm]
    simp only [g, hg0, ite_true]
  · have hnorm0 : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    have hc : condition.eval first.memory = false := by simp [condition, Expr.eval, readReal, hnorm, hnorm0]
    rw [hc]
    simp only [Bool.false_eq_true, ite_false]
    change ((reject n base).execute tapes ((copyNormal n base true).execute tapes next)).memory.boolean _ = false ∧
      EllipsoidCode.normal (n*n) base ((reject n base).execute tapes ((copyNormal n base true).execute tapes next)) = _
    refine ⟨writeBoolean_value _ _ _ _, ?_⟩
    change EllipsoidCode.normal (n*n) base ((copyNormal n base true).execute tapes next) = _
    rw [copyNormal_value, hgNext]
    simp only [Bool.true_eq, ite_true]
    change -(SDPFlat.equiv n g) = if SDPFlat.equiv n g = 0 then _ else -(SDPFlat.equiv n g)
    rw [if_neg (show SDPFlat.equiv n g ≠ 0 from fun h => hg (hflat.mp h))]

theorem decideReply_value (tapes : Tapes) (s : State) (n base : ℕ) (hm : 1 ≤ n*n) :
    Prepared n base hm (s.memory.real (slot (n*n) base 13)) ((decideReply n base).execute tapes s)
      (SDPFlat.mapReply n (SDP.reply n (workspace n base) s)) := by
  let first := s.tick ((readBoolean (slot n (workspace n base) 4)).operations + 1)
  let condition := Expr.le (readReal (slot (n*n) base 13)) (readReal (slot n (workspace n base) 4))
  let next := first.tick (condition.operations + 1)
  have hrun : (decideReply n base).execute tapes s =
      if s.memory.boolean (slot n (workspace n base) 4) then
        (if condition.eval first.memory then (accept n base).execute tapes next else (gradientReject n base).execute tapes next)
      else (reject n base).execute tapes ((copyNormal n base false).execute tapes first) := rfl
  rw [hrun]
  by_cases hf : s.memory.boolean (slot n (workspace n base) 4) = true
  · simp only [hf, ite_true, SDP.reply,
      SDPFlat.mapReply, Prepared]
    by_cases ha : s.memory.real (slot (n*n) base 13) ≤ s.memory.real (slot n (workspace n base) 4)
    · have hc : condition.eval first.memory = true := by simp [condition, Expr.eval, readReal, first, State.tick, ha]
      rw [hc]
      simp [ha, accept, writeBoolean, Code.execute, Expr.eval, Memory.writeBoolean]
    · have hc : condition.eval first.memory = false := by simp [condition, Expr.eval, readReal, first, State.tick, ha]
      rw [if_neg ha]
      rw [hc]
      simp only [Bool.false_eq_true, ite_false]
      exact gradientReject_value tapes next n base hm
  · have hf' := Bool.eq_false_of_not_eq_true hf
    simp only [hf', Bool.false_eq_true, ite_false,
      SDP.reply, SDPFlat.mapReply, Prepared]
    change ((reject n base).execute tapes ((copyNormal n base false).execute tapes first)).memory.boolean _ = false ∧
      EllipsoidCode.normal (n*n) base ((reject n base).execute tapes ((copyNormal n base false).execute tapes first)) = _
    refine ⟨writeBoolean_value _ _ _ _, ?_⟩
    change EllipsoidCode.normal (n*n) base ((copyNormal n base false).execute tapes first) = _
    exact copyNormal_value tapes first n base false

end DPCut.RealMachine.TargetCode
