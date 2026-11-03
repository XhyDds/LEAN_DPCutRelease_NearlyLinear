import DPCut.RealMachineSDPInside
import DPCut.RealMachineWriteFloor

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

open Matrix

namespace DPCut.RealMachine.SDP

theorem inside_floor (n base floor : ℕ) (h : floor ≤ slot n base 3) :
    (inside n base).RealWriteFloor floor := by
  have hslot (k : ℕ) (hk : 3 ≤ k) : floor ≤ slot n base k := by
    by_cases he : k = 3
    · simpa [he] using h
    · exact h.trans (slot_lt_slot _ _ _ _ (by omega)).le
  exact ⟨floor_inverse _ _ _ _ _ (hslot _ (by decide)) (hslot _ (by decide)),
    floor_determinant _ _ _ _ _ (hslot _ (by decide)) (hslot _ (by decide)),
    floor_sum _ _ _ (by have hs := hslot 11 (by decide); omega),
    floor_array _ _ _ (fun k => by have hs := hslot 10 (by decide); omega),
    floor_matrixSum _ _ _ _ _ (hslot _ (by decide)),
    floor_matrixMap _ _ _ _ h,
    floor_sum _ _ _ (hslot _ (by decide)),
    floor_writeReal _ _ _ (hslot _ (by decide)), trivial⟩

theorem body_floor (n base floor : ℕ) (h : floor ≤ slot n base 3) :
    (body n base).RealWriteFloor floor := by
  have hslot (k : ℕ) (hk : 3 < k) := h.trans (slot_lt_slot n base 3 k hk).le
  exact ⟨floor_matrixMap _ _ _ _ (hslot _ (by decide)),
    floor_matrixMap _ _ _ _ (hslot _ (by decide)),
    floor_psd _ _ _ _ _ _ (hslot _ (by decide)) (hslot _ (by decide)),
    ⟨⟨floor_matrixMap _ _ _ _ h, trivial⟩, inside_floor n base floor h⟩⟩

theorem oracleProgram_floor (n base floor : ℕ) (h : floor ≤ slot n base 3) :
    (oracleProgram n base).RealWriteFloor floor := by
  have hnorm : floor ≤ slot n base 11 + 1 := by have hs := slot_lt_slot n base 3 11 (by decide); omega
  exact ⟨⟨floor_sum _ _ _ hnorm, floor_writeReal _ _ _ hnorm⟩,
    ⟨⟨floor_matrixMap _ _ _ _ h, trivial⟩, body_floor n base floor h⟩⟩

def bodyReply (n : ℕ) (lam B : ℝ) (D : Weights n) (x : SDPCoordinates.Space n) : LSW.Reply (Fin n × Fin n) :=
  (MatrixElimination.totalPSD (SDPCoordinates.slack x)).elim
    (.inr (objective lam (boundedObjective B D) (SDPCoordinates.lift x),
      SDPCoordinates.normal n (objectiveMatrix (boundedObjective B D) + lam • (SDPCoordinates.lift x)⁻¹)))
    (fun v => .inl (SDPCoordinates.normal n (-(vecMulVec v v))))

theorem separate_value (tapes : Tapes) (s : State) (n base : ℕ) :
    reply n base ((separate n base).execute tapes s) =
      .inl (SDPCoordinates.normal n (-(vecMulVec (readVector n (slot n base 7) s.memory)
        (readVector n (slot n base 7) s.memory)))) := by
  let first := (negativeNormalProgram n (slot n base 7) (slot n base 3)).execute tapes s
  have hvalue := negativeNormal_value tapes s n (slot n base 7) (slot n base 3) (by
    intro i ij
    have hi := (vector_range (slot n base 7) i).1
    have ho := matrix_before_slot n base 3 7 (by decide) ij
    omega)
  change reply n base ((writeBoolean (slot n base 4) (.boolean false)).execute tapes first) = _
  simp only [reply, writeBoolean, Code.execute, Expr.eval, Memory.writeBoolean, Function.update_self,
    Bool.false_eq_true, ite_false]
  change Sum.inl (readCoordinates n (slot n base 3) first.memory) = _
  exact congrArg Sum.inl hvalue

theorem outside_value (tapes : Tapes) (s : State) (n base : ℕ) :
    reply n base ((outside n base).execute tapes s) = .inl (inputPoint n base s) := by
  let first := (matrixMapProgram n (slot n base 3) (fun ij => readReal (matrixAddress (slot n base 1) ij))).execute tapes s
  have hvalue : readCoordinates n (slot n base 3) first.memory = inputPoint n base s := by
    ext ij
    exact matrixMap_value tapes s n (slot n base 3) _ (fun ij kl =>
      realFrame_read _ _ (matrix_disjoint n base 1 3 (by decide) ij kl)) ij.1 ij.2
  change reply n base ((writeBoolean (slot n base 4) (.boolean false)).execute tapes first) = _
  simp only [reply, writeBoolean, Code.execute, Expr.eval, Memory.writeBoolean, Function.update_self,
    Bool.false_eq_true, ite_false]
  change Sum.inl (readCoordinates n (slot n base 3) first.memory) = _
  exact congrArg Sum.inl hvalue

theorem body_value (tapes : Tapes) (s : State) (n base : ℕ) (hn : 2 ≤ n) :
    reply n base ((body n base).execute tapes s) =
      bodyReply n (inputLambda n base s) (inputBound n base s) (inputWeights n base s) (inputPoint n base s) := by
  let a := (liftCoordinatesProgram n (slot n base 1) (slot n base 5)).execute tapes s
  let b := (slackProgram n (slot n base 5) (slot n base 6)).execute tapes a
  let c := (psdProgram n (slot n base 6) (slot n base 7) (slot n base 4) (slot n base 12)).execute tapes b
  let next := c.tick ((readBoolean (slot n base 4)).operations + 1)
  have hA : readMatrix n (slot n base 5) a.memory = SDPCoordinates.lift (inputPoint n base s) :=
    liftCoordinates_value _ _ _ _ _ (matrix_disjoint _ _ _ _ (by decide))
  have hB : readMatrix n (slot n base 6) b.memory = SDPCoordinates.slack (inputPoint n base s) := by
    rw [slackProgram_value _ _ _ _ _ (matrix_disjoint _ _ _ _ (by decide)), hA]
    rfl
  have hC : psdResult n (slot n base 7) (slot n base 4) c =
      MatrixElimination.totalPSD (SDPCoordinates.slack (inputPoint n base s)) := by
    rw [psdProgram_value _ _ _ _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))
      (vector_before_slot _ _ _ _ (by decide)) (by
        intro ij i
        have hm := matrix_before_slot n base 6 7 (by decide) ij
        have hv := (vector_range (slot n base 7) i).1
        omega), hB]
    simp only [MatrixElimination.totalPSD, MatrixElimination.symmetrize_eq
      (SDPCoordinates.slack_hermitian (inputPoint n base s))]
  have da (address : ℕ) (ha : address < slot n base 5) : a.memory.real address = s.memory.real address :=
    Code.realWriteFloor_frame _ (slot n base 5) (floor_matrixMap _ _ _ _ le_rfl) tapes s address ha
  have db (address : ℕ) (ha : address < slot n base 6) : b.memory.real address = a.memory.real address :=
    Code.realWriteFloor_frame _ (slot n base 6) (floor_matrixMap _ _ _ _ le_rfl) tapes a address ha
  have dc (address : ℕ) (ha : address < slot n base 7) : next.memory.real address = b.memory.real address :=
    Code.realWriteFloor_frame (psdProgram n (slot n base 6) (slot n base 7) (slot n base 4) (slot n base 12))
      (slot n base 7) (floor_psd _ _ _ _ _ _ le_rfl (slot_lt_slot n base 7 12 (by decide)).le) tapes b address ha
  have hX : readMatrix n (slot n base 5) next.memory = SDPCoordinates.lift (inputPoint n base s) := by
    funext i j
    change next.memory.real (matrixAddress (slot n base 5) (i,j)) = _
    rw [dc _ (matrix_before_slot n base 5 7 (by decide) (i,j)),
      db _ (matrix_before_slot n base 5 6 (by decide) (i,j))]
    exact congrFun (congrFun hA i) j
  have hlow (address : ℕ) (ha : address < slot n base 5) : next.memory.real address = s.memory.real address := by
    rw [dc _ (ha.trans (slot_lt_slot n base 5 7 (by decide))),
      db _ (ha.trans (slot_lt_slot n base 5 6 (by decide))), da _ ha]
  have hD : inputWeights n base next = inputWeights n base s :=
    funext (fun edge => hlow _ (weight_before_slot _ _ _ _ (by decide) edge))
  have hlam : inputLambda n base next = inputLambda n base s := hlow _ (slot_lt_slot _ _ _ _ (by decide))
  have hbound : inputBound n base next = inputBound n base s :=
    hlow _ (scalar_before_slot _ _ _ _ 1 (by decide) (by have hs := stride_bounds n; omega))
  have hrun : (body n base).execute tapes s =
      if c.memory.boolean (slot n base 4) then (separate n base).execute tapes next else (inside n base).execute tapes next := rfl
  rw [hrun]
  cases hp : MatrixElimination.totalPSD (SDPCoordinates.slack (inputPoint n base s)) with
  | none =>
      have hf : c.memory.boolean (slot n base 4) = false := by
        by_cases hf : c.memory.boolean (slot n base 4) = true
        · simp only [psdResult, hf, ite_true, hp] at hC
          cases hC
        · exact Bool.eq_false_of_not_eq_true hf
      simp only [hf, Bool.false_eq_true, ite_false]
      have hfeasible : readMatrix n (slot n base 5) next.memory ∈ feasible n := by
        rw [hX]
        exact (SDPCoordinates.slack_posSemidef_iff _).mp
          ((MatrixElimination.totalPSD_none _ (SDPCoordinates.slack_hermitian _)).mp hp)
      rw [inside_value tapes next n base hn hfeasible, hX, hD, hlam, hbound]
      simp only [bodyReply, hp, Option.elim_none]
  | some v =>
      have hf : c.memory.boolean (slot n base 4) = true := by
        by_cases hf : c.memory.boolean (slot n base 4) = true
        · exact hf
        · have hf' := Bool.eq_false_of_not_eq_true hf
          simp only [psdResult, hf', Bool.false_eq_true, ite_false, hp] at hC
          cases hC
      have hv : readVector n (slot n base 7) next.memory = v := by
        simpa only [psdResult, hf, ite_true, hp, Option.some.injEq] using hC
      simp only [hf, Bool.true_eq, ite_true]
      rw [separate_value, hv]
      simp only [bodyReply, hp, Option.elim_some]

theorem oracleProgram_value (tapes : Tapes) (s : State) (n base : ℕ) (hn : 2 ≤ n) :
    reply n base ((oracleProgram n base).execute tapes s) =
      SDPCoordinates.answer MatrixElimination.primitives (inputLambda n base s) (inputBound n base s)
        (inputWeights n base s, inputPoint n base s) := by
  let first := (coordinateNormProgram n (slot n base 1) (slot n base 11 + 1)).execute tapes s
  let condition := Expr.lt (.mul (.rational 2) (.cast (.natural n))) (readReal (slot n base 11 + 1))
  let next := first.tick (condition.operations + 1)
  have hnorm : first.memory.real (slot n base 11 + 1) = ‖inputPoint n base s‖ :=
    coordinateNorm_value _ _ _ _ _ (fun ij => by have h := matrix_before_slot n base 1 11 (by decide) ij; omega)
  have hlow (address : ℕ) (ha : address < slot n base 3) : next.memory.real address = s.memory.real address := by
    change ((writeReal (slot n base 11 + 1) (.sqrt (readReal (slot n base 11 + 1)))).execute tapes _).memory.real address = _
    have hd : address ≠ slot n base 11 + 1 := by have h := slot_lt_slot n base 3 11 (by decide); omega
    rw [writeReal_frame _ _ _ _ _ hd]
    exact sumProgram_frame _ _ _ _ _ hd
  have hpoint : inputPoint n base next = inputPoint n base s := by
    ext ij
    exact hlow _ (matrix_before_slot _ _ _ _ (by decide) ij)
  have hD : inputWeights n base next = inputWeights n base s :=
    funext (fun edge => hlow _ (weight_before_slot _ _ _ _ (by decide) edge))
  have hlam : inputLambda n base next = inputLambda n base s := hlow _ (slot_lt_slot _ _ _ _ (by decide))
  have hbound : inputBound n base next = inputBound n base s :=
    hlow _ (scalar_before_slot _ _ _ _ 1 (by decide) (by have hs := stride_bounds n; omega))
  have hcond : condition.eval first.memory = decide (2 * (n : ℝ) < ‖inputPoint n base s‖) := by
    simp only [condition, Expr.eval, readReal, Rat.cast_ofNat, hnorm]
  change reply n base (if condition.eval first.memory then (outside n base).execute tapes next else (body n base).execute tapes next) = _
  rw [hcond]
  unfold SDPCoordinates.answer
  by_cases ho : 2 * (n : ℝ) < ‖inputPoint n base s‖
  · simp only [ho, decide_true, Bool.true_eq, ite_true]
    rw [outside_value, hpoint]
  · simp only [ho, decide_false, Bool.false_eq_true, ite_false]
    rw [body_value _ _ _ _ hn, hpoint, hD, hlam, hbound]
    rfl

theorem oracleProgram_correct (tapes : Tapes) (s : State) (n base : ℕ) (hn : 2 ≤ n)
    (hlam : 0 ≤ inputLambda n base s) (hB : 0 ≤ inputBound n base s) :
    LSW.CorrectReply (SDPCoordinates.problem hn hlam hB) (inputWeights n base s) (inputPoint n base s)
      (reply n base ((oracleProgram n base).execute tapes s)) := by
  rw [oracleProgram_value _ _ _ _ hn]
  exact SDPCoordinates.answer_correct hn hlam hB MatrixElimination.primitives _ _

end DPCut.RealMachine.SDP
