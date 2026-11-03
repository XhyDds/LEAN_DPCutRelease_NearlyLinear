import DPCut.RealMachineSDPFields

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.SDP

def stride (n : ℕ) : ℕ := 4 * (n + 1) ^ 2 + 32
def slot (n base index : ℕ) : ℕ := base + stride n * index

theorem stride_bounds (n : ℕ) : n * n < stride n ∧ n < stride n ∧ 2 ≤ stride n := by
  unfold stride
  ring_nf
  omega

theorem matrix_range {n : ℕ} (base : ℕ) (ij : Fin n × Fin n) :
    base ≤ matrixAddress base ij ∧ matrixAddress base ij < base + n * n := by
  have h := (finProdFinEquiv ij).isLt
  unfold matrixAddress
  omega

theorem vector_range {n : ℕ} (base : ℕ) (i : Fin n) :
    base ≤ vectorAddress base i ∧ vectorAddress base i < base + n := by
  unfold vectorAddress
  have h := i.isLt
  omega

theorem weight_range {n : ℕ} (base : ℕ) (e : Edge n) :
    base ≤ weightAddress base e ∧ weightAddress base e < base + n * n := by
  have h := ((Fintype.equivFin (Edge n)) e).isLt
  have hm : Fintype.card (Edge n) ≤ n * n := by have h := twice_card_edge_le_square n; nlinarith
  unfold weightAddress
  omega

theorem slot_order (n base k l : ℕ) (h : k < l) :
    slot n base k + n * n < slot n base l := by
  have hm := Nat.mul_le_mul_left (stride n) (Nat.succ_le_of_lt h)
  have hs := (stride_bounds n).1
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hm
  unfold slot
  omega

theorem matrix_before_slot (n base k l : ℕ) (h : k < l) (ij : Fin n × Fin n) :
    matrixAddress (slot n base k) ij < slot n base l :=
  (matrix_range _ ij).2.trans (slot_order _ _ _ _ h)

theorem vector_before_slot (n base k l : ℕ) (h : k < l) (i : Fin n) :
    vectorAddress (slot n base k) i < slot n base l := by
  have hm := Nat.mul_le_mul_left (stride n) (Nat.succ_le_of_lt h)
  have hs := (stride_bounds n).2.1
  have hv := (vector_range (slot n base k) i).2
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hm
  unfold slot at *
  omega

theorem weight_before_slot (n base k l : ℕ) (h : k < l) (e : Edge n) :
    weightAddress (slot n base k) e < slot n base l :=
  (weight_range _ e).2.trans (slot_order _ _ _ _ h)

theorem slot_lt_slot (n base k l : ℕ) (h : k < l) : slot n base k < slot n base l :=
  (Nat.le_add_right _ _).trans_lt (slot_order _ _ _ _ h)

theorem scalar_before_slot (n base k l offset : ℕ) (h : k < l) (hoff : offset < stride n) :
    slot n base k + offset < slot n base l := by
  have hm := Nat.mul_le_mul_left (stride n) (Nat.succ_le_of_lt h)
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hm
  unfold slot
  omega

theorem matrix_disjoint (n base k l : ℕ) (h : k ≠ l) (ij kl : Fin n × Fin n) :
    matrixAddress (slot n base k) ij ≠ matrixAddress (slot n base l) kl := by
  rcases lt_or_gt_of_ne h with h | h
  · exact ne_of_lt ((matrix_before_slot _ _ _ _ h ij).trans_le (matrix_range _ kl).1)
  · exact ne_of_gt ((matrix_before_slot _ _ _ _ h kl).trans_le (matrix_range _ ij).1)

def inputWeights (n base : ℕ) (s : State) := readWeights n (slot n base 0) s.memory
def inputPoint (n base : ℕ) (s : State) := readCoordinates n (slot n base 1) s.memory
def inputLambda (n base : ℕ) (s : State) := s.memory.real (slot n base 2)
def inputBound (n base : ℕ) (s : State) := s.memory.real (slot n base 2 + 1)

def reply (n base : ℕ) (s : State) : LSW.Reply (Fin n × Fin n) :=
  if s.memory.boolean (slot n base 4) then
    .inr (s.memory.real (slot n base 4), readCoordinates n (slot n base 3) s.memory)
  else .inl (readCoordinates n (slot n base 3) s.memory)

def inside (n base : ℕ) : Code :=
  .seq (inverseProgram n (slot n base 5) (slot n base 8) (slot n base 12))
    (.seq (determinantProgram n (slot n base 5) (slot n base 11) (slot n base 12))
      (.seq (l1Program n (slot n base 0) (slot n base 11 + 2))
        (.seq (boundedWeightsProgram n (slot n base 0) (slot n base 10) (slot n base 2 + 1) (slot n base 11 + 2))
          (.seq (matrixObjectiveProgram n (slot n base 10) (slot n base 9))
            (.seq (gradientNormalProgram n (slot n base 9) (slot n base 8) (slot n base 2) (slot n base 3))
              (.seq (queryPairProgram n (slot n base 10) (slot n base 5) (slot n base 4))
                (.seq (writeReal (slot n base 4)
                    (.add (readReal (slot n base 4)) (.mul (readReal (slot n base 2)) (.log (readReal (slot n base 11))))))
                  (writeBoolean (slot n base 4) (.boolean true)))))))))

def separate (n base : ℕ) : Code :=
  .seq (negativeNormalProgram n (slot n base 7) (slot n base 3))
    (writeBoolean (slot n base 4) (.boolean false))

def outside (n base : ℕ) : Code :=
  .seq (matrixMapProgram n (slot n base 3) (fun ij => readReal (matrixAddress (slot n base 1) ij)))
    (writeBoolean (slot n base 4) (.boolean false))

def body (n base : ℕ) : Code :=
  .seq (liftCoordinatesProgram n (slot n base 1) (slot n base 5))
    (.seq (slackProgram n (slot n base 5) (slot n base 6))
      (.seq (psdProgram n (slot n base 6) (slot n base 7) (slot n base 4) (slot n base 12))
        (.branch (readBoolean (slot n base 4)) (separate n base) (inside n base))))

def oracleProgram (n base : ℕ) : Code :=
  .seq (coordinateNormProgram n (slot n base 1) (slot n base 11 + 1))
    (.branch (.lt (.mul (.rational 2) (.cast (.natural n))) (readReal (slot n base 11 + 1)))
      (outside n base) (body n base))

theorem inside_steps (n base : ℕ) : Steps (inside n base) (2000 * (n + 1) ^ 6) := by
  have hi := inverseProgram_steps n (slot n base 5) (slot n base 8) (slot n base 12)
  have hd := determinantProgram_steps n (slot n base 5) (slot n base 11) (slot n base 12)
  have hl := l1Program_steps n (slot n base 0) (slot n base 11 + 2)
  have hb := boundedWeights_steps n (slot n base 0) (slot n base 10) (slot n base 2 + 1) (slot n base 11 + 2)
  have ha := matrixObjective_steps n (slot n base 10) (slot n base 9)
  have hg := gradientNormal_steps n (slot n base 9) (slot n base 8) (slot n base 2) (slot n base 3)
  have hp := queryPair_steps n (slot n base 10) (slot n base 5) (slot n base 4)
  have hv := Steps.real (.natural (slot n base 4)) (.add (readReal (slot n base 4))
    (.mul (readReal (slot n base 2)) (.log (readReal (slot n base 11)))))
  have hf := Steps.boolean (.natural (slot n base 4)) (.boolean true)
  exact (hi.seq (hd.seq (hl.seq (hb.seq (ha.seq (hg.seq (hp.seq (hv.seq hf)))))))).mono (by
    simp only [Expr.operations, readReal]
    have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h6 : 1 ≤ (n + 1) ^ 6 := by change 0 < _; positivity
    omega)

theorem oracleProgram_steps (n base : ℕ) : Steps (oracleProgram n base) (10000 * (n + 1) ^ 6) := by
  have hs := (negativeNormal_steps n (slot n base 7) (slot n base 3)).seq
    (Steps.boolean (.natural (slot n base 4)) (.boolean false))
  have ho := (matrixMap_steps n (slot n base 3) 2 (fun ij => readReal (matrixAddress (slot n base 1) ij)) (by intro ij; rfl)).seq
    (Steps.boolean (.natural (slot n base 4)) (.boolean false))
  have hb := (liftCoordinates_steps n (slot n base 1) (slot n base 5)).seq
    ((slackProgram_steps n (slot n base 5) (slot n base 6)).seq
      ((psdProgram_steps n (slot n base 6) (slot n base 7) (slot n base 4) (slot n base 12)).seq
        (Steps.branch (readBoolean (slot n base 4)) hs (inside_steps n base))))
  have h := (coordinateNorm_steps n (slot n base 1) (slot n base 11 + 1)).seq
    (Steps.branch (.lt (.mul (.rational 2) (.cast (.natural n))) (readReal (slot n base 11 + 1))) ho hb)
  exact h.mono (by
    simp only [Expr.operations, readBoolean, readReal, Nat.max_def]
    have h2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have hsquare : n * n ≤ (n + 1) ^ 6 := (by nlinarith : n * n ≤ (n + 1) ^ 2).trans h2
    have h6 : 1 ≤ (n + 1) ^ 6 := by change 0 < _; positivity
    split_ifs <;> ring_nf <;> omega)

end DPCut.RealMachine.SDP
