import DPCut.RealMachineSDPOracle

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

open Matrix

namespace DPCut.RealMachine.SDP

theorem inside_value (tapes : Tapes) (s : State) (n base : ℕ) (hn : 2 ≤ n)
    (hX : readMatrix n (slot n base 5) s.memory ∈ feasible n) :
    reply n base ((inside n base).execute tapes s) =
      .inr (objective (inputLambda n base s)
          (boundedObjective (inputBound n base s) (inputWeights n base s))
          (readMatrix n (slot n base 5) s.memory),
        SDPCoordinates.normal n
          (objectiveMatrix (boundedObjective (inputBound n base s) (inputWeights n base s)) +
            inputLambda n base s • (readMatrix n (slot n base 5) s.memory)⁻¹)) := by
  let a := (inverseProgram n (slot n base 5) (slot n base 8) (slot n base 12)).execute tapes s
  let b := (determinantProgram n (slot n base 5) (slot n base 11) (slot n base 12)).execute tapes a
  let c := (l1Program n (slot n base 0) (slot n base 11 + 2)).execute tapes b
  let d := (boundedWeightsProgram n (slot n base 0) (slot n base 10) (slot n base 2 + 1) (slot n base 11 + 2)).execute tapes c
  let e := (matrixObjectiveProgram n (slot n base 10) (slot n base 9)).execute tapes d
  let f := (gradientNormalProgram n (slot n base 9) (slot n base 8) (slot n base 2) (slot n base 3)).execute tapes e
  let g := (queryPairProgram n (slot n base 10) (slot n base 5) (slot n base 4)).execute tapes f
  let h := (writeReal (slot n base 4) (.add (readReal (slot n base 4))
    (.mul (readReal (slot n base 2)) (.log (readReal (slot n base 11)))))).execute tapes g
  have hs := stride_bounds n
  have da (address : ℕ) (haddr : address < slot n base 8) : a.memory.real address = s.memory.real address :=
    inverseLoop_below tapes s n (slot n base 5) (slot n base 8) (slot n base 12) address (List.finRange n)
      haddr (haddr.trans (slot_lt_slot _ _ _ _ (by decide)))
  have db (address : ℕ) (haddr : address < slot n base 11) : b.memory.real address = a.memory.real address :=
    determinantProgram_frame tapes a n (slot n base 5) (slot n base 11) (slot n base 12) address
      haddr.ne (haddr.trans (slot_lt_slot _ _ _ _ (by decide)))
  have dc (address : ℕ) (haddr : address ≠ slot n base 11 + 2) : c.memory.real address = b.memory.real address :=
    sumProgram_frame tapes b _ _ _ haddr
  have dd (address : ℕ) (haddr : ∀ k : Fin (Fintype.card (Edge n)), address ≠ slot n base 10 + k.val) :
      d.memory.real address = c.memory.real address := arrayProgram_frame tapes c _ _ address haddr
  have de (address : ℕ) (haddr : ∀ ij : Fin n × Fin n, address ≠ matrixAddress (slot n base 9) ij) :
      e.memory.real address = d.memory.real address := matrixSumProgram_frame tapes d n _ _ address _ haddr
  have df (address : ℕ) (haddr : ∀ ij : Fin n × Fin n, address ≠ matrixAddress (slot n base 3) ij) :
      f.memory.real address = e.memory.real address := matrixMap_frame tapes e n _ address _ haddr
  have dg (address : ℕ) (haddr : address ≠ slot n base 4) : g.memory.real address = f.memory.real address :=
    sumProgram_frame tapes f _ _ address haddr
  have dc_low (address : ℕ) (ha : address < slot n base 8) : c.memory.real address = s.memory.real address := by
    rw [dc _ (by have hl := slot_lt_slot n base 8 11 (by decide); omega), db _ (ha.trans (slot_lt_slot _ _ _ _ (by decide))), da _ ha]
  have dd_low (address : ℕ) (ha : address < slot n base 8) : d.memory.real address = s.memory.real address := by
    rw [dd _ (by intro k; have hl := slot_lt_slot n base 8 10 (by decide); omega), dc_low _ ha]
  have de_low (address : ℕ) (ha : address < slot n base 8) : e.memory.real address = s.memory.real address := by
    rw [de _ (by intro ij; have hl := (matrix_range (slot n base 9) ij).1; have hh := slot_lt_slot n base 8 9 (by decide); omega),
      dd_low _ ha]
  have df_low (address : ℕ) (ha : address < slot n base 3) : f.memory.real address = s.memory.real address := by
    rw [df _ (by intro ij; have hl := (matrix_range (slot n base 3) ij).1; omega),
      de_low _ (ha.trans (slot_lt_slot _ _ _ _ (by decide)))]
  have hI : readMatrix n (slot n base 8) a.memory = (readMatrix n (slot n base 5) s.memory)⁻¹ := by
    rw [inverseProgram_value _ _ _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))
      (matrix_before_slot _ _ _ _ (by decide)) (matrix_disjoint _ _ _ _ (by decide))]
    exact MatrixElimination.inverse_eq _ (feasible_posDef hn hX)
  have hXb : readMatrix n (slot n base 5) a.memory = readMatrix n (slot n base 5) s.memory :=
    funext (fun i => funext (fun j => da _ (matrix_before_slot _ _ _ _ (by decide) (i,j))))
  have hdet : b.memory.real (slot n base 11) = (readMatrix n (slot n base 5) s.memory).det := by
    rw [determinantProgram_value _ _ _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))
      (slot_lt_slot _ _ _ _ (by decide)) (fun ij => (matrix_before_slot _ _ _ _ (by decide) ij).ne), hXb]
    exact MatrixElimination.determinant_correct _ (feasible_posDef hn hX)
  have hDc : readWeights n (slot n base 0) c.memory = inputWeights n base s :=
    funext (fun edge => dc_low _ (weight_before_slot _ _ _ _ (by decide) edge))
  have hDb : readWeights n (slot n base 0) b.memory = inputWeights n base s := by
    funext edge
    exact (db _ (weight_before_slot _ _ _ _ (by decide) edge)).trans (da _ (weight_before_slot _ _ _ _ (by decide) edge))
  have hl1 : c.memory.real (slot n base 11 + 2) = l1 (readWeights n (slot n base 0) c.memory) := by
    rw [l1Program_value _ _ _ _ _ (fun edge => by
      have hi := weight_before_slot n base 0 11 (by decide) edge
      omega), hDb, hDc]
  have hBound : c.memory.real (slot n base 2 + 1) = inputBound n base s :=
    dc_low _ (scalar_before_slot _ _ _ _ 1 (by decide) (by omega))
  have hD : readWeights n (slot n base 10) d.memory = boundedObjective (inputBound n base s) (inputWeights n base s) := by
    rw [boundedWeights_value _ _ _ _ _ _ _ (by
      intro edge other
      have hi := weight_before_slot n base 0 10 (by decide) edge
      have ho := (weight_range (slot n base 10) other).1
      omega) (by
      intro edge
      have hi := scalar_before_slot n base 2 10 1 (by decide) (by omega)
      have ho := (weight_range (slot n base 10) edge).1
      omega) (by
      intro edge
      have hi := weight_before_slot n base 10 11 (by decide) edge
      omega) hl1, hBound, hDc]
  have hA : readMatrix n (slot n base 9) e.memory = objectiveMatrix (boundedObjective (inputBound n base s) (inputWeights n base s)) := by
    rw [matrixObjective_value _ _ _ _ _ (by
      intro edge ij
      have hi := (weight_range (slot n base 10) edge).1
      have ho := matrix_before_slot n base 9 10 (by decide) ij
      omega), hD]
  have hIe : readMatrix n (slot n base 8) e.memory = (readMatrix n (slot n base 5) s.memory)⁻¹ := by
    funext i j
    change e.memory.real (matrixAddress (slot n base 8) (i,j)) = _
    have hi := matrix_before_slot n base 8 9 (by decide) (i,j)
    rw [de _ (fun ij => by have h := (matrix_range (slot n base 9) ij).1; omega),
      dd _ (by intro k; have h := slot_lt_slot n base 9 10 (by decide); omega),
      dc _ (by have h := slot_lt_slot n base 9 11 (by decide); omega),
      db _ (matrix_before_slot _ _ _ _ (by decide) (i,j))]
    exact congrFun (congrFun hI i) j
  have hlamE : e.memory.real (slot n base 2) = inputLambda n base s :=
    de_low _ (slot_lt_slot _ _ _ _ (by decide))
  have hnormal : readCoordinates n (slot n base 3) f.memory =
      SDPCoordinates.normal n (objectiveMatrix (boundedObjective (inputBound n base s) (inputWeights n base s)) +
        inputLambda n base s • (readMatrix n (slot n base 5) s.memory)⁻¹) := by
    rw [gradientNormal_value _ _ _ _ _ _ _ (matrix_disjoint _ _ _ _ (by decide))
      (matrix_disjoint _ _ _ _ (by decide)) (by
        intro ij
        have hi := slot_lt_slot n base 2 3 (by decide)
        have ho := (matrix_range (slot n base 3) ij).1
        omega), hA, hIe, hlamE]
  have hDf : readWeights n (slot n base 10) f.memory = boundedObjective (inputBound n base s) (inputWeights n base s) := by
    funext edge
    change f.memory.real (weightAddress (slot n base 10) edge) = _
    have hi := (weight_range (slot n base 10) edge).1
    rw [df _ (by intro ij; have ho := matrix_before_slot n base 3 10 (by decide) ij; omega),
      de _ (by intro ij; have ho := matrix_before_slot n base 9 10 (by decide) ij; omega)]
    exact congrFun hD edge
  have hXf : readMatrix n (slot n base 5) f.memory = readMatrix n (slot n base 5) s.memory := by
    funext i j
    change f.memory.real (matrixAddress (slot n base 5) (i,j)) = s.memory.real _
    rw [df _ (by
      intro ij
      exact matrix_disjoint n base 5 3 (by decide) (i,j) ij),
      de_low _ (matrix_before_slot _ _ _ _ (by decide) (i,j))]
  have hpair : g.memory.real (slot n base 4) =
      pairing (boundedObjective (inputBound n base s) (inputWeights n base s)) (fractionalQuery (readMatrix n (slot n base 5) s.memory)) := by
    have hw (edge : Edge n) : weightAddress (slot n base 10) edge ≠ slot n base 4 := by
      have hi := (weight_range (slot n base 10) edge).1
      have ho := slot_lt_slot n base 4 10 (by decide)
      omega
    have hm (ij : Fin n × Fin n) : matrixAddress (slot n base 5) ij ≠ slot n base 4 := by
      have hi := (matrix_range (slot n base 5) ij).1
      have ho := slot_lt_slot n base 4 5 (by decide)
      omega
    rw [queryPair_value _ _ _ _ _ _ hw hm, hDf, hXf]
  have hlamG : g.memory.real (slot n base 2) = inputLambda n base s := by
    rw [dg _ (slot_lt_slot n base 2 4 (by decide)).ne, df_low _ (slot_lt_slot _ _ _ _ (by decide))]
    rfl
  have hdetG : g.memory.real (slot n base 11) = (readMatrix n (slot n base 5) s.memory).det := by
    rw [dg _ (slot_lt_slot n base 4 11 (by decide)).ne',
      df _ (by intro ij; exact (matrix_before_slot n base 3 11 (by decide) ij).ne'),
      de _ (by intro ij; exact (matrix_before_slot n base 9 11 (by decide) ij).ne'),
      dd _ (by
        intro k
        have hk := k.isLt
        have hm : Fintype.card (Edge n) ≤ n * n := by have h := twice_card_edge_le_square n; nlinarith
        have ho := slot_order n base 10 11 (by decide)
        omega), dc _ (by omega)]
    exact hdet
  have hvalue : h.memory.real (slot n base 4) =
      objective (inputLambda n base s) (boundedObjective (inputBound n base s) (inputWeights n base s))
        (readMatrix n (slot n base 5) s.memory) := by
    rw [writeReal_value]
    simp only [Expr.eval, readReal, hpair, hlamG, hdetG, objective]
  have hnormalH : readCoordinates n (slot n base 3) h.memory = readCoordinates n (slot n base 3) f.memory := by
    ext ij
    have ha := matrix_before_slot n base 3 4 (by decide) ij
    change h.memory.real (matrixAddress (slot n base 3) ij) = f.memory.real _
    rw [writeReal_frame _ _ _ _ _ ha.ne, dg _ ha.ne]
  change reply n base ((writeBoolean (slot n base 4) (.boolean true)).execute tapes h) = _
  simp only [reply, writeBoolean, Code.execute, Memory.writeBoolean, Expr.eval, Function.update_self,
    Bool.true_eq, ite_true]
  change Sum.inr (h.memory.real (slot n base 4), readCoordinates n (slot n base 3) h.memory) = _
  rw [hvalue, hnormalH, hnormal]

end DPCut.RealMachine.SDP
