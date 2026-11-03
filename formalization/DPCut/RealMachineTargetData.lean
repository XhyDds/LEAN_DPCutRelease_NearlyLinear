import DPCut.RealMachineTargetOracle

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.TargetCode

open SDP EllipsoidCode

theorem copyPoint_value (tapes : Tapes) (s : State) (n base : ℕ) :
    SDPFlat.equiv n (SDP.inputPoint n (workspace n base) ((copyPoint n base).execute tapes s)) =
      EllipsoidCode.center (n*n) base s := by
  have hv := matrixMap_value tapes s n (slot n (workspace n base) 1)
    (fun ij => readReal (vectorAddress (slot (n*n) base 0) (finProdFinEquiv ij))) (by
      intro ij kl
      have hi := vector_before_slot (n*n) base 0 16 (by decide) (finProdFinEquiv ij)
      have ho := (matrix_range (slot n (workspace n base) 1) kl).1
      have hh : workspace n base ≤ slot n (workspace n base) 1 := by unfold slot; omega
      exact realFrame_read _ _ (by change _ ≠ _; unfold workspace at *; omega))
  ext k
  change ((copyPoint n base).execute tapes s).memory.real
    (matrixAddress (slot n (workspace n base) 1) (finProdFinEquiv.symm k)) =
      s.memory.real (vectorAddress (slot (n*n) base 0) k)
  have h := hv (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  simpa only [copyPoint, Expr.eval, readReal, Prod.mk.eta, finProdFinEquiv.apply_symm_apply] using h

theorem copyNormal_value (tapes : Tapes) (s : State) (n base : ℕ) (negative : Bool) :
    EllipsoidCode.normal (n*n) base ((copyNormal n base negative).execute tapes s) =
      if negative then -(SDPFlat.equiv n (readCoordinates n (slot n (workspace n base) 3) s.memory))
      else SDPFlat.equiv n (readCoordinates n (slot n (workspace n base) 3) s.memory) := by
  have hv := arrayProgram_value tapes s (vectorAddress (slot (n*n) base 2)) (copyNormalExpr n base negative)
    (vectorAddress_injective _) (by
      intro i j
      have hi := (matrix_range (slot n (workspace n base) 3) (finProdFinEquiv.symm i)).1
      have ho := vector_before_slot (n*n) base 2 16 (by decide) j
      have hh : workspace n base ≤ slot n (workspace n base) 3 := by unfold slot; omega
      have hne : matrixAddress (slot n (workspace n base) 3) (finProdFinEquiv.symm i) ≠
          vectorAddress (slot (n*n) base 2) j := by unfold workspace at *; omega
      unfold copyNormalExpr
      cases negative
      · exact realFrame_read _ _ hne
      · exact realFrame_neg (realFrame_read _ _ hne))
  ext k
  change ((copyNormal n base negative).execute tapes s).memory.real (vectorAddress (slot (n*n) base 2) k) = _
  unfold copyNormal
  rw [hv k]
  cases negative <;> rfl

theorem fixedNormal_value (tapes : Tapes) (s : State) (n base : ℕ) (hm : 1 ≤ n*n) :
    EllipsoidCode.normal (n*n) base ((fixedNormalProgram n base).execute tapes s) =
      EllipsoidOptimization.fixedNormal hm := by
  have hv := arrayProgram_value tapes s (vectorAddress (slot (n*n) base 2))
    (fun i : Fin (n*n) => Expr.rational (if i.val = 0 then 1 else 0)) (vectorAddress_injective _)
    (fun _ _ => realFrame_rational _ _)
  ext k
  have h := hv k
  change ((fixedNormalProgram n base).execute tapes s).memory.real (vectorAddress (slot (n*n) base 2) k) = _
  unfold fixedNormalProgram
  rw [h]
  by_cases hz : k.val = 0
  · have hk : k = (⟨0, by omega⟩ : Fin (n*n)) := Fin.ext hz
    simp [Expr.eval, EllipsoidOptimization.fixedNormal, hk]
  · have hk : k ≠ (⟨0, by omega⟩ : Fin (n*n)) := fun h => hz (congrArg Fin.val h)
    simp [Expr.eval, EllipsoidOptimization.fixedNormal, hz, hk]

theorem context_of_low (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (s t : State)
    (h : ∀ address < slot n (workspace n base) 3, t.memory.real address = s.memory.real address)
    (hs : Context n base lam B threshold D s) : Context n base lam B threshold D t := by
  have hweights : SDP.inputWeights n (workspace n base) t = SDP.inputWeights n (workspace n base) s :=
    funext (fun edge => h _ (weight_before_slot _ _ _ _ (by decide) edge))
  have hlambda : SDP.inputLambda n (workspace n base) t = SDP.inputLambda n (workspace n base) s :=
    h _ (slot_lt_slot _ _ _ _ (by decide))
  have hbound : SDP.inputBound n (workspace n base) t = SDP.inputBound n (workspace n base) s :=
    h _ (scalar_before_slot _ _ _ _ 1 (by decide) (by have hb := stride_bounds n; omega))
  have hthreshold : t.memory.real (slot (n*n) base 13) = s.memory.real (slot (n*n) base 13) := by
    apply h
    exact (workspace_after _ _ _ (by decide)).trans (by unfold slot; have hs := stride_bounds n; omega)
  exact ⟨hweights.trans hs.1, hlambda.trans hs.2.1, hbound.trans hs.2.2.1, hthreshold.trans hs.2.2.2⟩

theorem context_of_high (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (s t : State)
    (h : ∀ address, slot (n*n) base 3 ≤ address → t.memory.real address = s.memory.real address)
    (hs : Context n base lam B threshold D s) : Context n base lam B threshold D t := by
  have hw : slot (n*n) base 3 ≤ workspace n base := (workspace_after _ _ _ (by decide)).le
  have hweights : SDP.inputWeights n (workspace n base) t = SDP.inputWeights n (workspace n base) s := by
    funext edge
    exact h _ (hw.trans (by
      have hi := (weight_range (slot n (workspace n base) 0) edge).1
      simpa only [slot, Nat.mul_zero, Nat.add_zero] using hi))
  have hlambda : SDP.inputLambda n (workspace n base) t = SDP.inputLambda n (workspace n base) s :=
    h _ (hw.trans (by unfold slot; omega))
  have hbound : SDP.inputBound n (workspace n base) t = SDP.inputBound n (workspace n base) s :=
    h _ (hw.trans (by unfold slot; omega))
  have hthreshold := h (slot (n*n) base 13) (slot_lt_slot _ _ _ _ (by decide)).le
  exact ⟨hweights.trans hs.1, hlambda.trans hs.2.1, hbound.trans hs.2.2.1, hthreshold.trans hs.2.2.2⟩

theorem copyNormal_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (negative : Bool) (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((copyNormal n base negative).execute tapes s) := by
  refine context_of_high n base lam B threshold D s ((copyNormal n base negative).execute tapes s) ?_ hs
  intro address ha
  exact arrayProgram_frame _ _ _ _ _ (fun i => (lt_of_lt_of_le (vector_before_slot _ _ _ _ (by decide) i) ha).ne')

theorem fixedNormal_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((fixedNormalProgram n base).execute tapes s) := by
  refine context_of_high n base lam B threshold D s ((fixedNormalProgram n base).execute tapes s) ?_ hs
  intro address ha
  exact arrayProgram_frame _ _ _ _ _ (fun i => (lt_of_lt_of_le (vector_before_slot _ _ _ _ (by decide) i) ha).ne')

theorem copyPoint_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : Context n base lam B threshold D s) :
    Context n base lam B threshold D ((copyPoint n base).execute tapes s) := by
  have hW : SDP.inputWeights n (workspace n base) ((copyPoint n base).execute tapes s) = SDP.inputWeights n (workspace n base) s := by
    funext edge
    exact matrixMap_frame tapes s n _ _ _ (by
      intro ij
      have hi := weight_before_slot n (workspace n base) 0 1 (by decide) edge
      have ho := (matrix_range (slot n (workspace n base) 1) ij).1
      omega)
  have hL : SDP.inputLambda n (workspace n base) ((copyPoint n base).execute tapes s) = SDP.inputLambda n (workspace n base) s :=
    matrixMap_frame tapes s n _ _ _ (fun ij => (matrix_before_slot n (workspace n base) 1 2 (by decide) ij).ne')
  have hB : SDP.inputBound n (workspace n base) ((copyPoint n base).execute tapes s) = SDP.inputBound n (workspace n base) s := by
    apply matrixMap_frame
    intro ij
    have hi := matrix_before_slot n (workspace n base) 1 2 (by decide) ij
    omega
  have hT : ((copyPoint n base).execute tapes s).memory.real (slot (n*n) base 13) = s.memory.real (slot (n*n) base 13) :=
    Code.realWriteFloor_frame _ (workspace n base) (floor_matrixMap _ _ _ _ (by unfold slot; omega))
      tapes s _ (workspace_after _ _ _ (by decide))
  exact ⟨hW.trans hs.1,hL.trans hs.2.1,hB.trans hs.2.2.1,hT.trans hs.2.2.2⟩

end DPCut.RealMachine.TargetCode
