import DPCut.RealMachineSearch

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

theorem state_ext {m : ℕ} {a b : EllipsoidOptimization.State m}
    (hbest : a.best = b.best) (hlower : a.lower = b.lower) (hupper : a.upper = b.upper) : a = b := by
  cases a
  cases b
  simp_all

def OptimizerContext (n base : ℕ) (lam B epsilon : ℝ) (D : Weights n) (s : State) : Prop :=
  SDP.inputWeights n (TargetCode.workspace n base) s = D ∧
    SDP.inputLambda n (TargetCode.workspace n base) s = lam ∧
    SDP.inputBound n (TargetCode.workspace n base) s = B ∧ s.memory.real (epsilonAddress n base) = epsilon

theorem successProgram_state (n base : ℕ) (tapes : Tapes) (s : State) :
    searchState n base ((successProgram n base).execute tapes s) =
      ⟨center (n*n) base s, s.memory.real (thresholdAddress n base), s.memory.real (upperAddress n base)⟩ := by
  let first := (arrayProgram (vectorAddress (bestAddress n base)) (fun i : Fin (n*n) =>
    readReal (vectorAddress (slot (n*n) base 0) i))).execute tapes s
  have hs := stride_bounds (n*n)
  have hv := arrayProgram_value tapes s (vectorAddress (bestAddress n base))
    (fun i : Fin (n*n) => readReal (vectorAddress (slot (n*n) base 0) i))
    (vectorAddress_injective _) (fun i j => realFrame_read _ _ (by
      have hi := vector_before_slot (n*n) base 0 15 (by decide) i
      have ho := (vector_range (bestAddress n base) j).1
      unfold bestAddress at *
      omega))
  have hthreshold : first.memory.real (thresholdAddress n base) = s.memory.real (thresholdAddress n base) :=
    arrayProgram_frame _ _ _ _ _ (fun i => by
      have hi := slot_lt_slot (n*n) base 13 15 (by decide)
      have ho := (vector_range (bestAddress n base) i).1
      unfold thresholdAddress bestAddress at *
      omega)
  have hupper : first.memory.real (upperAddress n base) = s.memory.real (upperAddress n base) :=
    arrayProgram_frame _ _ _ _ _ (fun i => by
      have hi := scalar_before_slot (n*n) base 12 15 1 (by decide) (by omega)
      have ho := (vector_range (bestAddress n base) i).1
      unfold upperAddress lowerAddress bestAddress at *
      omega)
  apply state_ext
  · ext i
    change ((writeReal (lowerAddress n base) (readReal (thresholdAddress n base))).execute tapes first).memory.real
      (vectorAddress (bestAddress n base) i) = s.memory.real (vectorAddress (slot (n*n) base 0) i)
    rw [writeReal_frame _ _ _ _ _ (by
      have hi := slot_lt_slot (n*n) base 12 15 (by decide)
      have ho := (vector_range (bestAddress n base) i).1
      unfold lowerAddress bestAddress at *
      omega)]
    exact hv i
  · change ((writeReal (lowerAddress n base) (readReal (thresholdAddress n base))).execute tapes first).memory.real
      (lowerAddress n base) = _
    rw [writeReal_value]
    exact hthreshold
  · change ((writeReal (lowerAddress n base) (readReal (thresholdAddress n base))).execute tapes first).memory.real
      (upperAddress n base) = _
    rw [writeReal_frame _ _ _ _ _ (by unfold upperAddress; omega)]
    exact hupper

theorem failureUpperExpr_value (n base : ℕ) (s : State) :
    (failureUpperExpr n base).eval s.memory =
      min (s.memory.real (upperAddress n base)) (s.memory.real (thresholdAddress n base) + s.memory.real (epsilonAddress n base)/4) := by
  simp only [failureUpperExpr, Expr.eval, readReal, Rat.cast_ofNat, decide_eq_true_eq]
  split_ifs <;> simp_all [min_def]

theorem failureProgram_state (n base : ℕ) (tapes : Tapes) (s : State) :
    searchState n base ((failureProgram n base).execute tapes s) =
      ⟨(searchState n base s).best, (searchState n base s).lower,
        min ((searchState n base s).upper) (s.memory.real (thresholdAddress n base) + s.memory.real (epsilonAddress n base)/4)⟩ := by
  apply state_ext
  · ext i
    change ((writeReal (upperAddress n base) (failureUpperExpr n base)).execute tapes s).memory.real
      (vectorAddress (bestAddress n base) i) = s.memory.real _
    exact writeReal_frame _ _ _ _ _ (by
      have hi := scalar_before_slot (n*n) base 12 15 1 (by decide) (by have hs := stride_bounds (n*n); omega)
      have ho := (vector_range (bestAddress n base) i).1
      unfold upperAddress lowerAddress bestAddress at *
      omega)
  · change ((writeReal (upperAddress n base) (failureUpperExpr n base)).execute tapes s).memory.real
      (lowerAddress n base) = s.memory.real (lowerAddress n base)
    exact writeReal_frame tapes s (upperAddress n base) (lowerAddress n base) _ (by unfold upperAddress; omega)
  · change ((writeReal (upperAddress n base) (failureUpperExpr n base)).execute tapes s).memory.real
      (upperAddress n base) = _
    rw [writeReal_value]
    exact failureUpperExpr_value _ _ _

theorem post_context (n base : ℕ) (lam B threshold : ℝ) (D : Weights n) (tapes : Tapes) (s : State)
    (hs : TargetCode.Context n base lam B threshold D s) (success : Bool) :
    TargetCode.Context n base lam B threshold D
      ((if success then successProgram n base else failureProgram n base).execute tapes s) := by
  have hctx (code : Code) (hf : code.RealWriteCeiling (TargetCode.workspace n base))
      (ht : Code.PreservesReal (thresholdAddress n base) code) :
      TargetCode.Context n base lam B threshold D (code.execute tapes s) := by
    have hdata (address : ℕ) (ha : TargetCode.workspace n base ≤ address) :=
      Code.realWriteCeiling_frame code _ hf tapes s address ha
    have hW : SDP.inputWeights n (TargetCode.workspace n base) (code.execute tapes s) = SDP.inputWeights n (TargetCode.workspace n base) s := by
      funext edge
      exact hdata _ (by unfold slot weightAddress; omega)
    have hL := hdata (slot n (TargetCode.workspace n base) 2) (by unfold slot; omega)
    have hB := hdata (slot n (TargetCode.workspace n base) 2 + 1) (by unfold slot; omega)
    have hT := ht tapes s
    exact ⟨hW.trans hs.1,hL.trans hs.2.1,hB.trans hs.2.2.1,hT.trans hs.2.2.2⟩
  cases success
  · refine hctx _ (ceiling_writeReal _ _ _ (scalar_before_slot _ _ _ _ 1 (by decide) (by have h := stride_bounds (n*n); omega))) ?_
    intro tapes state
    exact writeReal_frame _ _ _ _ _ (by
      have h := scalar_before_slot (n*n) base 12 13 1 (by decide) (by have h := stride_bounds (n*n); omega)
      unfold upperAddress lowerAddress thresholdAddress at *
      omega)
  · refine hctx _ ⟨ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)),
      ceiling_writeReal _ _ _ (TargetCode.workspace_after _ _ _ (by decide))⟩ ?_
    intro tapes state
    change ((writeReal (lowerAddress n base) (readReal (thresholdAddress n base))).execute tapes _).memory.real
      (thresholdAddress n base) = _
    rw [writeReal_frame _ _ _ _ _ (by
      have h := slot_lt_slot (n*n) base 12 13 (by decide)
      unfold lowerAddress thresholdAddress at *
      omega)]
    exact arrayProgram_frame _ _ _ _ _ (fun i => by
      have h := slot_lt_slot (n*n) base 13 15 (by decide)
      have ho := (vector_range (bestAddress n base) i).1
      unfold bestAddress thresholdAddress at *
      omega)

end DPCut.RealMachine.EllipsoidCode
