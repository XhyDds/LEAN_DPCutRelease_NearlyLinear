import DPCut.RealMachineSearchData

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

theorem post_epsilon (n base : ℕ) (tapes : Tapes) (s : State) (success : Bool) :
    ((if success then successProgram n base else failureProgram n base).execute tapes s).memory.real (epsilonAddress n base) =
      s.memory.real (epsilonAddress n base) := by
  have hs := stride_bounds (n*n)
  have hsLarge : 3 ≤ stride (n*n) := by
    have hp : 0 < (n*n + 1) ^ 2 := by positivity
    unfold stride
    omega
  cases success
  · exact writeReal_frame _ _ _ _ _ (by unfold epsilonAddress upperAddress; omega)
  · change ((writeReal (lowerAddress n base) (readReal (thresholdAddress n base))).execute tapes _).memory.real _ = _
    rw [writeReal_frame _ _ _ _ _ (by unfold epsilonAddress; omega)]
    exact arrayProgram_frame _ _ _ _ _ (fun i => by
      have hi := scalar_before_slot (n*n) base 12 15 2 (by decide) (by omega)
      have ho := (vector_range (bestAddress n base) i).1
      unfold epsilonAddress lowerAddress bestAddress at *
      omega)

theorem searchStep_valid {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) (D : Weights n)
    (tapes : Tapes) (s : State) (hctx : OptimizerContext n base lam B epsilon D s)
    (hvalid : (searchState n base s).Valid (SDPFlat.problem hn hlam hB) D) :
    let output := (searchStep n base (iterations hn lam B epsilon hlam hB)).execute tapes s
    OptimizerContext n base lam B epsilon D output ∧
      (searchState n base output).Valid (SDPFlat.problem hn hlam hB) D ∧
      (searchState n base output).width ≤ (searchState n base s).width/2 + epsilon/4 := by
  let P := SDPFlat.problem hn hlam hB
  let mid := ((searchState n base s).lower + (searchState n base s).upper)/2
  let a := (writeReal (thresholdAddress n base) (midpointExpr n base)).execute tapes s
  let b := (checkCode n base (iterations hn lam B epsilon hlam hB)).execute tapes a
  let next := b.tick ((readBoolean (slot (n*n) base 14)).operations + 1)
  have hs := stride_bounds (n*n)
  have hsLarge : 3 ≤ stride (n*n) := by
    have hp : 0 < (n*n + 1) ^ 2 := by positivity
    unfold stride
    omega
  have hmid : a.memory.real (thresholdAddress n base) = mid := writeReal_value _ _ _ _
  have hA : TargetCode.Context n base lam B mid D a := by
    have hw : thresholdAddress n base < TargetCode.workspace n base := TargetCode.workspace_after _ _ _ (by decide)
    refine ⟨?_, ?_, ?_, hmid⟩
    · rw [← hctx.1]
      funext edge
      exact writeReal_frame _ _ _ _ _ (by
        have hi := (weight_range (slot n (TargetCode.workspace n base) 0) edge).1
        have hzero : slot n (TargetCode.workspace n base) 0 = TargetCode.workspace n base := by simp [slot]
        rw [hzero] at hi
        change weightAddress (TargetCode.workspace n base) edge ≠ thresholdAddress n base
        omega)
    · exact (writeReal_frame _ _ _ _ _ (by
        have hi : TargetCode.workspace n base ≤ slot n (TargetCode.workspace n base) 2 := by unfold slot; omega
        omega)).trans hctx.2.1
    · exact (writeReal_frame _ _ _ _ _ (by
        have hi : TargetCode.workspace n base ≤ slot n (TargetCode.workspace n base) 2 + 1 := by unfold slot; omega
        omega)).trans hctx.2.2.1
  have hBctx := checkCode_context base hn lam B mid epsilon hlam hB D tapes a hA
  have hBcorrect := checkCode_correct base hn lam B mid epsilon hlam hB D tapes a hA he hehalf
  have hprotected (address : ℕ) (hlo : lowerAddress n base ≤ address) (hhi : address < TargetCode.workspace n base) :
      b.memory.real address = a.memory.real address :=
    checkCode_protected n base address _ hlo hhi tapes a
  have hlower : b.memory.real (lowerAddress n base) = (searchState n base s).lower := by
    rw [hprotected _ le_rfl (TargetCode.workspace_after _ _ _ (by decide))]
    exact writeReal_frame _ _ _ _ _ (by
      have h := slot_lt_slot (n*n) base 12 13 (by decide)
      unfold lowerAddress thresholdAddress at *
      omega)
  have hupper : b.memory.real (upperAddress n base) = (searchState n base s).upper := by
    have hi := scalar_before_slot (n*n) base 12 16 1 (by decide) (by omega)
    rw [hprotected (upperAddress n base) (by unfold upperAddress; omega) (by simpa [upperAddress,lowerAddress] using hi)]
    exact writeReal_frame _ _ _ _ _ (by
      have h := scalar_before_slot (n*n) base 12 13 1 (by decide) (by omega)
      unfold upperAddress lowerAddress thresholdAddress at *
      omega)
  have heps : b.memory.real (epsilonAddress n base) = epsilon := by
    have hi := scalar_before_slot (n*n) base 12 16 2 (by decide) (by omega)
    rw [hprotected (epsilonAddress n base) (by unfold epsilonAddress; omega) (by simpa [epsilonAddress,lowerAddress] using hi)]
    exact (writeReal_frame _ _ _ _ _ (by
      have h := scalar_before_slot (n*n) base 12 13 2 (by decide) (by omega)
      unfold epsilonAddress lowerAddress thresholdAddress at *
      omega)).trans hctx.2.2.2
  have hthreshold : b.memory.real (thresholdAddress n base) = mid := hBctx.2.2.2
  have hbest : (searchState n base next).best = (searchState n base s).best := by
    ext i
    have hlo : lowerAddress n base ≤ vectorAddress (bestAddress n base) i := by
      have hi := slot_lt_slot (n*n) base 12 15 (by decide)
      have ho := (vector_range (bestAddress n base) i).1
      unfold lowerAddress bestAddress at *
      omega
    have hhi := vector_before_slot (n*n) base 15 16 (by decide) i
    change b.memory.real (vectorAddress (bestAddress n base) i) = _
    rw [hprotected _ hlo hhi]
    exact writeReal_frame _ _ _ _ _ (by
      have hi := slot_lt_slot (n*n) base 13 15 (by decide)
      have ho := (vector_range (bestAddress n base) i).1
      unfold thresholdAddress bestAddress at *
      omega)
  have hnext : TargetCode.Context n base lam B mid D next := hBctx
  have hrun : (searchStep n base (iterations hn lam B epsilon hlam hB)).execute tapes s =
      (if b.memory.boolean (slot (n*n) base 14) then successProgram n base else failureProgram n base).execute tapes next := by
    change (if b.memory.boolean (slot (n*n) base 14) then (successProgram n base).execute tapes next
      else (failureProgram n base).execute tapes next) = _
    split <;> rfl
  dsimp only
  rw [hrun]
  have hpost := post_context n base lam B mid D tapes next hnext (b.memory.boolean (slot (n*n) base 14))
  have hpostE := post_epsilon n base tapes next (b.memory.boolean (slot (n*n) base 14))
  refine ⟨⟨hpost.1,hpost.2.1,hpost.2.2.1,hpostE.trans heps⟩, ?_⟩
  by_cases hf : b.memory.boolean (slot (n*n) base 14) = true
  · have hx : center (n*n) base b ∈ EllipsoidOptimization.target P D mid :=
      hBcorrect.1 _ (by
        change (if b.memory.boolean (slot (n*n) base 14) then some (center (n*n) base b) else none) = _
        rw [hf]
        rfl)
    simp only [hf, ite_true]
    rw [successProgram_state]
    refine ⟨⟨hx.1, ?_, ?_⟩, ?_⟩
    · change b.memory.real (thresholdAddress n base) ≤ P.value D (center (n*n) base b)
      rw [hthreshold]
      exact hx.2
    · intro y hy
      exact (hvalid.2.2 y hy).trans_eq hupper.symm
    · change b.memory.real (upperAddress n base) - b.memory.real (thresholdAddress n base) ≤ _
      rw [hupper, hthreshold]
      unfold mid EllipsoidOptimization.State.width
      linarith
  · have hf' := Bool.eq_false_of_not_eq_true hf
    have hfailure : ∀ y ∈ P.body, P.value D y < mid + epsilon/4 :=
      hBcorrect.2 (by
        change (if b.memory.boolean (slot (n*n) base 14) then some (center (n*n) base b) else none) = none
        rw [hf']
        rfl)
    simp only [hf', Bool.false_eq_true, ite_false]
    rw [failureProgram_state]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · change (searchState n base next).best ∈ P.body
      rw [hbest]
      exact hvalid.1
    · change (searchState n base next).lower ≤ P.value D (searchState n base next).best
      rw [hbest]
      change b.memory.real (lowerAddress n base) ≤ P.value D (searchState n base s).best
      rw [hlower]
      exact hvalid.2.1
    · intro y hy
      exact le_min ((hvalid.2.2 y hy).trans_eq hupper.symm) (by
        change P.value D y ≤ b.memory.real (thresholdAddress n base) + b.memory.real (epsilonAddress n base)/4
        rw [hthreshold, heps]
        exact (hfailure y hy).le)
    · have hmin := min_le_right (b.memory.real (upperAddress n base))
        (b.memory.real (thresholdAddress n base) + b.memory.real (epsilonAddress n base)/4)
      change min (b.memory.real (upperAddress n base))
        (b.memory.real (thresholdAddress n base) + b.memory.real (epsilonAddress n base)/4) -
          b.memory.real (lowerAddress n base) ≤ _
      rw [hlower,hthreshold,heps]
      rw [hthreshold, heps] at hmin
      unfold mid at hmin ⊢
      unfold EllipsoidOptimization.State.width
      linarith

end DPCut.RealMachine.EllipsoidCode
