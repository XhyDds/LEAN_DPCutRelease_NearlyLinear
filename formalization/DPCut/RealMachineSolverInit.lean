import DPCut.RealMachineSolverSeed

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def rangeExpr (n base : ℕ) : Expr .real :=
  .add (.add (.rational 1) (.mul (.rational 2) (readReal (slot n (TargetCode.workspace n base) 2 + 1))))
    (.mul (readReal (slot n (TargetCode.workspace n base) 2)) (.cast (.natural (n*n))))

def initializeProgram (n base : ℕ) : Code :=
  .seq (seedProgram n base)
    (.seq (writeReal (thresholdAddress n base) (readReal (slot n (TargetCode.workspace n base) 4)))
      (.seq (successProgram n base)
        (writeReal (upperAddress n base) (.add (readReal (lowerAddress n base)) (rangeExpr n base)))))

theorem optimizerContext_ceiling (n base : ℕ) (lam B epsilon : ℝ) (D : Weights n)
    (code : Code) (hceil : code.RealWriteCeiling (TargetCode.workspace n base))
    (heps : Code.PreservesReal (epsilonAddress n base) code) (tapes : Tapes) (s : State)
    (hs : OptimizerContext n base lam B epsilon D s) :
    OptimizerContext n base lam B epsilon D (code.execute tapes s) := by
  have hf (address : ℕ) (ha : TargetCode.workspace n base ≤ address) :=
    Code.realWriteCeiling_frame code _ hceil tapes s address ha
  have hW : SDP.inputWeights n (TargetCode.workspace n base) (code.execute tapes s) =
      SDP.inputWeights n (TargetCode.workspace n base) s := by
    funext edge
    exact hf _ (by unfold slot weightAddress; omega)
  exact ⟨hW.trans hs.1,(hf _ (by unfold slot; omega)).trans hs.2.1,
    (hf _ (by unfold slot; omega)).trans hs.2.2.1,(heps tapes s).trans hs.2.2.2⟩

theorem rangeExpr_value {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) (s : State)
    (hs : OptimizerContext n base lam B epsilon D s) :
    (rangeExpr n base).eval s.memory = (SDPFlat.problem hn hlam hB).rangeBound := by
  norm_num only [rangeExpr, Expr.eval, readReal]
  change (1:ℝ) + 2 * SDP.inputBound n (TargetCode.workspace n base) s +
    SDP.inputLambda n (TargetCode.workspace n base) s * ((n*n:ℕ):ℝ) = _
  rw [hs.2.1,hs.2.2.1]
  simp only [SDPFlat.problem, SDPFlat.reindex, SDPCoordinates.problem, Nat.cast_mul]
  ring

theorem writeUpper_state (n base : ℕ) (value : Expr .real) (tapes : Tapes) (s : State) :
    searchState n base ((writeReal (upperAddress n base) value).execute tapes s) =
      ⟨(searchState n base s).best,(searchState n base s).lower,value.eval s.memory⟩ := by
  apply state_ext
  · ext i
    change ((writeReal (upperAddress n base) value).execute tapes s).memory.real
      (vectorAddress (bestAddress n base) i) = s.memory.real _
    exact writeReal_frame _ _ _ _ _ (by
      have hi := scalar_before_slot (n*n) base 12 15 1 (by decide) (by unfold stride; omega)
      have ho := (vector_range (bestAddress n base) i).1
      unfold upperAddress lowerAddress bestAddress at *
      omega)
  · change ((writeReal (upperAddress n base) value).execute tapes s).memory.real
      (lowerAddress n base) = s.memory.real _
    exact writeReal_frame _ _ _ _ _ (by unfold upperAddress; omega)
  · change ((writeReal (upperAddress n base) value).execute tapes s).memory.real
      (upperAddress n base) = value.eval s.memory
    exact writeReal_value tapes s _ _

theorem initializeProgram_steps (n base : ℕ) : Steps (initializeProgram n base) (12000 * (n+1)^6) := by
  have ht := Steps.real (.natural (thresholdAddress n base)) (readReal (slot n (TargetCode.workspace n base) 4))
  have hy := (arrayProgram_steps (vectorAddress (bestAddress n base))
    (fun i : Fin (n*n) => readReal (vectorAddress (slot (n*n) base 0) i)) 2 (by intro i; rfl)).seq
    (Steps.real (.natural (lowerAddress n base)) (readReal (thresholdAddress n base)))
  have hu := Steps.real (.natural (upperAddress n base))
    (.add (readReal (lowerAddress n base)) (rangeExpr n base))
  exact ((seedProgram_steps n base).seq (ht.seq (hy.seq hu))).mono (by
    simp only [Expr.operations, readReal, rangeExpr]
    ring_nf
    omega)

theorem initializeProgram_value {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n)
    (tapes : Tapes) (s : State) (hs : OptimizerContext n base lam B epsilon D s) :
    let output := (initializeProgram n base).execute tapes s
    OptimizerContext n base lam B epsilon D output ∧
      searchState n base output =
        ⟨0,(SDPFlat.problem hn hlam hB).value D 0,
          (SDPFlat.problem hn hlam hB).value D 0 + (SDPFlat.problem hn hlam hB).rangeBound⟩ := by
  let P := SDPFlat.problem hn hlam hB
  let first := (seedProgram n base).execute tapes s
  let thresholdCode := writeReal (thresholdAddress n base) (readReal (slot n (TargetCode.workspace n base) 4))
  let second := thresholdCode.execute tapes first
  let third := (successProgram n base).execute tapes second
  let upperCode := writeReal (upperAddress n base) (.add (readReal (lowerAddress n base)) (rangeExpr n base))
  let output := upperCode.execute tapes third
  have hfirst := seedProgram_context n base lam B epsilon D tapes s hs
  have hfirstValue := seedProgram_value base hn lam B epsilon hlam hB D tapes s hs
  have hlarge : 3 ≤ stride (n*n) := by unfold stride; omega
  have hthresholdEps : Code.PreservesReal (epsilonAddress n base) thresholdCode :=
    fun tapes s => writeReal_frame _ _ _ _ _ (by
      have hi := scalar_before_slot (n*n) base 12 13 2 (by decide) (by omega)
      unfold epsilonAddress lowerAddress thresholdAddress at *
      omega)
  have hsecond := optimizerContext_ceiling n base lam B epsilon D thresholdCode
    (ceiling_writeReal _ _ _ (TargetCode.workspace_after _ _ _ (by decide))) hthresholdEps tapes first hfirst
  have hsuccessCeil : (successProgram n base).RealWriteCeiling (TargetCode.workspace n base) :=
    ⟨ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)),
      ceiling_writeReal _ _ _ (TargetCode.workspace_after _ _ _ (by decide))⟩
  have hthird := optimizerContext_ceiling n base lam B epsilon D (successProgram n base)
    hsuccessCeil (fun tapes state => post_epsilon n base tapes state true) tapes second hsecond
  have hupperCeil : upperCode.RealWriteCeiling (TargetCode.workspace n base) :=
    ceiling_writeReal _ _ _ (scalar_before_slot _ _ _ _ 1 (by decide) (by omega))
  have hupperEps : Code.PreservesReal (epsilonAddress n base) upperCode :=
    fun tapes state => writeReal_frame _ _ _ _ _ (by unfold epsilonAddress upperAddress; omega)
  have hout := optimizerContext_ceiling n base lam B epsilon D upperCode hupperCeil hupperEps tapes third hthird
  have hthreshold : second.memory.real (thresholdAddress n base) = P.value D 0 :=
    (writeReal_value tapes first _ _).trans hfirstValue.2
  have hcenter : center (n*n) base second = 0 := by
    rw [← hfirstValue.1]
    ext i
    exact writeReal_frame _ _ _ _ _ (by
      have hi := vector_before_slot (n*n) base 0 13 (by decide) i
      unfold thresholdAddress
      omega)
  have hstate : searchState n base third =
      ⟨0,P.value D 0,(searchState n base second).upper⟩ := by
    rw [successProgram_state, hcenter,hthreshold]
    rfl
  refine ⟨hout,?_⟩
  change searchState n base output = _
  rw [writeUpper_state]
  have hlower : third.memory.real (lowerAddress n base) = P.value D 0 :=
    congrArg EllipsoidOptimization.State.lower hstate
  have hbest : (searchState n base third).best = 0 :=
    congrArg EllipsoidOptimization.State.best hstate
  apply state_ext hbest hlower
  change third.memory.real (lowerAddress n base) + (rangeExpr n base).eval third.memory = _
  rw [hlower,rangeExpr_value base hn lam B epsilon hlam hB D third hthird]

theorem initializeProgram_valid {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n)
    (tapes : Tapes) (s : State) (hs : OptimizerContext n base lam B epsilon D s) :
    let output := (initializeProgram n base).execute tapes s
    OptimizerContext n base lam B epsilon D output ∧
      (searchState n base output).Valid (SDPFlat.problem hn hlam hB) D ∧
      (searchState n base output).width = (SDPFlat.problem hn hlam hB).rangeBound := by
  let P := SDPFlat.problem hn hlam hB
  have hi := initializeProgram_value base hn lam B epsilon hlam hB D tapes s hs
  refine ⟨hi.1,?_⟩
  rw [hi.2]
  have hz : (0 : EuclideanSpace ℝ (Fin (n*n))) ∈ P.body :=
    P.inner_ball (by simpa only [Metric.mem_closedBall, dist_self] using P.inner_pos.le)
  refine ⟨⟨hz,le_refl _,?_⟩,?_⟩
  · intro y hy
    have h := P.range_le D y hy 0 hz
    linarith
  · unfold EllipsoidOptimization.State.width
    simp

end DPCut.RealMachine.EllipsoidCode
