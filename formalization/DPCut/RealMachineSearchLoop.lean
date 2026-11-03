import DPCut.RealMachineSearchInvariant

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

theorem searchLoop_valid {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) (D : Weights n)
    (tapes : Tapes) (rounds : ℕ) (s : State) (hctx : OptimizerContext n base lam B epsilon D s)
    (hvalid : (searchState n base s).Valid (SDPFlat.problem hn hlam hB) D) :
    let output := (searchLoop n base (iterations hn lam B epsilon hlam hB) rounds).execute tapes s
    OptimizerContext n base lam B epsilon D output ∧
      (searchState n base output).Valid (SDPFlat.problem hn hlam hB) D ∧
      (searchState n base output).width ≤
        ((searchState n base s).width - epsilon/2)/(2:ℝ)^rounds + epsilon/2 := by
  induction rounds generalizing s with
  | zero =>
      refine ⟨hctx,hvalid,?_⟩
      simp only [searchLoop, Code.execute, pow_zero, div_one]
      linarith
  | succ rounds ih =>
      let first := (searchStep n base (iterations hn lam B epsilon hlam hB)).execute tapes s
      have hs := searchStep_valid base hn lam B epsilon hlam hB he hehalf D tapes s hctx hvalid
      have hi := ih first hs.1 hs.2.1
      refine ⟨hi.1,hi.2.1,?_⟩
      change (searchState n base ((searchLoop n base (iterations hn lam B epsilon hlam hB) rounds).execute tapes first)).width ≤ _
      have hstep : (searchState n base first).width - epsilon/2 ≤
          ((searchState n base s).width - epsilon/2)/2 := by linarith [hs.2.2]
      calc
        _ ≤ ((searchState n base first).width - epsilon/2)/(2:ℝ)^rounds + epsilon/2 := hi.2.2
        _ ≤ (((searchState n base s).width - epsilon/2)/2)/(2:ℝ)^rounds + epsilon/2 :=
          add_le_add_right (div_le_div_of_nonneg_right hstep (by positivity)) _
        _ = _ := by rw [pow_succ]; field_simp

theorem searchLoop_accurate {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) (D : Weights n)
    (tapes : Tapes) (s : State) (hctx : OptimizerContext n base lam B epsilon D s)
    (hvalid : (searchState n base s).Valid (SDPFlat.problem hn hlam hB) D)
    (hwidth : (searchState n base s).width ≤ (SDPFlat.problem hn hlam hB).rangeBound) :
    LSW.Accurate (SDPFlat.problem hn hlam hB) epsilon D
      (searchState n base
        ((searchLoop n base (iterations hn lam B epsilon hlam hB)
          (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)).execute tapes s)).best := by
  let P := SDPFlat.problem hn hlam hB
  let output := (searchLoop n base (iterations hn lam B epsilon hlam hB) (EllipsoidOptimization.rounds P epsilon)).execute tapes s
  have hs := searchLoop_valid base hn lam B epsilon hlam hB he hehalf D tapes
    (EllipsoidOptimization.rounds P epsilon) s hctx hvalid
  have hbound := EllipsoidOptimization.rounds_precision P he
  have hw : (searchState n base output).width ≤ epsilon := by
    have hi : ((searchState n base s).width - epsilon/2)/(2:ℝ)^EllipsoidOptimization.rounds P epsilon ≤
        P.rangeBound/(2:ℝ)^EllipsoidOptimization.rounds P epsilon :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith [hs.2.2]
  refine ⟨hs.2.1.1,?_⟩
  intro y hy
  have hu := hs.2.1.2.2 y hy
  have hl := hs.2.1.2.1
  unfold EllipsoidOptimization.State.width at hw
  linarith

end DPCut.RealMachine.EllipsoidCode
