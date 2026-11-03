import DPCut.RealMachineTargetDecision

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section

namespace DPCut.RealMachine.TargetCode

open SDP EllipsoidCode

theorem prepared_realizes {n base : ℕ} (P : LSW.Problem (Fin (n*n)) (Weights n)) (O : LSW.Oracle P)
    (hm : 1 ≤ n*n) (D : Weights n) (threshold : ℝ)
    (s : State) (e : EllipsoidMethod.Ellipsoid (EuclideanSpace ℝ (Fin (n*n))))
    (he : Matches (n*n) base s e)
    (hp : Prepared n base hm threshold s (O.answer (D,e.center)).value) :
    DecisionRealized base e s (EllipsoidOptimization.targetOracle P O hm D threshold e.center) := by
  unfold EllipsoidOptimization.targetOracle
  split
  · rename_i g ho
    simp only [ho, Prepared] at hp
    exact ⟨hp.1,he,hp.2⟩
  · rename_i value g ho
    split_ifs with ha hg
    · simp only [ho, Prepared, ha, ite_true] at hp
      exact ⟨hp,he⟩
    · simp only [ho, Prepared, ha, ite_false, hg, ite_true] at hp
      exact ⟨hp.1,he,hp.2⟩
    · simp only [ho, Prepared, ha, ite_false, hg, ite_false] at hp
      exact ⟨hp.1,he,hp.2⟩

def script {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B threshold : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n) :
    PointScript (n*n) base
      (EllipsoidOptimization.target (SDPFlat.problem hn hlam hB) D threshold)
      (Context n base lam B threshold D) where
  code := ask n base
  oracle := EllipsoidOptimization.targetOracle (SDPFlat.problem hn hlam hB) (SDPFlat.oracle hn hlam hB)
    (by nlinarith) D threshold
  context_real := context_real n base lam B threshold D
  cut_context := cut_context n base lam B threshold D
  answer tapes s e hs he := by
    let a := (copyPoint n base).execute tapes s
    let b := (SDP.oracleProgram n (workspace n base)).execute tapes a
    let c := (decideReply n base).execute tapes b
    have hA := copyPoint_context n base lam B threshold D tapes s hs
    have hBctx : Context n base lam B threshold D b := context_of_low n base lam B threshold D a b
      (Code.realWriteFloor_frame _ _ (SDP.oracleProgram_floor n (workspace n base) _ le_rfl) tapes a) hA
    have hCctx := ask_context n base lam B threshold D tapes s hs
    have hCshape := ask_matches n base tapes s e he
    change Context n base lam B threshold D c ∧ DecisionRealized base e c _
    refine ⟨hCctx, ?_⟩
    have hflatPoint := copyPoint_value tapes s n base
    rw [he.1] at hflatPoint
    have hpoint : SDP.inputPoint n (workspace n base) a = (SDPFlat.equiv n).symm e.center := by
      calc
        _ = (SDPFlat.equiv n).symm (SDPFlat.equiv n (SDP.inputPoint n (workspace n base) a)) := by simp
        _ = _ := congrArg (SDPFlat.equiv n).symm hflatPoint
    have hreply := SDP.oracleProgram_value tapes a n (workspace n base) hn
    rw [hA.1, hA.2.1, hA.2.2.1, hpoint] at hreply
    have hreplyFlat : SDPFlat.mapReply n (SDP.reply n (workspace n base) b) =
        ((SDPFlat.oracle hn hlam hB).answer (D,e.center)).value :=
      congrArg (SDPFlat.mapReply n) hreply
    have hp := decideReply_value tapes b n base (by nlinarith : 1 ≤ n*n)
    rw [hBctx.2.2.2,hreplyFlat] at hp
    exact prepared_realizes _ _ (by nlinarith : 1 ≤ n*n) D threshold c e hCshape hp

end DPCut.RealMachine.TargetCode
