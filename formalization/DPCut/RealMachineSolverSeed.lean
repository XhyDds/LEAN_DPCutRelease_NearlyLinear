import DPCut.RealMachineSearchLoop

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def seedProgram (n base : ℕ) : Code :=
  .seq (ballProgram n base)
    (.seq (TargetCode.copyPoint n base) (SDP.oracleProgram n (TargetCode.workspace n base)))

theorem seedProgram_steps (n base : ℕ) : Steps (seedProgram n base) (11000 * (n+1)^6) := by
  have hp := matrixMap_steps n (slot n (TargetCode.workspace n base) 1) 2
    (fun ij => readReal (vectorAddress (slot (n*n) base 0) (finProdFinEquiv ij))) (by intro ij; rfl)
  exact ((ballProgram_steps n base).seq (hp.seq (SDP.oracleProgram_steps n (TargetCode.workspace n base)))).mono
    (by ring_nf; omega)

theorem seedProgram_protected (n base address : ℕ)
    (hlo : slot (n*n) base 12 ≤ address) (hhi : address < TargetCode.workspace n base) :
    Code.PreservesReal address (seedProgram n base) := by
  have hball : (ballProgram n base).RealWriteCeiling (slot (n*n) base 12) :=
    ⟨ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)),
      ceiling_matrixMap _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))⟩
  have hcopy : (TargetCode.copyPoint n base).RealWriteFloor (TargetCode.workspace n base) :=
    floor_matrixMap _ _ _ _ (by unfold slot; omega)
  have horacle := SDP.oracleProgram_floor n (TargetCode.workspace n base)
    (TargetCode.workspace n base) (by unfold slot; omega)
  have hb : Code.PreservesReal address (ballProgram n base) :=
    fun tapes s => Code.realWriteCeiling_frame _ _ hball tapes s address hlo
  have hp : Code.PreservesReal address (TargetCode.copyPoint n base) :=
    fun tapes s => Code.realWriteFloor_frame _ _ hcopy tapes s address hhi
  have ho : Code.PreservesReal address (SDP.oracleProgram n (TargetCode.workspace n base)) :=
    fun tapes s => Code.realWriteFloor_frame _ _ horacle tapes s address hhi
  exact hb.seq (hp.seq ho)

theorem seedProgram_context (n base : ℕ) (lam B epsilon : ℝ) (D : Weights n)
    (tapes : Tapes) (s : State) (hs : OptimizerContext n base lam B epsilon D s) :
    OptimizerContext n base lam B epsilon D ((seedProgram n base).execute tapes s) := by
  let threshold := s.memory.real (thresholdAddress n base)
  have hc : TargetCode.Context n base lam B threshold D s := ⟨hs.1,hs.2.1,hs.2.2.1,rfl⟩
  have hb := ballProgram_context base lam B threshold D tapes s hc
  have hp := TargetCode.copyPoint_context n base lam B threshold D tapes _ hb
  have ho := TargetCode.context_of_low n base lam B threshold D _
    ((SDP.oracleProgram n (TargetCode.workspace n base)).execute tapes _) (by
      exact Code.realWriteFloor_frame _ _ (SDP.oracleProgram_floor _ _ _ le_rfl) tapes _) hp
  refine ⟨ho.1,ho.2.1,ho.2.2.1,?_⟩
  exact (seedProgram_protected n base (epsilonAddress n base) (by unfold epsilonAddress lowerAddress; omega)
    (scalar_before_slot _ _ _ _ 2 (by decide) (by unfold stride; omega)) tapes s).trans hs.2.2.2

theorem seedProgram_value {n : ℕ} (base : ℕ) (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (D : Weights n)
    (tapes : Tapes) (s : State) (hs : OptimizerContext n base lam B epsilon D s) :
    let output := (seedProgram n base).execute tapes s
    center (n*n) base output = 0 ∧ output.memory.real (slot n (TargetCode.workspace n base) 4) =
      (SDPFlat.problem hn hlam hB).value D 0 := by
  let first := (ballProgram n base).execute tapes s
  let second := (TargetCode.copyPoint n base).execute tapes first
  let output := (SDP.oracleProgram n (TargetCode.workspace n base)).execute tapes second
  let threshold := s.memory.real (thresholdAddress n base)
  have hc : TargetCode.Context n base lam B threshold D s := ⟨hs.1,hs.2.1,hs.2.2.1,rfl⟩
  have hfirst := ballProgram_context base lam B threshold D tapes s hc
  have hsecond := TargetCode.copyPoint_context n base lam B threshold D tapes first hfirst
  have hz : center (n*n) base first = 0 := (ballProgram_value base hn tapes s).1
  have hx : SDP.inputPoint n (TargetCode.workspace n base) second = 0 := by
    apply (SDPFlat.equiv n).injective
    rw [TargetCode.copyPoint_value, hz, map_zero]
  have hcopyFloor : (TargetCode.copyPoint n base).RealWriteFloor (TargetCode.workspace n base) :=
    floor_matrixMap _ _ _ _ (by unfold slot; omega)
  have horacleFloor : (SDP.oracleProgram n (TargetCode.workspace n base)).RealWriteFloor (TargetCode.workspace n base) :=
    SDP.oracleProgram_floor _ _ _ (by unfold slot; omega)
  have hcenter : center (n*n) base output = 0 := by
    rw [← hz]
    ext i
    change output.memory.real (vectorAddress (slot (n*n) base 0) i) = first.memory.real _
    rw [Code.realWriteFloor_frame _ _ horacleFloor tapes second _
      (vector_before_slot (n*n) base 0 16 (by decide) i),
      Code.realWriteFloor_frame _ _ hcopyFloor tapes first _
        (vector_before_slot (n*n) base 0 16 (by decide) i)]
  have hr : SDP.reply n (TargetCode.workspace n base) output =
      SDPCoordinates.answer MatrixElimination.primitives lam B (D,0) := by
    rw [SDP.oracleProgram_value _ _ _ _ hn, hsecond.1,hsecond.2.1,hsecond.2.2.1,hx]
  have hcorrect := SDPCoordinates.answer_correct hn hlam hB MatrixElimination.primitives D 0
  rw [← hr] at hcorrect
  have hzero : (0 : SDPCoordinates.Space n) ∈ (SDPCoordinates.problem hn hlam hB).body :=
    (SDPCoordinates.problem hn hlam hB).inner_ball (by simp [Metric.mem_closedBall]; norm_num [SDPCoordinates.problem])
  refine ⟨hcenter,?_⟩
  by_cases hf : output.memory.boolean (slot n (TargetCode.workspace n base) 4) = true
  · simp only [SDP.reply, hf, ite_true, LSW.CorrectReply] at hcorrect
    simpa only [SDPFlat.problem, SDPFlat.reindex, map_zero] using hcorrect.2.1
  · have hf' := Bool.eq_false_of_not_eq_true hf
    simp only [SDP.reply, hf', Bool.false_eq_true, ite_false, LSW.CorrectReply] at hcorrect
    exact False.elim (hcorrect.1 hzero)

end DPCut.RealMachine.EllipsoidCode
