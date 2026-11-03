import DPCut.RealMachineEllipsoidCheck

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace DPCut.RealMachine

def Code.PreservesReal (address : ℕ) (code : Code) : Prop :=
  ∀ tapes s, (code.execute tapes s).memory.real address = s.memory.real address

theorem Code.PreservesReal.skip (address : ℕ) : Code.PreservesReal address .skip := by intro tapes s; rfl

theorem Code.PreservesReal.seq {address : ℕ} {first next : Code}
    (hf : Code.PreservesReal address first) (hn : Code.PreservesReal address next) :
    Code.PreservesReal address (.seq first next) := by
  intro tapes s
  exact (hn tapes (first.execute tapes s)).trans (hf tapes s)

theorem Code.PreservesReal.branch {address : ℕ} (condition : Expr .boolean) {yes no : Code}
    (hy : Code.PreservesReal address yes) (hn : Code.PreservesReal address no) :
    Code.PreservesReal address (.branch condition yes no) := by
  intro tapes s
  simp only [Code.execute]
  split
  · exact hy tapes _
  · exact hn tapes _

theorem Code.PreservesReal.control (address : ℕ) (code : Code) (h : code.ControlOnly) :
    Code.PreservesReal address code := fun tapes s => congrFun (Code.controlOnly_real _ h tapes s) address

namespace EllipsoidCode

open SDP

theorem ask_protected (n base address : ℕ) (hlo : slot (n*n) base 12 ≤ address)
    (hhi : address < TargetCode.workspace n base) :
    Code.PreservesReal address (TargetCode.ask n base) := by
  have hlow (code : Code) (h : code.RealWriteFloor (TargetCode.workspace n base)) :
      Code.PreservesReal address code := fun tapes s => Code.realWriteFloor_frame _ _ h tapes s address hhi
  have hhigh (code : Code) (h : code.RealWriteCeiling (slot (n*n) base 3)) :
      Code.PreservesReal address code := fun tapes s =>
    Code.realWriteCeiling_frame _ _ h tapes s address ((slot_lt_slot (n*n) base 3 12 (by decide)).le.trans hlo)
  have hnorm : (coordinateNormProgram n (slot n (TargetCode.workspace n base) 3) (slot n (TargetCode.workspace n base) 11 + 1)).RealWriteFloor
      (TargetCode.workspace n base) := by
    have ha : TargetCode.workspace n base ≤ slot n (TargetCode.workspace n base) 11 + 1 := by unfold slot; omega
    exact ⟨floor_sum _ _ _ ha,floor_writeReal _ _ _ ha⟩
  have hg : Code.PreservesReal address (TargetCode.gradientReject n base) :=
    (hlow _ hnorm).seq (((Code.PreservesReal.branch _
      (hhigh _ (ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide))))
      (hhigh _ (ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide))))).seq
        (Code.PreservesReal.control _ _ trivial)))
  have hdecision : Code.PreservesReal address (TargetCode.decideReply n base) :=
    Code.PreservesReal.branch _
      (Code.PreservesReal.branch _ (Code.PreservesReal.control _ _ trivial) hg)
      ((hhigh _ (ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)))).seq
        (Code.PreservesReal.control _ _ trivial))
  exact (hlow _ (floor_matrixMap _ _ _ _ (by unfold slot; omega))).seq
    ((hlow _ (SDP.oracleProgram_floor _ _ _ (by unfold slot; omega))).seq hdecision)

theorem checkLoop_protected (n base address fuel : ℕ) (hlo : slot (n*n) base 12 ≤ address)
    (hhi : address < TargetCode.workspace n base) :
    Code.PreservesReal address (checkLoop (n*n) base (TargetCode.ask n base) fuel) := by
  have hcut : Code.PreservesReal address (cutProgram (n*n) base) :=
    fun tapes s => Code.realWriteCeiling_frame _ _ (cutProgram_ceiling _ _) tapes s address hlo
  induction fuel with
  | zero => exact Code.PreservesReal.skip _
  | succ fuel ih =>
      exact (ask_protected _ _ _ hlo hhi).seq
        (Code.PreservesReal.branch _ (Code.PreservesReal.skip _) (hcut.seq ih))

theorem checkCode_protected (n base address fuel : ℕ) (hlo : slot (n*n) base 12 ≤ address)
    (hhi : address < TargetCode.workspace n base) :
    Code.PreservesReal address (checkCode n base fuel) := by
  have hballCeil : (ballProgram n base).RealWriteCeiling (slot (n*n) base 12) :=
    ⟨ceiling_array _ _ _ (vector_before_slot _ _ _ _ (by decide)),
      ceiling_matrixMap _ _ _ _ (matrix_before_slot _ _ _ _ (by decide))⟩
  have hball : Code.PreservesReal address (ballProgram n base) :=
    fun tapes s => Code.realWriteCeiling_frame _ _ hballCeil tapes s address hlo
  exact hball.seq ((Code.PreservesReal.control address (writeBoolean (slot (n*n) base 14) (.boolean false)) trivial).seq
    (checkLoop_protected _ _ _ _ hlo hhi))

end EllipsoidCode

end DPCut.RealMachine
