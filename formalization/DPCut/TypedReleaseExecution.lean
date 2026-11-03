import DPCut.TypedExecution
import DPCut.TypedImplementedRelease

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace DPCut.TypedMachine

def ImplementedExecution {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n)
    (result : ReleaseOutcome n) : Prop :=
  ∃ setup output,
    Executes (calibrationCommand n).code (parameterInput p) setup ∧
      Executes (releaseProgram hn p hp).code (encodeWeights w,setup.1,()) output ∧
      result = combineSetup setup output

theorem implementedExecution_exists {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∃ r, ImplementedExecution hn p hp w r := by
  obtain ⟨setup,hs⟩ := (calibrationCommand n).code.execution_exists (parameterInput p)
  obtain ⟨output,ho⟩ := (releaseProgram hn p hp).code.execution_exists (encodeWeights w,setup.1,())
  exact ⟨_,setup,output,hs,ho,rfl⟩

theorem implementedExecution_bound {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (w : Weights n) (r : ReleaseOutcome n) (trace : ImplementedExecution hn p hp w r) :
    r.2.1 ≤ (calibrationCommand n).operations+(releaseProgram hn p hp).operations ∧
      r.2.2 ≤ (releaseProgram hn p hp).solverCalls := by
  obtain ⟨setup,output,hs,ho,rfl⟩ := trace
  have hc := (calibrationCommand n).execution_bound _ _ hs
  have hb := (releaseProgram hn p hp).execution_bound _ _ ho
  have hz : (calibrationCommand n).solverCalls = 0 := rfl
  simp only [combineSetup]
  exact ⟨Nat.add_le_add hc.1 hb.1,by omega⟩

end DPCut.TypedMachine
