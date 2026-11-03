import DPCut.RealMachineSolverRuntime
import DPCut.RealMachineExecutionMeasurable
import DPCut.LSWPolynomialRuntime

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

open MeasureTheory

namespace DPCut.RealMachine.EllipsoidCode

open SDP

def weightsMemory (n base : ℕ) (D : Weights n) : Memory :=
  ⟨fun address => ∑ e : Edge n, if address = weightAddress (slot n (TargetCode.workspace n base) 0) e then D e else 0,
    fun _ => 0,fun _ => false⟩

def solverInput (n base : ℕ) (lam B epsilon : ℝ) (D : Weights n) : State :=
  ⟨(((weightsMemory n base D).writeReal (epsilonAddress n base) epsilon).writeReal
    (slot n (TargetCode.workspace n base) 2) lam).writeReal
      (slot n (TargetCode.workspace n base) 2+1) B,0,0,0⟩

theorem solverInput_context (n base : ℕ) (lam B epsilon : ℝ) (D : Weights n) :
    OptimizerContext n base lam B epsilon D (solverInput n base lam B epsilon D) := by
  have heps : epsilonAddress n base < TargetCode.workspace n base :=
    scalar_before_slot (n*n) base 12 16 2 (by decide) (by unfold stride; omega)
  have hslot : TargetCode.workspace n base ≤ slot n (TargetCode.workspace n base) 2 := by unfold slot; omega
  refine ⟨?_,?_,?_,?_⟩
  · funext e
    have hw := weight_before_slot n (TargetCode.workspace n base) 0 2 (by decide) e
    have hwlo := (weight_range (slot n (TargetCode.workspace n base) 0) e).1
    change TargetCode.workspace n base ≤ weightAddress (slot n (TargetCode.workspace n base) 0) e at hwlo
    change ((((weightsMemory n base D).writeReal (epsilonAddress n base) epsilon).writeReal
      (slot n (TargetCode.workspace n base) 2) lam).writeReal
      (slot n (TargetCode.workspace n base) 2+1) B).real
        (weightAddress (slot n (TargetCode.workspace n base) 0) e) = D e
    simp only [Memory.writeReal, Function.update_apply, if_neg (show
      weightAddress (slot n (TargetCode.workspace n base) 0) e ≠ slot n (TargetCode.workspace n base) 2+1 by omega),
      if_neg hw.ne,if_neg (show weightAddress (slot n (TargetCode.workspace n base) 0) e ≠ epsilonAddress n base by omega)]
    simp only [weightsMemory, (weightAddress_injective _).eq_iff]
    simp
  · simp only [inputLambda, solverInput, Memory.writeReal, Function.update_apply,
      if_neg (show slot n (TargetCode.workspace n base) 2 ≠ slot n (TargetCode.workspace n base) 2+1 by omega),
      ite_true]
  · simp only [inputBound, solverInput, Memory.writeReal, Function.update_self]
  · simp only [solverInput, Memory.writeReal, Function.update_apply,
      if_neg (show epsilonAddress n base ≠ slot n (TargetCode.workspace n base) 2+1 by omega),
      if_neg (show epsilonAddress n base ≠ slot n (TargetCode.workspace n base) 2 by omega), ite_true]

@[fun_prop] theorem measurable_solverInput (n base : ℕ) (lam B epsilon : ℝ) :
    Measurable (solverInput n base lam B epsilon) := by
  have hw : Measurable (weightsMemory n base) := by
    apply measurable_memory
    · apply measurable_pi_lambda
      intro address
      apply Finset.measurable_sum
      intro e _
      split_ifs
      · exact measurable_pi_apply e
      · exact measurable_const
    · exact measurable_const
    · exact measurable_const
  apply measurable_state
  · exact measurable_writeReal.comp ((measurable_writeReal.comp
      ((measurable_writeReal.comp (hw.prodMk (measurable_const.prodMk measurable_const))).prodMk
        (measurable_const.prodMk measurable_const))).prodMk (measurable_const.prodMk measurable_const))
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const

@[fun_prop] theorem measurable_outputMatrix (n base : ℕ) : Measurable (outputMatrix n base) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply (matrixAddress (slot (n*n) base 0) (i,j))).comp
    (measurable_memory_real.comp measurable_state_memory)

def program {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B) : Code :=
  solverProgram n 0 (iterations hn lam B epsilon hlam hB)
    (EllipsoidOptimization.rounds (SDPFlat.problem hn hlam hB) epsilon)

def covariance {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (D : Weights n) : Mat n :=
  outputMatrix n 0 ((program hn lam B epsilon hlam hB).execute Tapes.zero (solverInput n 0 lam B epsilon D))

@[fun_prop] theorem measurable_covariance {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    Measurable (covariance hn lam B epsilon hlam hB) :=
  (measurable_outputMatrix n 0).comp
    ((Code.measurable_execute (program hn lam B epsilon hlam hB) Tapes.zero).comp
      (measurable_solverInput n 0 lam B epsilon))

theorem covariance_accurate {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ)
    (hlam : 0 ≤ lam) (hB : 0 ≤ B) (he : 0 < epsilon) (hehalf : epsilon ≤ 1/2) (D : Weights n) :
    covariance hn lam B epsilon hlam hB D ∈ feasible n ∧
      optimum lam (boundedObjective B D) -
        objective lam (boundedObjective B D) (covariance hn lam B epsilon hlam hB D) ≤ epsilon :=
  solverProgram_accurate 0 hn lam B epsilon hlam hB he hehalf D Tapes.zero _
    (solverInput_context n 0 lam B epsilon D)

theorem scale_le_lswScale {n : ℕ} (hn : 2 ≤ n) (lam B epsilon : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B) :
    EllipsoidOptimization.scale (SDPFlat.problem hn hlam hB) epsilon ≤ sdpLSWScale n lam B epsilon := by
  change 1 + (n*n:ℕ) + Real.log ((2*(n:ℝ))/(1/4)) +
    Real.log ((1+2*B+lam*(n:ℝ)^2)/epsilon) ≤ _
  have hgeom : (2*(n:ℝ))/(1/4) = 8*n := by ring
  rw [hgeom]
  unfold sdpLSWScale
  push_cast
  linarith [Nat.cast_nonneg (α:=ℝ) (SDPCoordinates.oracleCharge n)]

end DPCut.RealMachine.EllipsoidCode
