import DPCut.TypedMachineNumerical
import DPCut.LSWRelease

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.VerifiedRelease

variable {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)

def solveValue (D : Weights n) : FeasibleMatrix n :=
  ⟨(TypedMachine.releaseSolver hn p hp).result D,
    ((TypedMachine.releaseSolver hn p hp).result_accurate D).1⟩

@[fun_prop] theorem measurable_solveValue : Measurable (solveValue hn p hp) :=
  ((TypedMachine.releaseSolver hn p hp).measurable_result).subtype_mk

def solve (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  .sample (Measure.dirac (solveValue hn p hp D)) (TypedMachine.releaseSolver hn p hp |>.operations D)

@[simp] theorem solve_law (D : Weights n) :
    (solve hn p hp D).law = Measure.dirac (solveValue hn p hp D) := rfl

@[fun_prop] theorem measurable_solve : Measurable (fun D => (solve hn p hp D).law) :=
  Measure.measurable_dirac.comp (measurable_solveValue hn p hp)

instance solve_probability (D : Weights n) : IsProbabilityMeasure (solve hn p hp D).law := by
  rw [solve_law]
  infer_instance

theorem solve_failure (D : Weights n) :
    (solve hn p hp D).law {X |
      (fullRunConfig n (precisionParameters p)).oracle.lam * (approximationRadius n p/2)^2 / (2*(n:ℝ)^4) <
        optimum (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) -
        objective (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) X.val} = 0 := by
  have ha := ((TypedMachine.releaseSolver hn p hp).result_accurate D).2
  have hl : 1 ≤ (fullRunConfig n (precisionParameters p)).oracle.lam :=
    le_trans (by norm_num : (1:ℝ) ≤ 8) (approxConfig_bounds hn hp).lam_lower
  have hg := ha.trans (solverAccuracy_le_gap (n:=n) (p:=p) hl)
  have hmem : solveValue hn p hp D ∉ {X : FeasibleMatrix n |
      (fullRunConfig n (precisionParameters p)).oracle.lam * (approximationRadius n p/2)^2 / (2*(n:ℝ)^4) <
        optimum (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) -
        objective (fullRunConfig n (precisionParameters p)).oracle.lam
          (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) X.val} :=
    not_lt_of_ge hg
  rw [solve_law]
  rw [Measure.dirac_apply, Set.indicator_of_notMem hmem]

def witness (D r : Weights n) : CostedLaw (Option (Weights n)) :=
  RandomizedWitness.run (fullRunConfig n (precisionParameters p)).oracle (solve hn p hp)
    (publicObjectiveBound n (precisionParameters p)) D r

def witnessKernel : OracleReplacement.WitnessKernel n :=
  ⟨fun q => (witness hn p hp q.1 q.2).law,
    RandomizedWitness.measurable_run hn _ (approxConfig_bounds hn hp).eps_pos _
      (measurable_solve hn p hp) _⟩

instance witnessKernel_markov : IsMarkovKernel (witnessKernel hn p hp) :=
  ⟨fun q => RandomizedWitness.run_probability hn _ (approxConfig_bounds hn hp).eps_pos _ _ q.1 q.2⟩

theorem witness_tv (D r : Weights n) :
    TVClose (witness hn p hp D r).law
      (findWitness (fullRunConfig n (precisionParameters p)).oracle
        (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) r)
      ((fullRunConfig n (precisionParameters p)).oracle.K *
        (2 * Real.sqrt (fullRunConfig n (precisionParameters p)).oracle.k * approximationRadius n p)) := by
  let c := fullRunConfig n (precisionParameters p)
  have ho := approxConfig_bounds hn hp
  obtain ⟨hr,hrhalf⟩ := approximationRadius_bounds (n:=n) hp
  have hbad (D : Weights n) : (solve hn p hp D).law {X |
      c.oracle.lam * (approximationRadius n p/2)^2 / (2*(n:ℝ)^4) <
        optimum c.oracle.lam (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) -
          objective c.oracle.lam (boundedObjective (publicObjectiveBound n (precisionParameters p)) D) X.val} ≤ ENNReal.ofReal 0 := by
    rw [solve_failure hn p hp D, ENNReal.ofReal_zero]
  have ht := RandomizedWitness.law_tv hn c.oracle ho.eps_pos
    (by linarith [ho.lam_lower]) ho.batch_pos
    (show 0 < approximationRadius n p/2 by linarith)
    (show approximationRadius n p/2 ≤ 1/2 by linarith) (le_refl 0)
    (solve hn p hp) hbad D r
  apply ht.mono
  have hfactor : 0 ≤ (c.oracle.K:ℝ) * (2*Real.sqrt c.oracle.k) := by positivity
  nlinarith

end DPCut.VerifiedRelease
