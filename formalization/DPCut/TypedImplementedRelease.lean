import DPCut.TypedPublicData
import DPCut.TypedReleaseCallBound

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

abbrev ReleaseOutcome (n : ℕ) := Weights n × ℕ × ℕ

def combineSetup {n : ℕ} (setup : Outcome publicType) (output : Outcome (weightType n)) : ReleaseOutcome n :=
  (decodeWeights output.1,setup.2.1+output.2.1,setup.2.2+output.2.2)

@[fun_prop] theorem measurable_combineSetup (n : ℕ) :
    Measurable (fun p : Outcome publicType × Outcome (weightType n) => combineSetup p.1 p.2) := by
  unfold combineSetup
  apply Measurable.prodMk
  · exact (measurable_decodeWeights n).comp (measurable_fst.comp measurable_snd)
  · fun_prop

/-- This is the named implementation: compute the public calibration by scalar
instructions, then run Algorithms 1--4 with that data and the proved ellipsoid
subroutine. The input contains only the graph and its public parameters. -/
def implementedRun {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    Measure (ReleaseOutcome n) :=
  ((calibrationCommand n).code.run (parameterInput p)).bind fun setup =>
    ((releaseProgram hn p hp).code.run (encodeWeights w,setup.1,())).map (combineSetup setup)

@[fun_prop] theorem measurable_implementedContinuation {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (w : Weights n) :
    Measurable (fun setup : Outcome publicType =>
      ((releaseProgram hn p hp).code.run (encodeWeights w,setup.1,())).map (combineSetup setup)) := by
  have hm : Measurable (fun setup : Outcome publicType =>
      (releaseProgram hn p hp).code.run (encodeWeights w,setup.1,())) :=
    (releaseProgram hn p hp).code.measurable_run.comp
      (measurable_const.prodMk (measurable_fst.prodMk (measurable_const (a:=()))))
  letI (setup : Outcome publicType) :
      IsProbabilityMeasure ((releaseProgram hn p hp).code.run (encodeWeights w,setup.1,())) :=
    Command.run_probability _ _
  exact measurable_map_kernel hm (measurable_combineSetup n)

theorem implementedRun_eq {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    implementedRun hn p hp w =
      ((releaseProgram hn p hp).code.run (releaseInput n p w)).map
        (fun output => (decodeWeights output.1,(calibrationCommand n).operations+output.2.1,output.2.2)) := by
  rw [implementedRun]
  change ((Measure.dirac ((publicData n p),(calibrationCommand n).operations,0)).bind _) = _
  rw [Measure.dirac_bind (measurable_implementedContinuation hn p hp w)]
  congr 1
  funext output
  simp [combineSetup]

def implementedLaw {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) : Measure (Weights n) :=
  (implementedRun hn p hp w).map Prod.fst

theorem implementedLaw_eq {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    implementedLaw hn p hp w =
      ((releaseProgram hn p hp).code.law (releaseInput n p w)).map decodeWeights := by
  rw [implementedLaw,implementedRun_eq]
  have hm : Measurable (fun output : Outcome (weightType n) =>
      (decodeWeights output.1,(calibrationCommand n).operations+output.2.1,output.2.2)) := by
    exact ((measurable_decodeWeights n).comp measurable_fst).prodMk (by fun_prop)
  rw [Measure.map_map measurable_fst hm]
  rw [Command.law,Measure.map_map (measurable_decodeWeights n) measurable_fst]
  rfl

theorem actualReleaseEps2_pos {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    0 < (fullRunConfig n (precisionParameters p)).eps2 :=
  (outerConfig_inner_utility_bounds hn (preprocessingThreshold_one_le hn (precisionParameters_valid hp))
    (boundedParameters (precisionParameters p)) (boundedParameters_valid (precisionParameters_valid hp))).eps2_pos

theorem implementedLaw_reference {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    implementedLaw hn p hp w = VerifiedRelease.release hn p hp w := by
  rw [implementedLaw_eq]
  let c := fullRunConfig n (precisionParameters p)
  let data := dataInput n
  let S := releaseSolver hn p hp
  have hfull := fullCommand_law S (boundedParameters (precisionParameters p)) c
    (approxConfig_bounds hn hp).eps_pos (actualReleaseEps2_pos hn p hp)
    (publicObjectiveBound n (precisionParameters p)) (runTermsOf data)
    (realPublic data 9) (realPublic data 10) (realPublic data 11)
    (newest : Term (releaseContext n) (weightType n)) (releaseInput n p w)
    (releaseInput_matches hn p hp w) (by rw [releaseInput_epsilon]; linarith [hp.2.2.1])
  change ((fullCommand S c.oracle.k c.oracle.K c.T1 c.T2 (runTermsOf data)
    (realPublic data 9) (realPublic data 10) (realPublic data 11) newest).code.law
      (releaseInput n p w)).map decodeWeights = _
  rw [hfull,releaseInput_threshold,releaseInput_shift,releaseInput_epsilon]
  simp only [Term.eval,newest,Local.read,releaseInput,decode_encodeWeights]
  rw [numericalWitnessKernel_release hn p hp]
  change _ = (OracleReplacement.fullRelease (VerifiedRelease.witnessKernel hn p hp)
    (precisionParameters p) w).map positiveWeights
  unfold OracleReplacement.fullRelease preprocessLaw
  simp only [c,fullRunConfig,precisionParameters,preprocessingThreshold]
  rw [show p.beta/2/2 = p.beta/4 by ring]

theorem implemented_private {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    EdgeDP (implementedLaw hn p hp) p.epsilon p.delta := by
  have heq : implementedLaw hn p hp = VerifiedRelease.release hn p hp :=
    funext (implementedLaw_reference hn p hp)
  rw [heq]
  exact VerifiedRelease.release_private hn p hp

theorem implemented_utility {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid)
    (w : Weights n) (hw : Nonnegative w) :
    HighProbability (implementedLaw hn p hp w) p.beta
      (fun h => AllCuts w h p.gamma ((2:ℝ)^178*mainError n p)) := by
  rw [implementedLaw_reference]
  exact VerifiedRelease.release_utility hn p hp w hw

theorem implemented_nonnegative {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    ∀ᵐ h ∂implementedLaw hn p hp w, Nonnegative h := by
  rw [implementedLaw_reference]
  exact VerifiedRelease.release_nonnegative hn p hp w

theorem implemented_probability {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    IsProbabilityMeasure (implementedLaw hn p hp w) := by
  rw [implementedLaw_reference]
  infer_instance

theorem measurable_implementedLaw {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    Measurable (implementedLaw hn p hp) := by
  rw [show implementedLaw hn p hp = VerifiedRelease.release hn p hp from
    funext (implementedLaw_reference hn p hp)]
  exact VerifiedRelease.measurable_release hn p hp

end DPCut.TypedMachine
