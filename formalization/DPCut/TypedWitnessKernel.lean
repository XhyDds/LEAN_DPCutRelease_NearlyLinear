import DPCut.TypedWitnessLaw
import DPCut.TypedReleaseTerms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

def SolverData.feasibleValue {n : ℕ} (S : SolverData n) (D : Weights n) : FeasibleMatrix n :=
  ⟨S.result D,(S.result_accurate D).1⟩

def SolverData.solve {n : ℕ} (S : SolverData n) (D : Weights n) : CostedLaw (FeasibleMatrix n) :=
  .sample (Measure.dirac (S.feasibleValue D)) (S.operations D)

@[fun_prop] theorem SolverData.measurable_feasibleValue {n : ℕ} (S : SolverData n) :
    Measurable S.feasibleValue := S.measurable_result.subtype_mk

@[fun_prop] theorem SolverData.measurable_solve {n : ℕ} (S : SolverData n) :
    Measurable (fun D => (S.solve D).law) :=
  Measure.measurable_dirac.comp S.measurable_feasibleValue

instance SolverData.solve_probability {n : ℕ} (S : SolverData n) (D : Weights n) :
    IsProbabilityMeasure (S.solve D).law := by
  change IsProbabilityMeasure (Measure.dirac _)
  infer_instance

def numericalWitnessKernel {n : ℕ} (S : SolverData n) (o : OracleConfig) (he : 0 < o.eps1) (B : ℝ) :
    OracleReplacement.WitnessKernel n :=
  ⟨fun q => (RandomizedWitness.run o S.solve B q.1 q.2).law,
    RandomizedWitness.measurable_run S.dimension o he S.solve S.measurable_solve B⟩

instance numericalWitnessKernel_markov {n : ℕ} (S : SolverData n) (o : OracleConfig) (he : 0 < o.eps1) (B : ℝ) :
    IsMarkovKernel (numericalWitnessKernel S o he B) :=
  ⟨fun q => RandomizedWitness.run_probability S.dimension o he S.solve B q.1 q.2⟩

theorem numericalWitnessKernel_value {n : ℕ} (S : SolverData n) (o : OracleConfig) (he : 0 < o.eps1) (B : ℝ)
    (D r : Weights n) :
    numericalWitnessKernel S o he B (D,r) =
      approximateFindWitness o (boundedObjective B D) r (S.result D) :=
  deterministicWitness_run_law S.dimension o he S.solve S.feasibleValue (fun _ => rfl) B D r

def OracleTerms.Matches {Γ : List ValueType} (terms : OracleTerms Γ) (o : OracleConfig) (B : ℝ)
    (s : Environment Γ) : Prop :=
  terms.epsilon.eval s = o.eps1 ∧ terms.tau.eval s = o.tau1 ∧ terms.bound.eval s = B

theorem OracleTerms.Matches.weaken {Γ : List ValueType} {a : ValueType}
    (terms : OracleTerms Γ) (o : OracleConfig) (B : ℝ) (s : Environment Γ)
    (h : terms.Matches o B s) (x : a.Value) :
    terms.weaken.Matches o B (x,s) := by
  simpa only [OracleTerms.Matches,OracleTerms.weaken,Term.eval_weaken_env] using h

theorem witnessCommand_kernel {Γ : List ValueType} {n : ℕ} (S : SolverData n) (o : OracleConfig)
    (he : 0 < o.eps1) (B : ℝ) (terms : OracleTerms Γ) (D r : Term Γ (weightType n))
    (s : Environment Γ) (hs : terms.Matches o B s) :
    ((witnessCommand S o.k o.K terms.epsilon terms.tau terms.bound D r).code.law s).map decodeWitness =
      numericalWitnessKernel S o he B (decodeWeights (D.eval s),decodeWeights (r.eval s)) := by
  rw [witnessCommand_law S o _ _ _ _ _ _ hs.1 hs.2.1 he,hs.2.2,numericalWitnessKernel_value]

theorem numericalWitnessKernel_release {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) :
    numericalWitnessKernel (releaseSolver hn p hp) (fullRunConfig n (precisionParameters p)).oracle
      (approxConfig_bounds hn hp).eps_pos (publicObjectiveBound n (precisionParameters p)) =
        VerifiedRelease.witnessKernel hn p hp := by
  ext q : 1
  exact congrArg CostedLaw.law rfl

end DPCut.TypedMachine
