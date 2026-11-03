import DPCut.TypedOuterContinuation

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

def outerMassContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig)
    (w a output : Weights n) (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (M : ℝ) : Measure β :=
  if a = 0 ∨ M ≤ c.stop then F0 output else
    (OracleReplacement.innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)).bind
      (outerInnerContinuation F1 a output)

theorem measurable_outerMassContinuation {n : ℕ} {β : Type*} [MeasurableSpace β]
    (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (w a output : Weights n) (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h1 : Measurable F1) : Measurable (outerMassContinuation K p c w a output F0 F1) := by
  have hi : Measurable (fun M : ℝ =>
      OracleReplacement.innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    OracleReplacement.measurable_innerLoop K p c c.T2 measurable_const (by fun_prop) measurable_id
  have hc : Measurable (fun q : ℝ × Option (Weights n × Weights n) => outerInnerContinuation F1 a output q.2) :=
    (measurable_outerInnerContinuation F1 h1 a output).comp measurable_snd
  letI (M : ℝ) : IsProbabilityMeasure
      (OracleReplacement.innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    OracleReplacement.innerLoop_probability K p c _ _ _ _
  have hprop : MeasurableSet {M : ℝ | a = 0} := by
    by_cases ha : a = 0
    · simpa only [ha,Set.setOf_true] using (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
    · simpa only [ha,Set.setOf_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set ℝ))
  apply Measurable.ite
  · exact hprop.union (measurableSet_le measurable_id measurable_const)
  · exact measurable_const
  · exact measurable_bind_kernel hi hc

theorem outerAfterNoise_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (S : SolverData n) (p : Parameters) (c : RunConfig) (he : 0 < c.oracle.eps1) (B : ℝ)
    (terms : RunTerms Γ) (w a output : Term Γ (weightType n)) (noise : Term Γ .real)
    (s : Environment Γ) (hs : terms.Matches p c B s)
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h0 : Measurable F0) (h1 : Measurable F1) :
    ((outerAfterNoise S c.oracle.k c.oracle.K c.T2 terms w a output noise).code.law s).bind
        (outerContinuation F0 F1) =
      outerMassContinuation (numericalWitnessKernel S c.oracle he B) p c
        (decodeWeights (w.eval s)) (decodeWeights (a.eval s)) (decodeWeights (output.eval s)) F0 F1
        (clipNoisyMass c.massCap (mass (hadamard (decodeWeights (a.eval s)) (decodeWeights (w.eval s))))
          (noise.eval s/c.eps2) c.tau2) := by
  simp only [outerAfterNoise,BoundedCommand.bind,BoundedCommand.pure]
  rw [law_bind_pure_first]
  let M := (noisyMassTerm terms.massCap (massTerm (productWeights a w)) (noise/terms.epsilon) terms.tau).eval s
  have hs0 : (terms.weaken : RunTerms (.real :: Γ)).Matches p c B (M,s) :=
    RunTerms.Matches.weaken (a := .real) terms p c B s hs M
  have h := outerAfterMass_continue S p c he B terms.weaken w.weaken a.weaken output.weaken newest (M,s) hs0
    F0 F1 h0 h1
  simp only [Term.eval_weaken_env,newest,Term.eval,Local.read] at h
  have hM : M = clipNoisyMass c.massCap (mass (hadamard (decodeWeights (a.eval s)) (decodeWeights (w.eval s))))
      (noise.eval s/c.eps2) c.tau2 := by
    simp only [M,eval_noisyMassTerm,eval_massTerm,eval_productWeights,Term.eval,RealBinary.eval,
      hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1]
  change ((outerAfterMass S c.oracle.k c.oracle.K c.T2 terms.weaken w.weaken a.weaken output.weaken newest).code.law
    (M,s)).bind (outerContinuation F0 F1) = _
  rw [← hM]
  simpa only [outerMassContinuation,newest] using h

theorem outerStep_continue {Γ : List ValueType} {n : ℕ} {β : Type*} [MeasurableSpace β]
    (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (he2 : 0 < c.eps2) (B : ℝ) (terms : RunTerms Γ)
    (w : Term Γ (weightType n)) (s : Environment Γ) (hs : terms.Matches p c B s)
    (a output : (weightType n).Value)
    (F0 : Weights n → Measure β) (F1 : Weights n × Weights n → Measure β)
    (h0 : Measurable F0) (h1 : Measurable F1) :
    ((outerStep S c.oracle.k c.oracle.K c.T2 terms w).code.law ((false,(a,output)),s)).bind
        (outerContinuation F0 F1) =
      (DPCut.laplace (1/c.eps2)).bind (fun noise =>
        outerMassContinuation (numericalWitnessKernel S c.oracle he B) p c
          (decodeWeights (w.eval s)) (decodeWeights a) (decodeWeights output) F0 F1
          (clipNoisyMass c.massCap (mass (hadamard (decodeWeights a) (decodeWeights (w.eval s)))) noise c.tau2)) := by
  have hC := measurable_outerContinuation F0 F1 h0 h1
  simp only [outerStep,BoundedCommand.branch,BoundedCommand.bind,BoundedCommand.pure,BoundedCommand.laplace,
    Command.law_branch,Term.eval,newest,Local.read,Bool.false_eq_true,ite_false]
  rw [law_bind_continue _ _ _ _ hC,Command.law_laplace]
  have hs0 : (terms.weaken : RunTerms (outerStateType n :: Γ)).Matches p c B ((false,(a,output)),s) :=
    RunTerms.Matches.weaken (a := outerStateType n) terms p c B s hs (false,(a,output))
  let aTerm : Term (outerStateType n :: Γ) (weightType n) := .fst (.snd newest)
  let outputTerm : Term (outerStateType n :: Γ) (weightType n) := .snd (.snd newest)
  have hnoise (noise : ℝ) := outerAfterNoise_continue (Γ := .real :: outerStateType n :: Γ) S p c he B
    terms.weaken.weaken w.weaken.weaken aTerm.weaken outputTerm.weaken newest
    (noise,(false,(a,output)),s)
    (RunTerms.Matches.weaken (a := .real) (terms.weaken : RunTerms (outerStateType n :: Γ))
      p c B ((false,(a,output)),s) hs0 noise) F0 F1 h0 h1
  simp only [Term.eval_weaken_env,Term.eval,newest,Local.read,aTerm,outputTerm] at hnoise
  simp_rw [hnoise]
  let F : ℝ → Measure β := fun noise =>
    outerMassContinuation (numericalWitnessKernel S c.oracle he B) p c
      (decodeWeights (w.eval s)) (decodeWeights a) (decodeWeights output) F0 F1
      (clipNoisyMass c.massCap (mass (hadamard (decodeWeights a) (decodeWeights (w.eval s)))) noise c.tau2)
  have hF : Measurable F :=
    (measurable_outerMassContinuation _ p c _ _ _ F0 F1 h1).comp (by fun_prop)
  rw [← laplace_scale (one_div_pos.mpr he2),bind_map_eq (by fun_prop) hF]
  congr 1
  funext noise
  congr 1
  ring

end DPCut.TypedMachine
