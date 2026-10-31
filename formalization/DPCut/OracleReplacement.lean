import DPCut.CostedProgram
import DPCut.OptimizerTV

/-! The release program with its witness kernel exposed as a parameter.
This permits replacement of the optimizer while retaining every adaptive branch. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.OracleReplacement
attribute [local instance] Classical.propDecidable

abbrev WitnessKernel (n : ℕ) := Kernel (Weights n × Weights n) (Option (Weights n))

def aggregateLoop {n : ℕ} (K : WitnessKernel n) (γ : ℝ) (w h : Weights n) :
    ℕ → Aggregate n → Measure (Aggregate n)
  | 0, a => Measure.dirac a
  | t + 1, a => if a.residual = 0 then Measure.dirac a else
      (K (plusDiscrepancy γ w h a.residual, a.residual)).bind fun gp => gp.elim
        ((K (minusDiscrepancy γ w h a.residual, a.residual)).bind fun gm =>
          gm.elim (Measure.dirac a) (fun g => aggregateLoop K γ w h t (aggregateMinusStep a g)))
        (fun g => aggregateLoop K γ w h t (aggregatePlusStep a g))

def aggregateLaw {n : ℕ} (K : WitnessKernel n) (γ : ℝ) (w h : Weights n) : Measure (Aggregate n) :=
  aggregateLoop K γ w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩

def innerLoop {n : ℕ} (K : WitnessKernel n) (p : Parameters) (c : RunConfig)
    (w : Weights n) (M : ℝ) : ℕ → Weights n → Measure (Option (Weights n × Weights n))
  | 0, _ => Measure.dirac none
  | t + 1, h => (aggregateLaw K p.gamma w h).bind fun a =>
      if a.Accepts h then Measure.dirac (some (h, a.residual)) else
        innerLoop K p c w M t (innerNext c M h a)

def outerLoop {n : ℕ} (K : WitnessKernel n) (p : Parameters) (c : RunConfig)
    (w : Weights n) : ℕ → Weights n → Weights n → Measure (Weights n)
  | 0, _, out => Measure.dirac out
  | t + 1, a, out => (laplace (1 / c.eps2)).bind fun noise =>
      let M := clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2
      if a = 0 ∨ M ≤ c.stop then Measure.dirac out else
        (innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)).bind fun r =>
          r.elim (outerLoop K p c w t a out)
            (fun hr => outerLoop K p c w t (residualUpdate a hr.2) (out + hadamard hr.1 hr.2))

def outerResult {n : ℕ} (K : WitnessKernel n) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) (r : Option (Weights n × Weights n)) :=
  r.elim (outerLoop K p c w t a out)
    (fun hr => outerLoop K p c w t (residualUpdate a hr.2) (out + hadamard hr.1 hr.2))

def outerAfterMass {n : ℕ} (K : WitnessKernel n) (p : Parameters) (c : RunConfig)
    (w : Weights n) (t : ℕ) (a out : Weights n) (M : ℝ) :=
  if a = 0 ∨ M ≤ c.stop then Measure.dirac out else
    (innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)).bind (outerResult K p c w t a out)

def fullRelease {n : ℕ} (K : WitnessKernel n) (p : Parameters) (w : Weights n) : Measure (Weights n) :=
  let U := preprocessingThreshold n p
  let c := runConfig n U (boundedParameters p) outerUtilityConstants
  (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w).bind fun y =>
    (outerLoop K (boundedParameters p) c (clipWeights U w) c.T1 1 0).map (fun h => h + y)

end DPCut.OracleReplacement
