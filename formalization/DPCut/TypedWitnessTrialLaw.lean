import DPCut.TypedWitnessProgram
import DPCut.OptimizerTV

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine
attribute [local instance] Classical.propDecidable

@[fun_prop] theorem measurable_decodeWitness (n : ℕ) : Measurable (decodeWitness (n:=n)) :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    (measurable_some.comp ((measurable_decodeWeights n).comp measurable_snd)) measurable_const

theorem trialSampleCommand_law {Γ : List ValueType} (n : ℕ) (o : OracleConfig)
    (epsilon : Term Γ .real) (D : Term Γ (weightType n)) (X : Term Γ (matrixType n))
    (s : Environment Γ) (he : epsilon.eval s = o.eps1) (hepos : 0 < o.eps1)
    (hX : Matrix.PosDef (X.eval s)) :
    (trialSampleCommand n o.k epsilon D X).code.law s =
      approximateTrialLaw o (decodeWeights (D.eval s)) (X.eval s) := by
  let d := decodeWeights (D.eval s)
  letI := laplace_isProbabilityMeasure (by norm_num : (0:ℝ)<1)
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hepos)
  let continuation : Command (batchType n o.k :: Γ) (trialType n o.k) :=
    Command.bind Command.laplace (Command.pure
      (.pair (.read (.tail .head))
        (pairingTerm D.weaken.weaken (clippedWitnessTerm n o.k (.read (.tail .head))) +
          newest/epsilon.weaken.weaken)))
  change (Command.bind (gaussianCommand n o.k X).code continuation).law s = _
  rw [Command.law_bind,gaussianCommand_law n o.k X s hX]
  have hnoise (z : Fin o.k → Fin n → ℝ) :
      continuation.law (z,s) =
        (DPCut.laplace (1/o.eps1)).map (fun noise => (z,pairing d (clippedWitness z)+noise)) := by
    dsimp only [continuation]
    rw [Command.law_bind,Command.law_laplace]
    simp only [Command.law_pure, Term.eval, RealBinary.eval, newest, Local.read,
      Term.eval_weaken_env, eval_pairingTerm, eval_clippedWitnessTerm, he]
    change (DPCut.laplace 1).bind (fun x => Measure.dirac (z,pairing d (clippedWitness z)+x/o.eps1)) = _
    have hf : Measurable (fun noise : ℝ => (z,pairing d (clippedWitness z)+noise/o.eps1)) := by fun_prop
    rw [Measure.bind_dirac_eq_map _ hf]
    rw [← laplace_scale (one_div_pos.mpr hepos), Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext noise
    simp only [Function.comp_apply]
    congr 2
    ring
  simp_rw [hnoise]
  unfold approximateTrialLaw
  rw [Measure.prod, map_bind_eq Measurable.map_prodMk_left (scoreShear d).measurable]
  congr 1
  funext z
  rw [Measure.map_map (scoreShear d).measurable measurable_prodMk_left]
  rfl

end DPCut.TypedMachine
