import DPCut.TypedPreprocessing

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

theorem fullAfterPreprocessing_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (he2 : 0 < c.eps2) (B : ℝ) (terms : RunTerms Γ)
    (U : Term Γ .real) (w : Term Γ (weightType n)) (s : Environment Γ)
    (hs : terms.Matches p c B s) (y : (weightType n).Value) :
    ((Command.bind (outerCommand S c.oracle.k c.oracle.K c.T1 c.T2 terms.weaken (clipWeightsTerm U w).weaken).code
      (Command.pure (positiveTerm (addWeights newest (.read (.tail .head)))))).law (y,s)).map decodeWeights =
      (OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
        (clipWeights (U.eval s) (decodeWeights (w.eval s))) c.T1 1 0).map
          (fun h => positiveWeights (h+decodeWeights y)) := by
  let value : Term (weightType n :: weightType n :: Γ) (weightType n) :=
    positiveTerm (addWeights newest (.read (.tail .head)))
  rw [law_bind_pure]
  have hv : Measurable (fun h : (weightType n).Value => value.eval (h,y,s)) :=
    value.measurable_eval.comp (measurable_id.prodMk (measurable_const (a:=(y,s))))
  rw [Measure.map_map (measurable_decodeWeights n) hv]
  have hfunc : decodeWeights ∘ (fun h : (weightType n).Value => value.eval (h,y,s)) =
      fun h => positiveWeights (decodeWeights h+decodeWeights y) := by
    funext h
    simp [value,eval_positiveTerm,eval_addWeights,Term.eval,newest,Local.read]
  rw [hfunc]
  have hf : Measurable (fun h : Weights n => positiveWeights (h+decodeWeights y)) := by fun_prop
  change (((outerCommand S c.oracle.k c.oracle.K c.T1 c.T2 terms.weaken (clipWeightsTerm U w).weaken).code.law
    (y,s)).map ((fun h : Weights n => positiveWeights (h+decodeWeights y)) ∘ decodeWeights)) = _
  rw [← Measure.map_map hf (measurable_decodeWeights n)]
  have hs0 : (terms.weaken : RunTerms (weightType n :: Γ)).Matches p c B (y,s) :=
    RunTerms.Matches.weaken (a := weightType n) terms p c B s hs y
  rw [outerCommand_law S p c he he2 B terms.weaken (clipWeightsTerm U w).weaken (y,s) hs0]
  simp only [Term.eval_weaken_env,eval_clipWeightsTerm]

theorem fullCommand_law {Γ : List ValueType} {n : ℕ} (S : SolverData n) (p : Parameters) (c : RunConfig)
    (he : 0 < c.oracle.eps1) (he2 : 0 < c.eps2) (B : ℝ) (terms : RunTerms Γ)
    (U V epsilon : Term Γ .real) (w : Term Γ (weightType n)) (s : Environment Γ)
    (hs : terms.Matches p c B s) (hepsilon : 0 < epsilon.eval s) :
    ((fullCommand S c.oracle.k c.oracle.K c.T1 c.T2 terms U V epsilon w).code.law s).map decodeWeights =
      (((Measure.pi (fun _ : Edge n => DPCut.laplace (1/epsilon.eval s))).map
          (noisyExcess (U.eval s) (V.eval s) (decodeWeights (w.eval s)))).bind fun y =>
        (OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
          (clipWeights (U.eval s) (decodeWeights (w.eval s))) c.T1 1 0).map (fun h => h+y)).map positiveWeights := by
  let rest : Command (weightType n :: Γ) (weightType n) :=
    Command.bind (outerCommand S c.oracle.k c.oracle.K c.T1 c.T2 terms.weaken (clipWeightsTerm U w).weaken).code
      (Command.pure (positiveTerm (addWeights newest (.read (.tail .head)))))
  change ((Command.bind (preprocessCommand n U V epsilon w).code rest).law s).map decodeWeights = _
  rw [Command.law_bind]
  have hm : Measurable (fun y : (weightType n).Value => rest.law (y,s)) :=
    rest.measurable_law.comp (measurable_id.prodMk (measurable_const (a:=s)))
  rw [map_bind_eq hm (measurable_decodeWeights n)]
  have hrest (y : (weightType n).Value) : (rest.law (y,s)).map decodeWeights =
      (OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
        (clipWeights (U.eval s) (decodeWeights (w.eval s))) c.T1 1 0).map
          (fun h => positiveWeights (h+decodeWeights y)) :=
    fullAfterPreprocessing_law S p c he he2 B terms U w s hs y
  change ((preprocessCommand n U V epsilon w).code.law s).bind
    (fun y => (rest.law (y,s)).map decodeWeights) = _
  simp_rw [hrest]
  let outer := OracleReplacement.outerLoop (numericalWitnessKernel S c.oracle he B) p c
    (clipWeights (U.eval s) (decodeWeights (w.eval s))) c.T1 1 0
  letI : IsProbabilityMeasure outer := OracleReplacement.outerLoop_probability _ p c he2 _ _ _ _
  have hcont : Measurable (fun y : Weights n => outer.map (fun h => positiveWeights (h+y))) :=
    measurable_map_kernel measurable_const (by fun_prop)
  rw [← bind_map_eq (measurable_decodeWeights n) hcont,preprocessCommand_law n U V epsilon w s hepsilon]
  have hplain : Measurable (fun y : Weights n => outer.map (fun h => h+y)) :=
    measurable_map_kernel measurable_const (by fun_prop)
  rw [map_bind_eq hplain measurable_positiveWeights]
  congr 1
  funext y
  rw [Measure.map_map measurable_positiveWeights (by fun_prop)]
  rfl

end DPCut.TypedMachine
