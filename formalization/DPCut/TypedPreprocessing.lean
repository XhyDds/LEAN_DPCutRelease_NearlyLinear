import DPCut.TypedOuterLaw

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut.TypedMachine

theorem finiteLaplace_scale (n : ℕ) {epsilon : ℝ} (he : 0 < epsilon) :
    (Measure.pi (fun _ : Fin (Fintype.card (Edge n)) => DPCut.laplace 1)).map
      (fun z e => z (Fintype.equivFin (Edge n) e)/epsilon) =
        Measure.pi (fun _ : Edge n => DPCut.laplace (1/epsilon)) := by
  letI := laplace_isProbabilityMeasure (by norm_num : (0:ℝ)<1)
  have hr : (Measure.pi (fun _ : Fin (Fintype.card (Edge n)) => DPCut.laplace 1)).map
      (fun z e => z (Fintype.equivFin (Edge n) e)) =
        Measure.pi (fun _ : Edge n => DPCut.laplace 1) := by
    convert (measurePreserving_piCongrLeft (fun _ : Edge n => DPCut.laplace 1)
      (Fintype.equivFin (Edge n)).symm).map_eq using 1
    congr 1
    funext z e
    simpa using (MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Edge n => ℝ)
      (Fintype.equivFin (Edge n)).symm z (Fintype.equivFin (Edge n) e)).symm
  have hs : (DPCut.laplace 1).map (fun x => x/epsilon) = DPCut.laplace (1/epsilon) := by
    have h := laplace_scale (one_div_pos.mpr he)
    convert h using 2
    funext x
    ring
  have hpi : (Measure.pi (fun _ : Edge n => DPCut.laplace 1)).map
      (fun z e => z e/epsilon) = Measure.pi (fun _ : Edge n => DPCut.laplace (1/epsilon)) := by
    have h := Measure.pi_map_pi (μ := fun _ : Edge n => DPCut.laplace 1)
      (f := fun _ : Edge n => fun x : ℝ => x/epsilon)
      (fun _ : Edge n => (measurable_id.div_const epsilon).aemeasurable)
    simpa only [hs] using h
  have hmap := congrArg (fun μ : Measure (Weights n) => μ.map (fun z e => z e/epsilon)) hr
  dsimp only at hmap
  rw [Measure.map_map (by fun_prop) (by fun_prop),hpi] at hmap
  exact hmap

theorem preprocessCommand_law {Γ : List ValueType} (n : ℕ) (U V epsilon : Term Γ .real)
    (w : Term Γ (weightType n)) (s : Environment Γ) (he : 0 < epsilon.eval s) :
    ((preprocessCommand n U V epsilon w).code.law s).map decodeWeights =
      (Measure.pi (fun _ : Edge n => DPCut.laplace (1/epsilon.eval s))).map
        (noisyExcess (U.eval s) (V.eval s) (decodeWeights (w.eval s))) := by
  simp only [preprocessCommand,BoundedCommand.bind,BoundedCommand.pure]
  rw [law_bind_pure,scalarArray_law]
  have hm : Measurable (fun z : (weightType n).Value =>
      (noisyExcessTerm U.weaken V.weaken epsilon.weaken w.weaken newest).eval (z,s)) :=
    (Term.measurable_eval (noisyExcessTerm U.weaken V.weaken epsilon.weaken w.weaken
      (newest : Term (weightType n :: Γ) (weightType n)))).comp
        (measurable_id.prodMk (measurable_const (a:=s)))
  rw [Measure.map_map (measurable_decodeWeights n) hm]
  have hfunc : decodeWeights ∘ (fun z : (weightType n).Value =>
      (noisyExcessTerm U.weaken V.weaken epsilon.weaken w.weaken
        (newest : Term (weightType n :: Γ) (weightType n))).eval (z,s)) =
      fun z => noisyExcess (U.eval s) (V.eval s) (decodeWeights (w.eval s))
        (fun e => z (Fintype.equivFin (Edge n) e)/epsilon.eval s) := by
    funext z
    simpa only [Term.eval_weaken_env,Term.eval,newest,Local.read,decodeWeights] using
      eval_noisyExcessTerm (Γ := weightType n :: Γ) U.weaken V.weaken epsilon.weaken w.weaken newest (z,s)
  rw [hfunc]
  have hi := congrArg (fun μ : Measure (Weights n) =>
    μ.map (noisyExcess (U.eval s) (V.eval s) (decodeWeights (w.eval s)))) (finiteLaplace_scale n he)
  dsimp only at hi
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hi
  exact hi

end DPCut.TypedMachine
