import DPCut.FullReleaseLaw

/-! Basic composition of preprocessing and the clipped bounded release. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

theorem fullRelease_private {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    EdgeDP (fullReleaseLaw (n := n) p outerUtilityConstants) p.epsilon p.delta := by
  intro w w' hw
  have he : 0 < p.epsilon / 2 := by linarith [hp.2.2.1]
  have hd : 0 ≤ p.delta := hp.2.2.2.2.1.le
  have hsym : Adjacent w' w := by simpa only [Adjacent, l1, Pi.sub_apply, abs_sub_comm] using hw.2.2
  have hpre : Indistinguishable
      (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w)
      (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w') (p.epsilon / 2) 0 :=
    ⟨preprocess_private he _ _ w w' hw,
      preprocess_private he _ _ w' w ⟨hw.2.1, hw.1, hsym⟩⟩
  letI := preprocessLaw_probability he (p.beta / 2) p.gamma w
  letI := preprocessLaw_probability he (p.beta / 2) p.gamma w'
  letI (y : Weights n) : IsProbabilityMeasure (fullReleaseContinuation p w y) :=
    fullReleaseContinuation_probability hn hp w y
  letI (y : Weights n) : IsProbabilityMeasure (fullReleaseContinuation p w' y) :=
    fullReleaseContinuation_probability hn hp w' y
  have hcut := cutRelease_shared_private hn (preprocessingThreshold_one_le hn hp)
    (boundedParameters p) (boundedParameters_valid hp).privacyValid _ _
    (hw.2.2.clipWeights (preprocessingThreshold n p))
  have hfg (y : Weights n) : Indistinguishable (fullReleaseContinuation p w y)
      (fullReleaseContinuation p w' y) (p.epsilon / 2) p.delta :=
    hcut.map (show Measurable (fun h : Weights n => h + y) by fun_prop)
  have hcomp := Indistinguishable.bind_approx
    (f := fullReleaseContinuation p w) (g := fullReleaseContinuation p w')
    he.le he.le (le_refl 0) hd hpre
    ((measurable_fullReleaseContinuation hn hp).comp measurable_prodMk_left)
    ((measurable_fullReleaseContinuation hn hp).comp measurable_prodMk_left) hfg
  have hout : Indistinguishable (fullReleaseLaw p outerUtilityConstants w)
      (fullReleaseLaw p outerUtilityConstants w') p.epsilon p.delta := by
    simpa only [add_halves, zero_add] using hcomp
  exact hout.1

end DPCut
