import DPCut.LaplaceVector
import DPCut.PreprocessAlgebra

/-! The actual preprocessing law releases only the postprocessed excess vector. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace DPCut

lemma preprocessLaw_probability {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (β γ : ℝ) (w : Weights n) : IsProbabilityMeasure (preprocessLaw ε β γ w) := by
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hε)
  exact Measure.isProbabilityMeasure_map (measurable_noisyExcess _ _ _).aemeasurable

theorem preprocess_private {n : ℕ} {ε : ℝ} (hε : 0 < ε) (β γ : ℝ) :
    EdgeDP (preprocessLaw (n := n) ε β γ) ε 0 := by
  intro w w' hw
  let U := clipThreshold n ε β γ
  let V := noiseShift n ε β
  have hpriv := shifted_laplace_pi_private hε (excess U w) (excess U w') (hw.2.2.excess U)
  have hm : Measurable (fun x : Weights n => fun e => max 0 (x e - V)) := by fun_prop
  have hp := hpriv.map hm
  rw [Measure.map_map hm (by fun_prop), Measure.map_map hm (by fun_prop)] at hp
  exact hp.1

end DPCut
