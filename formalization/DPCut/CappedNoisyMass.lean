import DPCut.NoisyMassPrivacy
import DPCut.CappedProgress
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

@[fun_prop] lemma measurable_lowerBiasedMass {X : Type*} [MeasurableSpace X]
    {capacity M noise τ : X → ℝ} (hc : Measurable capacity) (hM : Measurable M)
    (hn : Measurable noise) (ht : Measurable τ) :
    Measurable (fun x => lowerBiasedMass (capacity x) (M x) (noise x) (τ x)) := by
  unfold lowerBiasedMass
  fun_prop

def cappedNoisyMassLaw {n : ℕ} (ε τ capacity : ℝ) (w : Weights n) : Measure ℝ :=
  (laplace (1 / ε)).map (fun noise => lowerBiasedMass capacity (mass w) noise τ)

lemma cappedNoisyMassLaw_probability {n : ℕ} {ε : ℝ} (hε : 0 < ε) (τ capacity : ℝ) (w : Weights n) :
    IsProbabilityMeasure (cappedNoisyMassLaw ε τ capacity w) := by
  letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / ε)
  exact Measure.isProbabilityMeasure_map (by unfold lowerBiasedMass; fun_prop)

lemma cappedNoisyMassLaw_private {n : ℕ} {ε : ℝ} (hε : 0 < ε) (τ capacity : ℝ)
    {w w' : Weights n} (hw : Adjacent w w') :
    Indistinguishable (cappedNoisyMassLaw ε τ capacity w) (cappedNoisyMassLaw ε τ capacity w') ε 0 := by
  have hp := (shifted_laplace_private hε (mass_sensitivity hw)).map
    (show Measurable (fun x : ℝ => max 0 (min capacity (x - τ))) by fun_prop)
  have hm : Measurable (fun x : ℝ => max 0 (min capacity (x - τ))) := by fun_prop
  rw [Measure.map_map hm (show Measurable (fun x : ℝ => mass w + x) by fun_prop),
    Measure.map_map hm (show Measurable (fun x : ℝ => mass w' + x) by fun_prop)] at hp
  exact hp

end DPCut
