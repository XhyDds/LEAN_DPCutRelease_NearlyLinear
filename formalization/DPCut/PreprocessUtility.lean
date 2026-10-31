import DPCut.PreprocessPrivacy
import DPCut.LaplaceVectorTail
import DPCut.EdgeCard

/-! The probability and simultaneous cut accuracy of preprocessing. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace DPCut

lemma preprocess_tail_calibration {n : ℕ} (hn : 2 ≤ n) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) :
    Real.exp (-noiseShift n ε β / (1 / ε)) = (β / n) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : -noiseShift n ε β / (1 / ε) =
      -(Real.log (n / β) + Real.log (n / β)) := by
    unfold noiseShift
    field_simp
    ring
  rw [he, Real.exp_neg, Real.exp_add, Real.exp_log (div_pos hn' hβ)]
  field_simp

lemma preprocess_noise_failure {n : ℕ} (hn : 2 ≤ n) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    (Measure.pi (fun _ : Edge n => laplace (1 / ε)))
      {z | ¬ ∀ e, |z e| ≤ noiseShift n ε β} ≤ ENNReal.ofReal β := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (laplace_pi_failure (one_div_pos.mpr hε) (noiseShift_pos hn hε hβ hβ1).le).trans
  apply ENNReal.ofReal_le_ofReal
  rw [preprocess_tail_calibration hn hε hβ]
  calc
    _ ≤ (n : ℝ) ^ 2 * (β / n) ^ 2 :=
      mul_le_mul_of_nonneg_right (edge_card_le_square n) (sq_nonneg _)
    _ = β ^ 2 := by field_simp
    _ ≤ β := by nlinarith

theorem preprocess_utility {n : ℕ} (hn : 2 ≤ n) {ε β γ : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ)
    (w : Weights n) (hw : Nonnegative w) :
    HighProbability (preprocessLaw ε β γ w) β
      (fun y => AllCuts w (y + clipWeights (clipThreshold n ε β γ) w) (γ / 2) 0) := by
  letI := preprocessLaw_probability hε β γ w
  have hs : MeasurableSet {y : Weights n |
      AllCuts w (y + clipWeights (clipThreshold n ε β γ) w) (γ / 2) 0} :=
    measurableSet_allCuts measurable_const (by fun_prop) _ _
  apply highProbability_of_failure hs hβ.le
  have hbad : MeasurableSet {y : Weights n |
      ¬AllCuts w (y + clipWeights (clipThreshold n ε β γ) w) (γ / 2) 0} := hs.compl
  rw [preprocessLaw, Measure.map_apply (measurable_noisyExcess _ _ _) hbad]
  apply le_trans (measure_mono ?_) (preprocess_noise_failure hn hε hβ hβ1)
  intro z hz hgood
  exact hz (noisyExcess_allCuts hγ (clipThreshold_eq ε β γ) hw hgood)

end DPCut
