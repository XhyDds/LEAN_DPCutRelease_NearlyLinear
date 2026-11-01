import DPCut.ConstrainedCut
import DPCut.ApplicationCalibration

/-! Theorem 34, including its instantiation with Theorem 1's release. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

theorem theorem34_transfer : ConstrainedCutStatement := constrained_cut

theorem theorem34 : ∃ CA : ℝ, 0 < CA ∧ ∀ n, 2 ≤ n →
    ∀ p : Parameters, p.Valid → ∀ F F' : Set (Finset (Fin n)), F.Nonempty → F'.Nonempty →
    ∀ ρ τ : ℝ, 1 ≤ ρ → 0 ≤ τ → τ < 1 →
    ∀ K : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel K →
      (∀ h, Nonnegative h → HighProbability (K h) τ
        (fun S => S ∈ F' ∧ cut h S ≤ ρ * constrainedOptimum h F)) →
      ∃ R : Kernel (Weights n) (Finset (Fin n)), IsMarkovKernel R ∧ EdgeDP R p.epsilon p.delta ∧
        ∀ w, Nonnegative w → HighProbability (R w) (p.beta + τ)
          (fun S => S ∈ F' ∧ cut w S ≤ ρ * (1 + p.gamma) / (1 - p.gamma) * constrainedOptimum w F +
            (ρ + 1) / (1 - p.gamma) * (CA * mainError n p)) := by
  obtain ⟨CA, hCA, hm⟩ := theorem1_statistical_exists
  refine ⟨CA, hCA, fun n hn p hp F F' hF hF' ρ τ hρ hτ hτ1 K hK hAlg => ?_⟩
  obtain ⟨M, hM, hg, hDP, hu⟩ := hm n hn p hp
  letI := hM
  letI := hK
  let R : Kernel (Weights n) (Finset (Fin n)) :=
    ⟨fun w => (M w).bind K, measurable_bind_kernel M.measurable (K.measurable.comp measurable_snd)⟩
  haveI : IsMarkovKernel R := ⟨fun w => probability_bind (M w) K K.measurable⟩
  have hA : 0 ≤ CA * mainError n p := by
    have hlog := (core_log_bounds hn (le_refl (1 : ℝ)) p hp).one_le
    have hγ := hp.1
    have hε := hp.2.2.1
    unfold mainError
    positivity
  have hh := theorem34_transfer n hn F F' hF hF' p.gamma p.epsilon p.delta p.beta ρ τ
    (CA * mainError n p) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2.1
    hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2 hρ hτ hτ1 hA M K hM hK hg hDP hu hAlg
  exact ⟨R, inferInstance, hh.1, hh.2⟩

lemma minimization_ratio_slack {ρ η ξ : ℝ} (hρ : 0 ≤ ρ) (hη : η < 1)
    (hξ : 0 < ξ) (heta : η ≤ ξ / (2 * ρ + ξ)) :
    ρ * (1 + η) / (1 - η) ≤ ρ + ξ := by
  have hd : 0 < 2 * ρ + ξ := by positivity
  have hh := (le_div_iff₀ hd).mp heta
  apply (div_le_iff₀ (sub_pos.mpr hη)).mpr
  nlinarith

end DPCut
