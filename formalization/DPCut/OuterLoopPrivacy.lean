import DPCut.OuterLoopMeasurable
import DPCut.BasicPrivacyComposition

/-! Basic composition across outer rounds, with the residual mask invariant. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut
attribute [local instance] Classical.propDecidable

theorem outerLoop_privacy {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hinner : ∀ w w' : Weights n, Adjacent w w' → ∀ M h,
      Indistinguishable (innerLoop p c w M c.T2 h) (innerLoop p c w' M c.T2 h) ε δ)
    (w w' : Weights n) (hw : Adjacent w w') (t : ℕ) (a out : Weights n) (ha : IsMask a) :
    Indistinguishable (outerLoop p c w t a out) (outerLoop p c w' t a out)
      (t * (c.eps2 + ε)) (t * δ) := by
  induction t generalizing a out with
  | zero => exact Indistinguishable.of_eq rfl (by simp) (by simp)
  | succ t ih =>
    have hw' := hw.mask ha
    have hE : 0 ≤ ε + t * (c.eps2 + ε) := by positivity
    have hD : 0 ≤ δ + t * δ := by positivity
    have hstep (M : ℝ) : Indistinguishable (outerAfterMass p c w t a out M)
        (outerAfterMass p c w' t a out M) (ε + t * (c.eps2 + ε)) (δ + t * δ) := by
      unfold outerAfterMass
      split_ifs with hs
      · exact Indistinguishable.of_eq rfl hE hD
      · letI := innerLoop_probability hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)
        letI := innerLoop_probability hn p c ho (hadamard a w') M c.T2 (initialEstimate M a)
        letI : ∀ r, IsProbabilityMeasure (outerResult p c w t a out r) :=
          outerResult_probability hn p c ho he w a out t
        letI : ∀ r, IsProbabilityMeasure (outerResult p c w' t a out r) :=
          outerResult_probability hn p c ho he w' a out t
        apply Indistinguishable.bind_approx_on hε (by positivity) hδ (by positivity)
          (hinner _ _ hw' M (initialEstimate M a))
          (measurable_outerResult hn p c ho he w a out t)
          (measurable_outerResult hn p c ho he w' a out t)
          measurableSet_innerSupported
          (innerLoop_supported hn p c ho _ _ _ _) (innerLoop_supported hn p c ho _ _ _ _)
        intro r hr
        cases r with
        | none => exact ih a out ha
        | some pair => exact ih _ _ (residualUpdate_isMask ha hr)
    letI := noisyMassLaw_probability he c.tau2 c.massCap (hadamard a w)
    letI := noisyMassLaw_probability he c.tau2 c.massCap (hadamard a w')
    letI : ∀ M, IsProbabilityMeasure (outerAfterMass p c w t a out M) :=
      outerAfterMass_probability hn p c ho he w a out t
    letI : ∀ M, IsProbabilityMeasure (outerAfterMass p c w' t a out M) :=
      outerAfterMass_probability hn p c ho he w' a out t
    have hp := Indistinguishable.bind_approx he.le hE (le_refl 0) hD
      (noisyMassLaw_private he c.tau2 c.massCap hw')
      (measurable_outerAfterMass hn p c ho he w a out t)
      (measurable_outerAfterMass hn p c ho he w' a out t) hstep
    rw [← outerLoop_succ_noisyMass hn p c ho he w,
      ← outerLoop_succ_noisyMass hn p c ho he w'] at hp
    convert hp using 1 <;> push_cast <;> ring

end DPCut
