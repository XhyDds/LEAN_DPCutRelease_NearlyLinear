import DPCut.CappedOuterLoop
import DPCut.BasicPrivacyComposition

/-! Basic composition across outer rounds, with the residual mask invariant. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut
attribute [local instance] Classical.propDecidable

theorem cappedOuterLoop_privacy {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hinner : ∀ w w' : Weights n, Adjacent w w' → ∀ a M h,
      Indistinguishable (cappedInnerLoop p c w a M c.T2 h) (cappedInnerLoop p c w' a M c.T2 h) ε δ)
    (w w' : Weights n) (hw : Adjacent w w') (t : ℕ) (a out : Weights n) (ha : IsMask a) :
    Indistinguishable (cappedOuterLoop p c w t a out) (cappedOuterLoop p c w' t a out)
      (t * (c.eps2 + ε)) (t * δ) := by
  induction t generalizing a out with
  | zero => exact Indistinguishable.of_eq rfl (by simp) (by simp)
  | succ t ih =>
    have hw' := hw.mask ha
    have hE : 0 ≤ ε + t * (c.eps2 + ε) := by positivity
    have hD : 0 ≤ δ + t * δ := by positivity
    have hstep (M : ℝ) : Indistinguishable (cappedOuterAfterMass p c w t a out M)
        (cappedOuterAfterMass p c w' t a out M) (ε + t * (c.eps2 + ε)) (δ + t * δ) := by
      unfold cappedOuterAfterMass
      split_ifs with hs
      · exact Indistinguishable.of_eq rfl hE hD
      · letI := cappedInnerLoop_probability hn p c ho (hadamard a w) a M c.T2 (initialEstimate M a)
        letI := cappedInnerLoop_probability hn p c ho (hadamard a w') a M c.T2 (initialEstimate M a)
        letI : ∀ r, IsProbabilityMeasure (cappedOuterResult p c w t a out r) :=
          cappedOuterResult_probability hn p c ho he w a out t
        letI : ∀ r, IsProbabilityMeasure (cappedOuterResult p c w' t a out r) :=
          cappedOuterResult_probability hn p c ho he w' a out t
        apply Indistinguishable.bind_approx_on hε (by positivity) hδ (by positivity)
          (hinner _ _ hw' a M (initialEstimate M a))
          (measurable_cappedOuterResult hn p c ho he w a out t)
          (measurable_cappedOuterResult hn p c ho he w' a out t)
          measurableSet_innerSupported
          (cappedInnerLoop_supported hn p c ho _ _ _ _ _) (cappedInnerLoop_supported hn p c ho _ _ _ _ _)
        intro r hr
        cases r with
        | none => exact ih a out ha
        | some pair => exact ih _ _ (residualUpdate_isMask ha hr)
    letI := cappedNoisyMassLaw_probability he c.tau2 (mass a) (hadamard a w)
    letI := cappedNoisyMassLaw_probability he c.tau2 (mass a) (hadamard a w')
    letI : ∀ M, IsProbabilityMeasure (cappedOuterAfterMass p c w t a out M) :=
      cappedOuterAfterMass_probability hn p c ho he w a out t
    letI : ∀ M, IsProbabilityMeasure (cappedOuterAfterMass p c w' t a out M) :=
      cappedOuterAfterMass_probability hn p c ho he w' a out t
    have hp := Indistinguishable.bind_approx he.le hE (le_refl 0) hD
      (cappedNoisyMassLaw_private he c.tau2 (mass a) hw')
      (measurable_cappedOuterAfterMass hn p c ho he w a out t)
      (measurable_cappedOuterAfterMass hn p c ho he w' a out t) hstep
    rw [← cappedOuterLoop_succ_noisyMass hn p c ho he w,
      ← cappedOuterLoop_succ_noisyMass hn p c ho he w'] at hp
    convert hp using 1 <;> push_cast <;> ring

end DPCut
