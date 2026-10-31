import DPCut.FindWitnessPrivacy

/-! Support and the per-success accounting inequality for the witness oracle. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

def WitnessSupported {n : ℕ} (r q : Weights n) (y : Option (Weights n)) : Prop :=
  y.elim True (fun g => ∀ e, 0 ≤ g e ∧ g e ≤ r e ∧ r e * q e ≤ 8 * g e)

lemma measurableSet_witnessSupported {n : ℕ} (r q : Weights n) :
    MeasurableSet {y | WitnessSupported r q y} := by
  apply measurableSet_option_elim
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro e
  exact (measurableSet_le measurable_const (measurable_pi_apply e)).inter
    ((measurableSet_le (measurable_pi_apply e) measurable_const).inter
      (measurableSet_le measurable_const ((measurable_pi_apply e).const_mul 8)))

lemma acceptTrial_supported {n : ℕ} (o : OracleConfig) (r q : Weights n) (hr : IsMask r)
    (p : TrialSample n o.k) (hgood : ∀ e, q e / 8 ≤ clippedWitness p.1 e) :
    WitnessSupported r q (acceptTrial o r p) := by
  unfold acceptTrial
  split_ifs with hp
  · intro e
    exact ⟨(normalizeWitness_bounds hr (fun e => (clippedWitness_bounds p.1 e).1) hp.2 e).1,
      (normalizeWitness_bounds hr (fun e => (clippedWitness_bounds p.1 e).1) hp.2 e).2,
      normalized_witness_charge hr hgood (clippedWitness_bounds p.1) hp.2 e⟩
  · trivial

theorem auxiliaryFindWitness_supported {n : ℕ} (o : OracleConfig)
    (D D' ζ r : Weights n) (hr : IsMask r) :
    ∀ᵐ y ∂auxiliaryFindWitness o D D' ζ r,
      WitnessSupported r (queryMax (optimizer o.lam D) (optimizer o.lam D')) y := by
  unfold auxiliaryFindWitness
  split_ifs
  · exact (ae_dirac_iff (measurableSet_witnessSupported _ _)).mpr trivial
  · apply repeatUntil_ae (measurable_acceptTrial_fixed o r)
      (measurableSet_witnessSupported _ _) trivial
    apply ae_cond_of_forall_mem (measurableSet_trialGood o D D' ζ r)
    intro p hp
    exact acceptTrial_supported o r _ hr p (fun e => (hp.2 e).1)

theorem findWitness_supported {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D r : Weights n) (hr : IsMask r) :
    ∀ᵐ y ∂findWitness o D r, WitnessSupported r 0 y := by
  unfold findWitness
  split_ifs
  · exact (ae_dirac_iff (measurableSet_witnessSupported _ _)).mpr trivial
  · rw [findTrials_eq_repeatUntil o he]
    apply repeatUntil_ae (measurable_acceptTrial_fixed o r)
      (measurableSet_witnessSupported _ _) trivial
    exact Filter.Eventually.of_forall fun p => acceptTrial_supported o r 0 hr p
      (fun e => by simpa using (clippedWitness_bounds p.1 e).1)

lemma witness_supported_residual {n : ℕ} (r q g : Weights n) (hr : IsMask r)
    (hg : WitnessSupported r q (some g)) : IsMask (r - g) := by
  intro e
  obtain ⟨h0, h1, _⟩ := hg e
  change 0 ≤ r e - g e ∧ r e - g e ≤ 1
  constructor <;> linarith [(hr e).1, (hr e).2]

lemma witness_success_charge {n : ℕ} (o : OracleConfig) (he : 0 ≤ o.eps1)
    (ζ r q g : Weights n) (hg : WitnessSupported r q (some g)) :
    10 * o.K * o.eps1 * (∑ e, |ζ e| * r e * q e) ≤
      80 * o.K * o.eps1 * pairing (fun e => |ζ e|) g := by
  have h : (∑ e, |ζ e| * r e * q e) ≤ 8 * pairing (fun e => |ζ e|) g := by
    rw [pairing, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    nlinarith [mul_le_mul_of_nonneg_left (hg e).2.2 (abs_nonneg (ζ e))]
  have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ 10 * o.K * o.eps1 by positivity)
  nlinarith

end DPCut
