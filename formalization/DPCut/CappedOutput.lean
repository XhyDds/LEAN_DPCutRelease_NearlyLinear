import DPCut.CappedReleasePrivacy

/-! The actual capped release preserves the cap almost surely, independently
of every accuracy event. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

def BelowCap {n : ℕ} (cap h : Weights n) : Prop :=
  Nonnegative h ∧ ∀ e, h e ≤ cap e

lemma measurableSet_belowCap {n : ℕ} (cap : Weights n) :
    MeasurableSet {h | BelowCap cap h} := by
  change MeasurableSet ({h | Nonnegative h} ∩ {h | ∀ e, h e ≤ cap e})
  apply (measurableSet_nonnegative measurable_id).inter
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun e => measurableSet_le (measurable_pi_apply e) measurable_const

theorem cappedOuterLoop_belowCap {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (hstop : 0 ≤ c.stop)
    (w cap : Weights n) (t : ℕ) (a out : Weights n) (ha : IsMask a)
    (hout : Nonnegative out) (hcap : ∀ e, out e + a e ≤ cap e) :
    ∀ᵐ h ∂cappedOuterLoop p c w t a out, BelowCap cap h := by
  have houtcap : BelowCap cap out := ⟨hout, fun e => by linarith [hcap e, (ha e).1]⟩
  induction t generalizing a out with
  | zero => exact (ae_dirac_iff (measurableSet_belowCap cap)).mpr houtcap
  | succ t ih =>
    rw [cappedOuterLoop_succ_raw]
    apply ae_bind_of_ae_ae
      ((measurable_cappedOuterAfterMass hn p c ho he w a out t).comp (by fun_prop))
      (measurableSet_belowCap cap)
    apply Filter.Eventually.of_forall
    intro z
    dsimp only [Function.comp_def]
    unfold cappedOuterAfterMass
    split_ifs with hdone
    · exact (ae_dirac_iff (measurableSet_belowCap cap)).mpr houtcap
    · let H := lowerBiasedMass (mass a) (mass (hadamard a w)) z c.tau2
      have hH : 0 < H := hstop.trans_lt (lt_of_not_ge (fun h => hdone (Or.inr h)))
      have hbound : 0 ≤ H ∧ H ≤ mass a :=
        lowerBiasedMass_bounds (show 0 ≤ mass a from Finset.sum_nonneg fun e _ => (ha e).1)
      have hHa : H ≤ mass a := hbound.2
      apply ae_bind_of_ae_ae (measurable_cappedOuterResult hn p c ho he w a out t)
        (measurableSet_belowCap cap)
      filter_upwards [cappedInnerLoop_valid hn p c ho (hadamard a w) a H
        (fun e => (ha e).1) hH hHa c.T2 (initialEstimate H a)
        (initialEstimate_capped_valid (fun e => (ha e).1) hH hHa)] with r hr
      cases r with
      | none => exact ih a out ha hout hcap houtcap
      | some pair =>
        obtain ⟨hh, hm⟩ := hr
        have hnew : Nonnegative (out + hadamard pair.1 pair.2) :=
          fun e => add_nonneg (hout e) (mul_nonneg (hh.1 e) (hm e).1)
        have hnewcap : ∀ e, (out + hadamard pair.1 pair.2) e + (residualUpdate a pair.2) e ≤ cap e := by
          intro e
          have hmul := mul_le_mul_of_nonneg_right (hh.2.2.1 e) (hm e).1
          change out e + pair.1 e * pair.2 e + a e * (1 - pair.2 e) ≤ cap e
          nlinarith [hcap e]
        apply ih _ _ (residualUpdate_isMask ha hm) hnew hnewcap
        exact ⟨hnew, fun e => by
          have hpos := (residualUpdate_isMask ha hm e).1
          linarith [hnewcap e]⟩

def supportMask {n : ℕ} (D : Finset (Edge n)) : Weights n := fun e => if e ∈ D then 1 else 0

lemma supportMask_isMask {n : ℕ} (D : Finset (Edge n)) : IsMask (supportMask D) := by
  intro e
  simp only [supportMask]
  split <;> norm_num

lemma belowCap_supportMask {n : ℕ} (D : Finset (Edge n)) {h : Weights n}
    (hh : BelowCap (supportMask D) h) : CappedOn D h := by
  refine ⟨fun e => ⟨hh.1 e, (hh.2 e).trans (supportMask_isMask D e).2⟩, ?_⟩
  intro e he
  apply le_antisymm _ (hh.1 e)
  simpa [supportMask, he] using hh.2 e

lemma supportMask_input {n : ℕ} {D : Finset (Edge n)} {w : Weights n} (hw : CappedOn D w) :
    hadamard (supportMask D) w = w := by
  funext e
  by_cases he : e ∈ D
  · simp [hadamard, supportMask, he]
  · simp [hadamard, supportMask, he, hw.2 e he]

end DPCut
