import DPCut.CappedReplacement

/-! Uniform witness approximation error through both capped adaptive loops. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.CappedReplacement
open OracleReplacement (WitnessKernel aggregateLaw aggregateLoop aggregateLoop_probability aggregateLoop_tv)
attribute [local instance] Classical.propDecidable innerLoop_probability
variable {n : ℕ} (K H : WitnessKernel n) [IsMarkovKernel K] [IsMarkovKernel H]
variable {η : ℝ} (hη : 0 ≤ η) (hKH : ∀ q, TVClose (K q) (H q) η)
include hη hKH

theorem innerLoop_tv (p : Parameters) (c : RunConfig) (w u : Weights n) (M : ℝ)
    (t : ℕ) (h : Weights n) :
    TVClose (innerLoop K p c w u M t h) (innerLoop H p c w u M t h)
      (t * ((Fintype.card (Edge n) : ℝ) * (2 * η))) := by
  let E : ℝ := Fintype.card (Edge n) * (2 * η)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  induction t generalizing h with
  | zero => exact TVClose.refl _ (by simp)
  | succ t ih =>
    rw [innerLoop, innerLoop]
    let f (J : WitnessKernel n) (a : Aggregate n) :=
      if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop J p c w u M t (cappedNext c u M h a)
    have hi (J : WitnessKernel n) [IsMarkovKernel J] : ∀ a, IsProbabilityMeasure (f J a) := by as_aux_lemma =>
      intro a
      dsimp [f]
      split_ifs
      · infer_instance
      · exact innerLoop_probability J p c w u M t _
    letI := hi K
    letI := hi H
    have hf (a) : TVClose (f K a) (f H a) (t * E) := by
      dsimp [f]
      split_ifs
      · exact TVClose.refl _ (by positivity)
      · exact ih _
    letI := OracleReplacement.aggregateLoop_probability K p.gamma w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩
    letI := OracleReplacement.aggregateLoop_probability H p.gamma w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩
    have ht := (aggregateLoop_tv K H hη hKH p.gamma w h (Fintype.card (Edge n))
      ⟨0, 0, 1⟩).bind (f := f K) (g := f H) (by positivity : 0 ≤ (t : ℝ) * E)
      (measurable_inner_continuation K p c w u h M t)
      (measurable_inner_continuation H p c w u h M t) hf
    change TVClose ((OracleReplacement.aggregateLaw K p.gamma w h).bind (f K))
      ((OracleReplacement.aggregateLaw H p.gamma w h).bind (f H)) ((t + 1 : ℕ) * E)
    rw [show ((t + 1 : ℕ) : ℝ) * E = E + t * E by push_cast; ring]
    exact ht

theorem outerLoop_tv (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    TVClose (outerLoop K p c w t a out) (outerLoop H p c w t a out)
      (t * (c.T2 * ((Fintype.card (Edge n) : ℝ) * (2 * η)))) := by
  let E : ℝ := c.T2 * ((Fintype.card (Edge n) : ℝ) * (2 * η))
  have hE : 0 ≤ E := by dsimp [E]; positivity
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
  induction t generalizing a out with
  | zero => exact TVClose.refl _ (by simp)
  | succ t ih =>
    have hr (r) : TVClose (outerResult K p c w t a out r) (outerResult H p c w t a out r)
        (t * E) := by cases r <;> exact ih _ _
    letI := outerResult_probability K p c he w a out t
    letI := outerResult_probability H p c he w a out t
    have hm (M) : TVClose (outerAfterMass K p c w t a out M)
        (outerAfterMass H p c w t a out M) (E + t * E) := by
      unfold outerAfterMass
      split_ifs
      · exact TVClose.refl _ (by positivity)
      · letI := innerLoop_probability K p c (hadamard a w) a M c.T2 (initialEstimate M a)
        letI := innerLoop_probability H p c (hadamard a w) a M c.T2 (initialEstimate M a)
        exact (innerLoop_tv K H hη hKH p c _ a M c.T2 _).bind (by positivity)
          (measurable_outerResult K p c he w a out t)
          (measurable_outerResult H p c he w a out t) hr
    let f (J : WitnessKernel n) (noise : ℝ) :=
      outerAfterMass J p c w t a out (lowerBiasedMass (mass a) (mass (hadamard a w)) noise c.tau2)
    letI : ∀ z, IsProbabilityMeasure (f K z) := fun z => outerAfterMass_probability K p c he _ _ _ _ _
    letI : ∀ z, IsProbabilityMeasure (f H z) := fun z => outerAfterMass_probability H p c he _ _ _ _ _
    have ht := (TVClose.refl (laplace (1 / c.eps2)) (le_refl (0 : ℝ))).bind
      (f := f K) (g := f H)
      (by positivity : 0 ≤ E + (t : ℝ) * E)
      ((measurable_outerAfterMass K p c he w a out t).comp (show Measurable
        (fun noise : ℝ => lowerBiasedMass (mass a) (mass (hadamard a w)) noise c.tau2) by fun_prop))
      ((measurable_outerAfterMass H p c he w a out t).comp (by fun_prop)) (fun z => hm _)
    rw [outerLoop_succ_raw, outerLoop_succ_raw]
    change TVClose ((laplace (1 / c.eps2)).bind (f K))
      ((laplace (1 / c.eps2)).bind (f H)) ((t + 1 : ℕ) * E)
    rw [show ((t + 1 : ℕ) : ℝ) * E = 0 + (E + t * E) by push_cast; ring]
    exact ht


end DPCut.CappedReplacement
