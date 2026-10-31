import DPCut.OracleReplacementLaw

/-! Uniform errors of witness kernels accumulate along every adaptive branch. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.OracleReplacement
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (K H : WitnessKernel n) [IsMarkovKernel K] [IsMarkovKernel H]
variable {η : ℝ} (hη : 0 ≤ η) (hKH : ∀ q, TVClose (K q) (H q) η)
include hη hKH

omit hη hKH in
lemma bind_option_probability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (Option α)) [IsProbabilityMeasure μ] (P : Measure β) [IsProbabilityMeasure P]
    (f : α → Measure β) (hf : Measurable f) [∀ a, IsProbabilityMeasure (f a)] :
    IsProbabilityMeasure (μ.bind (fun a => a.elim P f)) := by
  letI : ∀ a : Option α, IsProbabilityMeasure (a.elim P f) := fun a => by
    cases a <;> dsimp <;> infer_instance
  exact probability_bind _ _ (measurable_option_elim P hf)

omit hη hKH in
lemma bind_option_tv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ ν : Measure (Option α)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {P Q : Measure β} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {f g : α → Measure β} [∀ a, IsProbabilityMeasure (f a)] [∀ a, IsProbabilityMeasure (g a)]
    {δ ξ : ℝ} (hξ : 0 ≤ ξ) (h : TVClose μ ν δ) (hf : Measurable f) (hg : Measurable g)
    (hPQ : TVClose P Q ξ) (hfg : ∀ a, TVClose (f a) (g a) ξ) :
    TVClose (μ.bind (fun a => a.elim P f)) (ν.bind (fun a => a.elim Q g)) (δ + ξ) := by
  letI : ∀ a : Option α, IsProbabilityMeasure (a.elim P f) := fun a => by
    cases a <;> dsimp <;> infer_instance
  letI : ∀ a : Option α, IsProbabilityMeasure (a.elim Q g) := fun a => by
    cases a <;> dsimp <;> infer_instance
  apply h.bind hξ (measurable_option_elim P hf) (measurable_option_elim Q hg)
  intro a
  cases a
  · exact hPQ
  · exact hfg _

attribute [local instance] aggregateLoop_probability innerLoop_probability

theorem aggregateLoop_tv (γ : ℝ) (w h : Weights n) (t : ℕ) (a : Aggregate n) :
    TVClose (aggregateLoop K γ w h t a) (aggregateLoop H γ w h t a) (t * (2 * η)) := by
  induction t generalizing a with
  | zero => exact TVClose.refl _ (by simp)
  | succ t ih =>
    rw [aggregateLoop, aggregateLoop]
    split_ifs
    · exact TVClose.refl _ (by positivity)
    · have hminus := bind_option_tv (by positivity : 0 ≤ (t : ℝ) * (2 * η))
        (hKH (minusDiscrepancy γ w h a.residual, a.residual))
        (measurable_aggregateLoop K γ t measurable_const measurable_const (measurable_aggregateMinusStep a))
        (measurable_aggregateLoop H γ t measurable_const measurable_const (measurable_aggregateMinusStep a))
        (TVClose.refl (Measure.dirac a) (by positivity)) (fun g => ih (aggregateMinusStep a g))
      letI := bind_option_probability (K (minusDiscrepancy γ w h a.residual, a.residual))
        (Measure.dirac a) (fun g => aggregateLoop K γ w h t (aggregateMinusStep a g))
        (measurable_aggregateLoop K γ t measurable_const measurable_const (measurable_aggregateMinusStep a))
      letI := bind_option_probability (H (minusDiscrepancy γ w h a.residual, a.residual))
        (Measure.dirac a) (fun g => aggregateLoop H γ w h t (aggregateMinusStep a g))
        (measurable_aggregateLoop H γ t measurable_const measurable_const (measurable_aggregateMinusStep a))
      rw [show ((t + 1 : ℕ) : ℝ) * (2 * η) = η + (η + t * (2 * η)) by push_cast; ring]
      exact bind_option_tv (by positivity) (hKH (plusDiscrepancy γ w h a.residual, a.residual))
        (measurable_aggregateLoop K γ t measurable_const measurable_const (measurable_aggregatePlusStep a))
        (measurable_aggregateLoop H γ t measurable_const measurable_const (measurable_aggregatePlusStep a))
        hminus (fun g => (ih (aggregatePlusStep a g)).mono (by linarith))

theorem innerLoop_tv (p : Parameters) (c : RunConfig) (w : Weights n) (M : ℝ)
    (t : ℕ) (h : Weights n) :
    TVClose (innerLoop K p c w M t h) (innerLoop H p c w M t h)
      (t * ((Fintype.card (Edge n) : ℝ) * (2 * η))) := by
  let E : ℝ := Fintype.card (Edge n) * (2 * η)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  induction t generalizing h with
  | zero => exact TVClose.refl _ (by simp)
  | succ t ih =>
    rw [innerLoop, innerLoop]
    let f (J : WitnessKernel n) (a : Aggregate n) :=
      if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop J p c w M t (innerNext c M h a)
    have hi (J : WitnessKernel n) [IsMarkovKernel J] : ∀ a, IsProbabilityMeasure (f J a) := by as_aux_lemma =>
      intro a
      dsimp [f]
      split_ifs
      · infer_instance
      · exact innerLoop_probability J p c w M t _
    letI := hi K
    letI := hi H
    have hf (a) : TVClose (f K a) (f H a) (t * E) := by
      dsimp [f]
      split_ifs
      · exact TVClose.refl _ (by positivity)
      · exact ih _
    letI := aggregateLoop_probability K p.gamma w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩
    letI := aggregateLoop_probability H p.gamma w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩
    have ht := (aggregateLoop_tv K H hη hKH p.gamma w h (Fintype.card (Edge n))
      ⟨0, 0, 1⟩).bind (f := f K) (g := f H) (by positivity : 0 ≤ (t : ℝ) * E)
      (measurable_inner_continuation K p c w h M t)
      (measurable_inner_continuation H p c w h M t) hf
    change TVClose ((aggregateLaw K p.gamma w h).bind (f K))
      ((aggregateLaw H p.gamma w h).bind (f H)) ((t + 1 : ℕ) * E)
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
      · letI := innerLoop_probability K p c (hadamard a w) M c.T2 (initialEstimate M a)
        letI := innerLoop_probability H p c (hadamard a w) M c.T2 (initialEstimate M a)
        exact (innerLoop_tv K H hη hKH p c _ M c.T2 _).bind (by positivity)
          (measurable_outerResult K p c he w a out t)
          (measurable_outerResult H p c he w a out t) hr
    let f (J : WitnessKernel n) (noise : ℝ) :=
      outerAfterMass J p c w t a out (clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2)
    letI : ∀ z, IsProbabilityMeasure (f K z) := fun z => outerAfterMass_probability K p c he _ _ _ _ _
    letI : ∀ z, IsProbabilityMeasure (f H z) := fun z => outerAfterMass_probability H p c he _ _ _ _ _
    have ht := (TVClose.refl (laplace (1 / c.eps2)) (le_refl (0 : ℝ))).bind
      (f := f K) (g := f H)
      (by positivity : 0 ≤ E + (t : ℝ) * E)
      ((measurable_outerAfterMass K p c he w a out t).comp (show Measurable
        (fun noise : ℝ => clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2) by fun_prop))
      ((measurable_outerAfterMass H p c he w a out t).comp (by fun_prop)) (fun z => hm _)
    change TVClose ((laplace (1 / c.eps2)).bind (f K))
      ((laplace (1 / c.eps2)).bind (f H)) ((t + 1 : ℕ) * E)
    rw [show ((t + 1 : ℕ) : ℝ) * E = 0 + (E + t * E) by push_cast; ring]
    exact ht

theorem fullRelease_tv (hn : 2 ≤ n) (p : Parameters) (hp : p.Valid) (w : Weights n) :
    let c := runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants
    TVClose (fullRelease K p w) (fullRelease H p w)
      (c.T1 * (c.T2 * ((Fintype.card (Edge n) : ℝ) * (2 * η)))) := by
  let c := runConfig n (preprocessingThreshold n p) (boundedParameters p) outerUtilityConstants
  have he := config_eps2_pos hn (preprocessingThreshold_one_le hn hp) (boundedParameters_valid hp)
  letI := preprocessLaw_probability (show 0 < p.epsilon / 2 by linarith [hp.2.2.1])
    (p.beta / 2) p.gamma w
  letI := continuation_probability K hn hp w
  letI := continuation_probability H hn hp w
  have ht := (TVClose.refl (preprocessLaw (p.epsilon / 2) (p.beta / 2) p.gamma w)
    (le_refl (0 : ℝ))).bind (f := continuation K p w) (g := continuation H p w)
    (by positivity : 0 ≤ (c.T1 : ℝ) * (c.T2 *
      ((Fintype.card (Edge n) : ℝ) * (2 * η))))
    ((measurable_continuation K hn hp).comp measurable_prodMk_left)
    ((measurable_continuation H hn hp).comp measurable_prodMk_left)
    (fun y => (outerLoop_tv K H hη hKH (boundedParameters p) c he
      (clipWeights (preprocessingThreshold n p) w) c.T1 1 0).map
        (show Measurable (fun h : Weights n => h + y) by fun_prop))
  simpa only [zero_add] using ht

end DPCut.OracleReplacement
