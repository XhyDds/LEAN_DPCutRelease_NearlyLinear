import DPCut.InnerProgress

/-! Adaptive failure accounting for the concrete inner multiplicative-weights loop. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma HighProbability.failure_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {β : ℝ} {P : α → Prop} (h : HighProbability μ β P)
    (hβ : 0 ≤ β) : μ {x | ¬P x} ≤ ENNReal.ofReal β := by
  apply (prob_le_iff_measure_le hβ).mp
  have hc := measureReal_add_measureReal_compl (μ := μ) h.1
  rw [measureReal_univ_eq_one] at hc
  change prob μ {x | P x} + prob μ {x | ¬P x} = 1 at hc
  linarith [h.2]

/-- With less potential than `t` decrements, exhaustion requires a bad oracle call. -/
theorem innerLoop_failure_of_potential {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) {w : Weights n} {M H β : ℝ}
    (hw : Nonnegative w) (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M)
    (hMH : M ≤ H) (hHH : H ≤ (1 + p.gamma / 4) * M)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma) (hβ : 0 ≤ β)
    (horacle : ∀ h : Weights n, Nonnegative h → HighProbability (aggregateLaw c.oracle p.gamma w h) β
      (fun a => a.Partition ∧ a.Accurate w h p.gamma c.B))
    (t : ℕ) (h : Weights n) (hh : EstimateValid w H h)
    (hpot : potential w h M H < t * (p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2))) :
    innerLoop p c w H t h {none} ≤ ENNReal.ofReal (t * β) := by
  induction t generalizing h with
  | zero =>
    have hp := potential_nonneg w h (H := H) hM.le
    simp only [Nat.cast_zero, zero_mul] at hpot
    linarith
  | succ t ih =>
    rw [innerLoop_succ_eq]
    letI := aggregateLaw_probability hn c.oracle ho p.gamma w h
    let f := fun a : Aggregate n => if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop p c w H t (innerNext c H h a)
    have hf : Measurable f := measurable_inner_continuation hn p c ho w h H t
    letI (a : Aggregate n) : IsProbabilityMeasure (f a) := by
      dsimp [f]
      split_ifs
      · infer_instance
      · exact innerLoop_probability hn p c ho w H t _
    have hb := (horacle h hh.1).failure_bound hβ
    have he : (aggregateLaw c.oracle p.gamma w h).bind f {none} ≤ ENNReal.ofReal (β + t * β) := by
      apply measure_bind_le_of_good hf (measurableSet_aggregate_accurate w h p.gamma c.B)
        measurableSet_option_none hβ (by positivity) hb
      intro a ha
      dsimp [f]
      split_ifs with hacc
      · simp [Measure.dirac_apply' _ measurableSet_option_none]
      · obtain ⟨hv, hdec⟩ := innerNext_progress p c hw hM hH hmw hh hMH hHH hγ hγ1 hη
          ha.1 ha.2 hacc
        apply ih _ hv
        push_cast at hpot
        nlinarith only [hdec, hpot]
    convert he using 1
    push_cast
    congr 1
    ring

theorem innerLoop_initial_failure {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) {U H : ℝ} {w a : Weights n}
    (hU : 0 ≤ U) (hw : Bounded U w) (ha : IsMask a) (hM : 0 < mass (hadamard a w))
    (hH : 0 < H) (hMH : mass (hadamard a w) ≤ H)
    (hHH : H ≤ (1 + p.gamma / 4) * mass (hadamard a w))
    (hlarge : n * U ≤ mass (hadamard a w))
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma)
    (hT : c.T2 = innerHorizon n p.gamma) (hβ : 0 ≤ c.betaGE)
    (horacle : ∀ h : Weights n, Nonnegative h → HighProbability
      (aggregateLaw c.oracle p.gamma (hadamard a w) h) c.betaGE
      (fun b => b.Partition ∧ b.Accurate (hadamard a w) h p.gamma c.B)) :
    innerLoop p c (hadamard a w) H c.T2 (initialEstimate H a) {none} ≤
      ENNReal.ofReal (c.T2 * c.betaGE) := by
  have hw0 : Nonnegative w := fun e => (hw e).1
  have hwA : Nonnegative (hadamard a w) := fun e => mul_nonneg (ha e).1 (hw e).1
  apply innerLoop_failure_of_potential hn p c ho hwA hM hH rfl hMH hHH hγ hγ1 hη hβ horacle
    c.T2 _ (initialEstimate_valid hw0 ha hM hH)
  have hp := initialEstimate_potential_le hn hU hw ha hH hM hlarge
  have ht := innerHorizon_progress_budget (n := n) hγ hM
  rw [hT]
  exact hp.trans_lt ht

end DPCut
