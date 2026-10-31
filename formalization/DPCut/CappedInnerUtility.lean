import DPCut.CappedInnerLoop
import DPCut.InnerLoopUtility

/-! Potential-based failure bound for the actual capped inner loop. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

theorem cappedInnerLoop_failure {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) {w a : Weights n} {M H β : ℝ}
    (hw : Nonnegative w) (ha : Nonnegative a) (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M)
    (hcap : H ≤ mass a) (hHM : H ≤ M) (hMH : (1 - p.gamma / 50) * M ≤ H)
    (htarget : ∀ e, w e / M ≤ a e / H)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma) (hβ : 0 ≤ β)
    (horacle : ∀ h : Weights n, Nonnegative h → HighProbability (aggregateLaw c.oracle p.gamma w h) β
      (fun b => b.Partition ∧ b.Accurate w h p.gamma c.B))
    (t : ℕ) (h : Weights n) (hh : CappedEstimateValid a H h)
    (hpot : potential w h M H < t * (p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2))) :
    cappedInnerLoop p c w a H t h {none} ≤ ENNReal.ofReal (t * β) := by
  induction t generalizing h with
  | zero =>
    have hp := potential_nonneg w h (H := H) hM.le
    simp only [Nat.cast_zero, zero_mul] at hpot
    linarith
  | succ t ih =>
    rw [cappedInnerLoop]
    letI := aggregateLaw_probability hn c.oracle ho p.gamma w h
    let f := fun b : Aggregate n => if b.Accepts h then Measure.dirac (some (h, b.residual))
      else cappedInnerLoop p c w a H t (cappedNext c a H h b)
    have hf : Measurable f := measurable_cappedInner_continuation hn p c ho w a h H t
    letI (b : Aggregate n) : IsProbabilityMeasure (f b) := by
      dsimp [f]
      split_ifs
      · infer_instance
      · exact cappedInnerLoop_probability hn p c ho w a H t _
    have he : (aggregateLaw c.oracle p.gamma w h).bind f {none} ≤ ENNReal.ofReal (β + t * β) := by
      apply measure_bind_le_of_good hf (measurableSet_aggregate_accurate w h p.gamma c.B)
        measurableSet_option_none hβ (by positivity) ((horacle h hh.1).failure_bound hβ)
      intro b hb
      dsimp [f]
      split_ifs with hacc
      · simp [Measure.dirac_apply' _ measurableSet_option_none]
      · obtain ⟨hv, hdec⟩ := cappedNext_progress p c hw ha hM hH hmw hcap hh hHM hMH htarget
          hγ hγ1 hη hb.1 hb.2 hacc
        apply ih _ hv
        push_cast at hpot
        nlinarith only [hdec, hpot]
    convert he using 1
    push_cast
    congr 1
    ring

end DPCut
