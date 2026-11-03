import DPCut.CappedInnerLoop
import DPCut.InnerLoopUtility
import DPCut.InnerReleaseUtility

/-! Joint success, contraction and all-cut accuracy of the capped inner loop. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

theorem cappedInnerLoop_release_of_potential {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) {w a : Weights n} {M H β : ℝ}
    (hw : Nonnegative w) (ha : Nonnegative a) (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M)
    (hcap : H ≤ mass a) (hHM : H ≤ M) (hMH : (1 - p.gamma / 50) * M ≤ H)
    (htarget : ∀ e, w e / M ≤ a e / H)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma)
    (hB : 0 ≤ c.B) (hlarge : 100 * c.B ≤ M) (hβ : 0 ≤ β)
    (horacle : ∀ h : Weights n, Nonnegative h → HighProbability (aggregateLaw c.oracle p.gamma w h) β
      (fun a => a.Partition ∧ a.Accurate w h p.gamma c.B))
    (t : ℕ) (h : Weights n) (hh : CappedEstimateValid a H h)
    (hpot : potential w h M H < t * (p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2))) :
    cappedInnerLoop p c w a H t h {r | ¬InnerReleaseGood w p.gamma c.B r} ≤ ENNReal.ofReal (t * β) := by
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
    have hb := (horacle h hh.1).failure_bound hβ
    have he : (aggregateLaw c.oracle p.gamma w h).bind f {r | ¬InnerReleaseGood w p.gamma c.B r} ≤
        ENNReal.ofReal (β + t * β) := by
      apply measure_bind_le_of_good hf (measurableSet_aggregate_accurate w h p.gamma c.B)
        (measurableSet_innerReleaseGood w p.gamma c.B).compl hβ (by positivity) hb
      intro b hb
      dsimp [f]
      split_ifs with hacc
      · have hg : InnerReleaseGood w p.gamma c.B (some (h, b.residual)) :=
          ⟨hh.1, hb.1.2.2.1, capped_residual_contraction hw hh.1 hb.1 hb.2 hacc
            hγ hγ1 hB (by simpa [hmw] using hlarge) (by simpa [hmw, hh.2.1] using hMH), hb.2.2.2⟩
        simp [Measure.dirac_apply' _ (measurableSet_innerReleaseGood w p.gamma c.B).compl, hg]
      · obtain ⟨hv, hdec⟩ := cappedNext_progress p c hw ha hM hH hmw hcap hh hHM hMH htarget hγ hγ1 hη
          hb.1 hb.2 hacc
        apply ih _ hv
        push_cast at hpot
        nlinarith only [hdec, hpot]
    convert he using 1
    push_cast
    congr 1
    ring


lemma capped_target_feasible {n : ℕ} {w a : Weights n} {H : ℝ}
    (hw : Bounded 1 w) (ha : IsMask a) (hH : 0 < H) (hHM : H ≤ mass (hadamard a w)) :
    H ≤ mass a ∧ ∀ e, (hadamard a w) e / mass (hadamard a w) ≤ a e / H := by
  have hm : 0 < mass (hadamard a w) := hH.trans_le hHM
  have hle (e : Edge n) : (hadamard a w) e ≤ a e := by
    exact mul_le_of_le_one_right (ha e).1 (hw e).2
  refine ⟨hHM.trans (Finset.sum_le_sum fun e _ => hle e), fun e => ?_⟩
  exact (div_le_div_of_nonneg_right (hle e) hm.le).trans
    (div_le_div_of_nonneg_left (ha e).1 hH hHM)

theorem cappedInnerLoop_initial_release {n : ℕ} (hn : 2 ≤ n)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n 1 p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) {w a : Weights n} {H : ℝ}
    (hw : Bounded 1 w) (ha : IsMask a) (hM : 0 < mass (hadamard a w))
    (hH : 0 < H) (hHM : H ≤ mass (hadamard a w))
    (hMH : (1 - p.gamma / 50) * mass (hadamard a w) ≤ H)
    (hlarge : 100 * c.B ≤ mass (hadamard a w)) :
    cappedInnerLoop p c (hadamard a w) a H c.T2 (initialEstimate H a)
      {r | ¬InnerReleaseGood (hadamard a w) p.gamma c.B r} ≤ ENNReal.ofReal (c.T2 * c.betaGE) := by
  have hB : 0 ≤ c.B := (by positivity : 0 ≤ (n : ℝ) * 1).trans hc.certificate_lower
  have hwA : Bounded 1 (hadamard a w) := fun e =>
    ⟨mul_nonneg (ha e).1 (hw e).1, ((mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2)⟩
  obtain ⟨hcap, htarget⟩ := capped_target_feasible hw ha hH hHM
  apply cappedInnerLoop_release_of_potential hn p c hc.oracle_privacy (fun e => (hwA e).1)
    (fun e => (ha e).1) hM hH rfl hcap hHM hMH htarget hγ hγ1 hc.eta_eq hB hlarge hc.betaGE_nonneg
    (fun h hh => hc.aggregate_utility _ h hwA hh) _ _
    (initialEstimate_capped_valid (fun e => (ha e).1) hH hcap)
  have hp := initialEstimate_potential_le hn (by norm_num : (0 : ℝ) ≤ 1) hw ha hH hM
    (hc.certificate_lower.trans (by linarith))
  rw [hc.horizon_eq]
  exact hp.trans_lt (innerHorizon_progress_budget hγ hM)

end DPCut
