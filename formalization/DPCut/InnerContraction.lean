import DPCut.OuterProgress
import DPCut.Lemma21
import DPCut.OuterLoopMeasurable

/-! Inner success and residual contraction on the same oracle good event. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def InnerContracts {n : ℕ} (w : Weights n) (result : Option (Weights n × Weights n)) : Prop :=
  result.elim False (fun hr => IsMask hr.2 ∧
    mass (residualUpdate w hr.2) ≤ (19 / 20 : ℝ) * mass w)

lemma measurableSet_innerContracts {n : ℕ} (w : Weights n) :
    MeasurableSet {r | InnerContracts w r} := by
  have h : MeasurableSet {hr : Weights n × Weights n | IsMask hr.2 ∧
      mass (residualUpdate w hr.2) ≤ (19 / 20 : ℝ) * mass w} :=
    (measurableSet_isMask measurable_snd).inter (measurableSet_le (show Measurable (fun hr : Weights n × Weights n => mass (residualUpdate w hr.2)) by fun_prop) measurable_const)
  convert (measurableSet_option_elim h.compl).compl using 1
  ext r
  cases r <;> simp [InnerContracts]

theorem innerLoop_contracts_of_potential {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) {w : Weights n} {M H β : ℝ}
    (hw : Nonnegative w) (hM : 0 < M) (hH : 0 < H) (hmw : mass w = M)
    (hMH : M ≤ H) (hHH : H ≤ (1 + p.gamma / 4) * M)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) (hη : c.eta = stepSize p.gamma)
    (hB : 0 ≤ c.B) (hlarge : 10 * c.B ≤ M) (hβ : 0 ≤ β)
    (horacle : ∀ h : Weights n, Nonnegative h → HighProbability (aggregateLaw c.oracle p.gamma w h) β
      (fun a => a.Partition ∧ a.Accurate w h p.gamma c.B))
    (t : ℕ) (h : Weights n) (hh : EstimateValid w H h)
    (hpot : potential w h M H < t * (p.gamma ^ 2 * M / (64 * (1 + p.gamma) ^ 2))) :
    innerLoop p c w H t h {r | ¬InnerContracts w r} ≤ ENNReal.ofReal (t * β) := by
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
    have he : (aggregateLaw c.oracle p.gamma w h).bind f {r | ¬InnerContracts w r} ≤
        ENNReal.ofReal (β + t * β) := by
      apply measure_bind_le_of_good hf (measurableSet_aggregate_accurate w h p.gamma c.B)
        (measurableSet_innerContracts w).compl hβ (by positivity) hb
      intro a ha
      dsimp [f]
      split_ifs with hacc
      · have hg : InnerContracts w (some (h, a.residual)) :=
          ⟨ha.1.2.2.1, residual_contraction n w h a p.gamma c.B hw hh.1 ha.1 ha.2 hacc
            hγ hγ1 hB (by simpa [hmw] using hlarge) (by simpa [hmw, hh.2.1] using hMH)⟩
        simp [Measure.dirac_apply' _ (measurableSet_innerContracts w).compl, hg]
      · obtain ⟨hv, hdec⟩ := innerNext_progress p c hw hM hH hmw hh hMH hHH hγ hγ1 hη
          ha.1 ha.2 hacc
        apply ih _ hv
        push_cast at hpot
        nlinarith only [hdec, hpot]
    convert he using 1
    push_cast
    congr 1
    ring

theorem innerLoop_initial_contracts {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 0 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4) {w a : Weights n} {H : ℝ}
    (hw : Bounded U w) (ha : IsMask a) (hM : 0 < mass (hadamard a w))
    (hH : 0 < H) (hMH : mass (hadamard a w) ≤ H)
    (hHH : H ≤ (1 + p.gamma / 4) * mass (hadamard a w))
    (hlarge : 10 * c.B ≤ mass (hadamard a w)) :
    innerLoop p c (hadamard a w) H c.T2 (initialEstimate H a)
      {r | ¬InnerContracts (hadamard a w) r} ≤ ENNReal.ofReal (c.T2 * c.betaGE) := by
  have hB : 0 ≤ c.B := (mul_nonneg (Nat.cast_nonneg n) hU).trans hc.certificate_lower
  have hwA : Bounded U (hadamard a w) := fun e =>
    ⟨mul_nonneg (ha e).1 (hw e).1, ((mul_le_of_le_one_left (hw e).1 (ha e).2).trans (hw e).2)⟩
  apply innerLoop_contracts_of_potential hn p c hc.oracle_privacy (fun e => (hwA e).1)
    hM hH rfl hMH hHH hγ hγ1 hc.eta_eq hB hlarge hc.betaGE_nonneg
    (fun h hh => hc.aggregate_utility _ h hwA hh) _ _
    (initialEstimate_valid (fun e => (hw e).1) ha hM hH)
  have hp := initialEstimate_potential_le hn hU hw ha hH hM
    (hc.certificate_lower.trans (by linarith))
  rw [hc.horizon_eq]
  exact hp.trans_lt (innerHorizon_progress_budget hγ hM)

end DPCut
