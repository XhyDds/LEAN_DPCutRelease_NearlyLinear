import DPCut.CappedInnerLoop
import DPCut.InnerLoopPrivacy

/-! Advanced composition for capped updates: the cap and mass are fixed public
transcript values, and projection only changes the public state update. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

def cappedStateUpdate {n : ℕ} (c : RunConfig) (a : Weights n) (H : ℝ)
    (q : InnerState n × Aggregate n) : InnerState n :=
  if q.1.1 then q.1 else
    if q.2.Accepts q.1.2.1 then (true, q.1.2.1, q.2.residual)
      else (false, cappedNext c a H q.1.2.1 q.2, 0)

lemma measurable_cappedStateUpdate {n : ℕ} (c : RunConfig) (a : Weights n) (H : ℝ) :
    Measurable (cappedStateUpdate c a H) := by
  apply Measurable.ite ((measurable_fst.comp measurable_fst) (measurableSet_singleton true)) measurable_fst
  apply Measurable.ite (measurableSet_aggregateAccepts (by fun_prop) measurable_snd)
  · fun_prop
  · exact measurable_const.prodMk
      ((measurable_cappedNext c measurable_const (by fun_prop) measurable_const measurable_snd).prodMk measurable_const)

lemma cappedState_done {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (H : ℝ) (k : ℕ) (h r : Weights n) :
    adaptiveLoop (innerStateKernel hn p c ho w) (cappedStateUpdate c a H) innerStateOutput
      k (true, h, r) = Measure.dirac (some (h, r)) := by
  induction k with
  | zero => simp [adaptiveLoop, innerStateOutput]
  | succ k ih =>
    rw [adaptiveLoop]
    have hm : Measurable (fun b : Aggregate n => adaptiveLoop (innerStateKernel hn p c ho w)
        (cappedStateUpdate c a H) innerStateOutput k (cappedStateUpdate c a H ((true, h, r), b))) :=
      (measurable_adaptiveLoop _ (measurable_cappedStateUpdate c a H) measurable_innerStateOutput k).comp
        ((measurable_cappedStateUpdate c a H).comp measurable_prodMk_left)
    have hk : innerStateKernel hn p c ho w (true, h, r) = Measure.dirac default := by
      simp [innerStateKernel]
    rw [hk, Measure.dirac_bind hm]
    simpa [cappedStateUpdate] using ih

theorem cappedInnerLoop_eq_stateLoop {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (H : ℝ) (k : ℕ) (h : Weights n) :
    cappedInnerLoop p c w a H k h = adaptiveLoop (innerStateKernel hn p c ho w)
      (cappedStateUpdate c a H) innerStateOutput k (false, h, 0) := by
  induction k generalizing h with
  | zero => simp [cappedInnerLoop, adaptiveLoop, innerStateOutput]
  | succ k ih =>
    rw [cappedInnerLoop, adaptiveLoop]
    have hk : innerStateKernel hn p c ho w (false, h, 0) = aggregateLaw c.oracle p.gamma w h := by
      simp [innerStateKernel]
    rw [hk]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro b
    by_cases hb : b.Accepts h
    · simp only [if_pos hb, cappedStateUpdate, Bool.false_eq_true, if_false]
      exact (cappedState_done hn p c ho w a H k h b.residual).symm
    · simp only [if_neg hb, cappedStateUpdate, Bool.false_eq_true, if_false]
      exact ih _

theorem cappedInnerLoop_privacy {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w w' a : Weights n) (H : ℝ) (k : ℕ) (h : Weights n)
    {ε₀ δ₀ δ : ℝ} (hε : 0 < ε₀) (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp : ∀ h, Indistinguishable (aggregateLaw c.oracle p.gamma w h)
      (aggregateLaw c.oracle p.gamma w' h) ε₀ δ₀) :
    Indistinguishable (cappedInnerLoop p c w a H k h) (cappedInnerLoop p c w' a H k h)
      (advancedEpsilon k ε₀ δ) (k * δ₀ + δ) := by
  rw [cappedInnerLoop_eq_stateLoop hn p c ho w, cappedInnerLoop_eq_stateLoop hn p c ho w']
  apply adaptiveLoop_private _ _ (measurable_cappedStateUpdate c a H) measurable_innerStateOutput
    k (false, h, 0) hε hδ₀ hδ₀1 hδ hδ1
  intro s
  dsimp only [innerStateKernel, Kernel.coe_mk]
  split_ifs
  · exact Indistinguishable.of_eq rfl hε.le hδ₀
  · exact hp _

end DPCut
