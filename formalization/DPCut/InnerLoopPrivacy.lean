import DPCut.InnerLoopMeasurable
import DPCut.AdaptiveLoop

/-! Advanced composition for the actual early-stopping inner loop. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut
attribute [local instance] Classical.propDecidable

abbrev InnerState (n : ℕ) := Bool × Weights n × Weights n

def innerStateKernel {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) : Kernel (InnerState n) (Aggregate n) where
  toFun s := if s.1 then Measure.dirac default else aggregateLaw c.oracle p.gamma w s.2.1
  measurable' := by
    apply Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
    change Measurable ((fun q : Weights n × Weights n => aggregateLaw c.oracle p.gamma q.1 q.2) ∘
      (fun s : InnerState n => (w, s.2.1)))
    exact (measurable_aggregateLaw hn c.oracle (by linarith [ho.lam_lower]) ho.eps_pos p.gamma).comp
      (measurable_const.prodMk (measurable_fst.comp measurable_snd))

instance innerStateKernel_markov {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) : IsMarkovKernel (innerStateKernel hn p c ho w) := by
  constructor
  intro s
  change IsProbabilityMeasure (if s.1 then Measure.dirac default else aggregateLaw c.oracle p.gamma w s.2.1)
  split_ifs
  · infer_instance
  · exact aggregateLaw_probability hn c.oracle ho p.gamma w s.2.1

def innerStateUpdate {n : ℕ} (c : RunConfig) (M : ℝ) (q : InnerState n × Aggregate n) : InnerState n :=
  if q.1.1 then q.1 else
    if q.2.Accepts q.1.2.1 then (true, q.1.2.1, q.2.residual)
      else (false, innerNext c M q.1.2.1 q.2, 0)

lemma measurable_innerStateUpdate {n : ℕ} (c : RunConfig) (M : ℝ) :
    Measurable (innerStateUpdate (n := n) c M) := by
  apply Measurable.ite ((measurable_fst.comp measurable_fst) (measurableSet_singleton true)) measurable_fst
  apply Measurable.ite (measurableSet_aggregateAccepts (by fun_prop) measurable_snd)
  · fun_prop
  · exact measurable_const.prodMk
      ((measurable_innerNext c measurable_const (by fun_prop) measurable_snd).prodMk measurable_const)

def innerStateOutput {n : ℕ} (s : InnerState n) : Option (Weights n × Weights n) :=
  if s.1 then some s.2 else none

lemma measurable_innerStateOutput {n : ℕ} : Measurable (innerStateOutput (n := n)) :=
  Measurable.ite (measurable_fst (measurableSet_singleton true))
    (measurable_some.comp measurable_snd) measurable_const

lemma innerState_done {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) (M : ℝ) (k : ℕ) (h r : Weights n) :
    adaptiveLoop (innerStateKernel hn p c ho w) (innerStateUpdate c M) innerStateOutput
      k (true, h, r) = Measure.dirac (some (h, r)) := by
  induction k with
  | zero => simp [adaptiveLoop, innerStateOutput]
  | succ k ih =>
    rw [adaptiveLoop]
    have hm : Measurable (fun a : Aggregate n => adaptiveLoop (innerStateKernel hn p c ho w)
        (innerStateUpdate c M) innerStateOutput k (innerStateUpdate c M ((true, h, r), a))) :=
      (measurable_adaptiveLoop _ (measurable_innerStateUpdate c M) measurable_innerStateOutput k).comp
        ((measurable_innerStateUpdate c M).comp measurable_prodMk_left)
    have hk : innerStateKernel hn p c ho w (true, h, r) = Measure.dirac default := by
      simp [innerStateKernel]
    rw [hk, Measure.dirac_bind hm]
    simpa [innerStateUpdate] using ih

theorem innerLoop_eq_stateLoop {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) (M : ℝ) (k : ℕ) (h : Weights n) :
    innerLoop p c w M k h = adaptiveLoop (innerStateKernel hn p c ho w)
      (innerStateUpdate c M) innerStateOutput k (false, h, 0) := by
  induction k generalizing h with
  | zero => simp [innerLoop, adaptiveLoop, innerStateOutput]
  | succ k ih =>
    rw [innerLoop_succ_eq, adaptiveLoop]
    have hk : innerStateKernel hn p c ho w (false, h, 0) = aggregateLaw c.oracle p.gamma w h := by
      simp [innerStateKernel]
    rw [hk]
    apply Measure.bind_congr_right
    apply Filter.Eventually.of_forall
    intro a
    by_cases ha : a.Accepts h
    · simp only [if_pos ha, innerStateUpdate, Bool.false_eq_true, if_false]
      exact (innerState_done hn p c ho w M k h a.residual).symm
    · simp only [if_neg ha, innerStateUpdate, Bool.false_eq_true, if_false]
      exact ih _

theorem innerLoop_privacy {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w w' : Weights n) (M : ℝ) (k : ℕ) (h : Weights n)
    {ε₀ δ₀ δ : ℝ} (hε : 0 < ε₀) (hδ₀ : 0 ≤ δ₀) (hδ₀1 : δ₀ < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hp : ∀ h, Indistinguishable (aggregateLaw c.oracle p.gamma w h)
      (aggregateLaw c.oracle p.gamma w' h) ε₀ δ₀) :
    Indistinguishable (innerLoop p c w M k h) (innerLoop p c w' M k h)
      (advancedEpsilon k ε₀ δ) (k * δ₀ + δ) := by
  rw [innerLoop_eq_stateLoop hn p c ho w, innerLoop_eq_stateLoop hn p c ho w']
  apply adaptiveLoop_private _ _ (measurable_innerStateUpdate c M) measurable_innerStateOutput
    k (false, h, 0) hε hδ₀ hδ₀1 hδ hδ1
  intro s
  dsimp only [innerStateKernel, Kernel.coe_mk]
  split_ifs
  · exact Indistinguishable.of_eq rfl hε.le hδ₀
  · exact hp _

end DPCut
