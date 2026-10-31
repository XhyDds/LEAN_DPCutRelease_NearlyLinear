import DPCut.AggregateMeasurable

/-! Sampling, measurability, and residual support for the actual inner loop. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {A : Type*} [MeasurableSpace A] {n : ℕ}

@[fun_prop] lemma measurable_pairing {w h : A → Weights n} (hw : Measurable w) (hh : Measurable h) :
    Measurable (fun x => pairing (w x) (h x)) :=
  Finset.measurable_sum _ fun e _ => ((measurable_pi_apply e).comp hw).mul
    ((measurable_pi_apply e).comp hh)

@[fun_prop] lemma measurable_mwUpdate {M θ η : A → ℝ} {h g : A → Weights n}
    (hM : Measurable M) (hθ : Measurable θ) (hη : Measurable η)
    (hh : Measurable h) (hg : Measurable g) :
    Measurable (fun x => mwUpdate (M x) (θ x) (η x) (h x) (g x)) := by
  unfold mwUpdate
  fun_prop

lemma measurableSet_aggregateAccepts {h : A → Weights n} {a : A → Aggregate n}
    (hh : Measurable h) (ha : Measurable a) : MeasurableSet {x | (a x).Accepts (h x)} := by
  unfold Aggregate.Accepts
  apply measurableSet_le <;> fun_prop

def innerNext {n : ℕ} (c : RunConfig) (M : ℝ) (h : Weights n) (a : Aggregate n) : Weights n :=
  if pairing h a.minus ≤ pairing h a.plus then mwUpdate M 1 c.eta h a.plus
    else mwUpdate M (-1) c.eta h a.minus

@[fun_prop] lemma measurable_innerNext (c : RunConfig) {M : A → ℝ}
    {h : A → Weights n} {a : A → Aggregate n}
    (hM : Measurable M) (hh : Measurable h) (ha : Measurable a) :
    Measurable (fun x => innerNext c (M x) (h x) (a x)) := by
  unfold innerNext
  apply Measurable.ite
  · apply measurableSet_le <;> fun_prop
  · fun_prop
  · fun_prop

lemma innerLoop_succ_eq (p : Parameters) (c : RunConfig) (w : Weights n) (M : ℝ)
    (t : ℕ) (h : Weights n) :
    innerLoop p c w M (t + 1) h = (aggregateLaw c.oracle p.gamma w h).bind fun a =>
      if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop p c w M t (innerNext c M h a) := by
  rw [innerLoop]
  congr 1
  funext a
  dsimp only [innerNext]
  split_ifs <;> rfl

theorem measurable_innerLoop (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w h : A → Weights n} {M : A → ℝ},
      Measurable w → Measurable h → Measurable M →
      Measurable (fun x => innerLoop p c (w x) (M x) t (h x)) := by
  induction t with
  | zero => intro A _ w h M hw hh hM; exact measurable_const
  | succ t ih =>
    intro A _ w h M hw hh hM
    have hl : 0 < c.oracle.lam := by linarith [ho.lam_lower]
    have hm : Measurable (fun x => aggregateLaw c.oracle p.gamma (w x) (h x)) := by
      change Measurable ((fun q : Weights n × Weights n => aggregateLaw c.oracle p.gamma q.1 q.2) ∘
        (fun x => (w x, h x)))
      exact (measurable_aggregateLaw hn c.oracle hl ho.eps_pos p.gamma).comp (hw.prodMk hh)
    letI : ∀ x, IsProbabilityMeasure (aggregateLaw c.oracle p.gamma (w x) (h x)) :=
      fun x => aggregateLaw_probability hn c.oracle ho p.gamma _ _
    have hc : Measurable (fun q : A × Aggregate n => if q.2.Accepts (h q.1)
        then Measure.dirac (some (h q.1, q.2.residual))
        else innerLoop p c (w q.1) (M q.1) t (innerNext c (M q.1) (h q.1) q.2)) := by
      apply Measurable.ite (measurableSet_aggregateAccepts (hh.comp measurable_fst) measurable_snd)
      · apply Measure.measurable_dirac.comp
        apply measurable_some.comp
        exact (hh.comp measurable_fst).prodMk (measurable_aggregate_residual.comp measurable_snd)
      · exact ih (hw.comp measurable_fst)
          (measurable_innerNext c (hM.comp measurable_fst) (hh.comp measurable_fst) measurable_snd)
          (hM.comp measurable_fst)
    simp_rw [innerLoop_succ_eq]
    exact measurable_bind_kernel hm (show Measurable (Function.uncurry _) from hc)

lemma measurable_inner_continuation (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w h : Weights n) (M : ℝ) (t : ℕ) :
    Measurable (fun a : Aggregate n => if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop p c w M t (innerNext c M h a)) := by
  apply Measurable.ite (measurableSet_aggregateAccepts measurable_const measurable_id)
  · exact Measure.measurable_dirac.comp (measurable_some.comp
      (measurable_const.prodMk measurable_aggregate_residual))
  · exact measurable_innerLoop hn p c ho t measurable_const
      (measurable_innerNext c measurable_const measurable_const measurable_id) measurable_const

theorem innerLoop_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    IsProbabilityMeasure (innerLoop p c w M t h) := by
  induction t generalizing h with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | succ t ih =>
    rw [innerLoop_succ_eq]
    letI := aggregateLaw_probability hn c.oracle ho p.gamma w h
    letI : ∀ a : Aggregate n, IsProbabilityMeasure
        (if a.Accepts h then Measure.dirac (some (h, a.residual))
          else innerLoop p c w M t (innerNext c M h a)) := fun a => by
      split_ifs
      · infer_instance
      · exact ih _
    exact probability_bind _ _ (measurable_inner_continuation hn p c ho w h M t)

def InnerSupported {n : ℕ} (r : Option (Weights n × Weights n)) : Prop :=
  r.elim True (fun hr => IsMask hr.2)

lemma measurableSet_innerSupported {n : ℕ} : MeasurableSet {r : Option (Weights n × Weights n) |
    InnerSupported r} := measurableSet_option_elim (measurableSet_isMask measurable_snd)

theorem innerLoop_supported (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    ∀ᵐ r ∂innerLoop p c w M t h, InnerSupported r := by
  induction t generalizing h with
  | zero => exact (ae_dirac_iff measurableSet_innerSupported).mpr trivial
  | succ t ih =>
    rw [innerLoop_succ_eq]
    apply ae_bind_of_ae_ae (measurable_inner_continuation hn p c ho w h M t) measurableSet_innerSupported
    filter_upwards [aggregateLaw_residual_mask hn c.oracle (by linarith [ho.lam_lower])
      ho.eps_pos p.gamma w h] with a ha
    split_ifs
    · exact (ae_dirac_iff measurableSet_innerSupported).mpr ha
    · exact ih _

end DPCut
