import DPCut.CappedInnerProgress
import DPCut.CutBasics
import DPCut.InnerLoopMeasurable

/-! The actual capped inner sampling loop, its measurable probability law,
and its almost-sure output invariants. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

def cappedInnerLoop {n : ℕ} (p : Parameters) (c : RunConfig) (w a : Weights n) (H : ℝ) :
    ℕ → Weights n → Measure (Option (Weights n × Weights n))
  | 0, _ => Measure.dirac none
  | t + 1, h => (aggregateLaw c.oracle p.gamma w h).bind fun b =>
      if b.Accepts h then Measure.dirac (some (h, b.residual))
      else cappedInnerLoop p c w a H t (cappedNext c a H h b)

theorem measurable_cappedInnerLoop {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (t : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] {w a h : X → Weights n} {H : X → ℝ},
      Measurable w → Measurable a → Measurable h → Measurable H →
      Measurable (fun x => cappedInnerLoop p c (w x) (a x) (H x) t (h x)) := by
  induction t with
  | zero => intro X _ w a h H hw ha hh hH; exact measurable_const
  | succ t ih =>
    intro X _ w a h H hw ha hh hH
    have hm : Measurable (fun x => aggregateLaw c.oracle p.gamma (w x) (h x)) :=
      (measurable_aggregateLaw hn c.oracle (by linarith [ho.lam_lower]) ho.eps_pos p.gamma).comp
        (hw.prodMk hh)
    letI : ∀ x, IsProbabilityMeasure (aggregateLaw c.oracle p.gamma (w x) (h x)) :=
      fun _ => aggregateLaw_probability hn c.oracle ho p.gamma _ _
    change Measurable (fun x => (aggregateLaw c.oracle p.gamma (w x) (h x)).bind _)
    apply measurable_bind_kernel hm
    apply Measurable.ite (measurableSet_aggregateAccepts (hh.comp measurable_fst) measurable_snd)
    · exact Measure.measurable_dirac.comp (measurable_some.comp
        ((hh.comp measurable_fst).prodMk (measurable_aggregate_residual.comp measurable_snd)))
    · exact ih (hw.comp measurable_fst) (ha.comp measurable_fst)
        (measurable_cappedNext c (ha.comp measurable_fst) (hh.comp measurable_fst)
          (hH.comp measurable_fst) measurable_snd) (hH.comp measurable_fst)

lemma measurable_cappedInner_continuation {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a h : Weights n) (H : ℝ) (t : ℕ) :
    Measurable (fun b : Aggregate n => if b.Accepts h then Measure.dirac (some (h, b.residual))
      else cappedInnerLoop p c w a H t (cappedNext c a H h b)) := by
  apply Measurable.ite (measurableSet_aggregateAccepts measurable_const measurable_id)
  · exact Measure.measurable_dirac.comp (measurable_some.comp
      (measurable_const.prodMk measurable_aggregate_residual))
  · exact measurable_cappedInnerLoop hn p c ho t measurable_const measurable_const
      (measurable_cappedNext c measurable_const measurable_const measurable_const measurable_id) measurable_const

theorem cappedInnerLoop_probability {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    IsProbabilityMeasure (cappedInnerLoop p c w a H t h) := by
  induction t generalizing h with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | succ t ih =>
    letI := aggregateLaw_probability hn c.oracle ho p.gamma w h
    letI : ∀ b : Aggregate n, IsProbabilityMeasure
        (if b.Accepts h then Measure.dirac (some (h, b.residual))
          else cappedInnerLoop p c w a H t (cappedNext c a H h b)) := fun b => by
      split_ifs
      · infer_instance
      · exact ih _
    exact probability_bind _ _ (measurable_cappedInner_continuation hn p c ho w a h H t)

lemma measurableSet_cappedEstimateValid {n : ℕ} (a : Weights n) (H : ℝ) :
    MeasurableSet {h | CappedEstimateValid a H h} := by
  have h₁ : MeasurableSet {h : Weights n | mass h = H} :=
    measurableSet_eq_fun (by unfold mass; fun_prop) measurable_const
  have h₂ : MeasurableSet {h : Weights n | ∀ e, h e ≤ a e} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun e => measurableSet_le (measurable_pi_apply e) measurable_const
  have h₃ : MeasurableSet {h : Weights n | ∀ e, 0 < a e → 0 < h e} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_pi_apply e)
  exact (measurableSet_nonnegative measurable_id).inter (h₁.inter (h₂.inter h₃))

def CappedInnerOutputValid {n : ℕ} (a : Weights n) (H : ℝ) (r : Option (Weights n × Weights n)) : Prop :=
  r.elim True (fun hr => CappedEstimateValid a H hr.1 ∧ IsMask hr.2)

lemma measurableSet_cappedInnerOutputValid {n : ℕ} (a : Weights n) (H : ℝ) :
    MeasurableSet {r | CappedInnerOutputValid a H r} :=
  measurableSet_option_elim ((measurable_fst (measurableSet_cappedEstimateValid a H)).inter
    (measurableSet_isMask measurable_snd))

theorem cappedInnerLoop_valid {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (H : ℝ)
    (ha : Nonnegative a) (hH : 0 < H) (hcap : H ≤ mass a) (t : ℕ) (h : Weights n)
    (hh : CappedEstimateValid a H h) :
    ∀ᵐ r ∂cappedInnerLoop p c w a H t h, CappedInnerOutputValid a H r := by
  induction t generalizing h with
  | zero => exact (ae_dirac_iff (measurableSet_cappedInnerOutputValid a H)).mpr trivial
  | succ t ih =>
    apply ae_bind_of_ae_ae (measurable_cappedInner_continuation hn p c ho w a h H t)
      (measurableSet_cappedInnerOutputValid a H)
    filter_upwards [aggregateLaw_residual_mask hn c.oracle (by linarith [ho.lam_lower])
      ho.eps_pos p.gamma w h] with b hb
    split_ifs
    · exact (ae_dirac_iff (measurableSet_cappedInnerOutputValid a H)).mpr ⟨hh, hb⟩
    · exact ih _ (cappedNext_valid c ha hH hcap hh b)

theorem cappedInnerLoop_supported {n : ℕ} (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (w a : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    ∀ᵐ r ∂cappedInnerLoop p c w a M t h, InnerSupported r := by
  induction t generalizing h with
  | zero => exact (ae_dirac_iff measurableSet_innerSupported).mpr trivial
  | succ t ih =>
    rw [cappedInnerLoop]
    apply ae_bind_of_ae_ae (measurable_cappedInner_continuation hn p c ho w a h M t) measurableSet_innerSupported
    filter_upwards [aggregateLaw_residual_mask hn c.oracle (by linarith [ho.lam_lower])
      ho.eps_pos p.gamma w h] with a ha
    split_ifs
    · exact (ae_dirac_iff measurableSet_innerSupported).mpr ha
    · exact ih _

end DPCut
