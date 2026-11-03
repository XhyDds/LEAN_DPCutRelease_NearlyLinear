import DPCut.Lemma21
import DPCut.OuterLoopMeasurable

/-! Measurable probability semantics for the stopping flag. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def outerStopResult (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a : Weights n)
    (r : Option (Weights n × Weights n)) : Measure Bool :=
  r.elim (outerStopsLaw p c w t a)
    (fun hr => outerStopsLaw p c w t (residualUpdate a hr.2))

def outerStopAfterMass (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a : Weights n)
    (M : ℝ) : Measure Bool :=
  if a = 0 ∨ M ≤ c.stop then Measure.dirac true else
    (innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)).bind (outerStopResult p c w t a)

lemma outerStopsLaw_succ_raw (p : Parameters) (c : RunConfig) (w : Weights n)
    (t : ℕ) (a : Weights n) :
    outerStopsLaw p c w (t + 1) a = (laplace (1 / c.eps2)).bind
      (fun noise => outerStopAfterMass p c w t a (clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2)) := by
  rw [outerStopsLaw]
  congr 1
  funext noise
  dsimp only [outerStopAfterMass]
  split_ifs
  · rfl
  · congr 1
    funext r
    cases r <;> rfl

theorem measurable_outerStopsLaw (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w a : A → Weights n},
      Measurable w → Measurable a →
      Measurable (fun x => outerStopsLaw p c (w x) t (a x)) := by
  induction t with
  | zero => intro A _ w a hw ha; exact measurable_const
  | succ t ih =>
    intro A _ w a hw ha
    have hnone := ih hw ha
    have hsome : Measurable (fun q : A × (Weights n × Weights n) =>
        outerStopsLaw p c (w q.1) t (residualUpdate (a q.1) q.2.2)) := by
      apply ih (hw.comp measurable_fst)
      fun_prop
    have hresult : Measurable (fun q : A × Option (Weights n × Weights n) =>
        outerStopResult p c (w q.1) t (a q.1) q.2) :=
      measurable_option_cases hnone hsome
    let M := fun q : A × ℝ => clipNoisyMass c.massCap (mass (hadamard (a q.1) (w q.1))) q.2 c.tau2
    have hM : Measurable M := by dsimp [M]; fun_prop
    have hinner : Measurable (fun q : A × ℝ => innerLoop p c (hadamard (a q.1) (w q.1))
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      measurable_innerLoop hn p c ho c.T2 (by fun_prop) (by fun_prop) hM
    letI : ∀ q : A × ℝ, IsProbabilityMeasure (innerLoop p c (hadamard (a q.1) (w q.1))
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      fun q => innerLoop_probability hn p c ho _ _ _ _
    have hcont : Measurable (fun q : (A × ℝ) × Option (Weights n × Weights n) =>
        outerStopResult p c (w q.1.1) t (a q.1.1) q.2) :=
      hresult.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hbind := measurable_bind_kernel
      (f := fun q r => outerStopResult p c (w q.1) t (a q.1) r) hinner hcont
    have hstop : MeasurableSet {q : A × ℝ | a q.1 = 0 ∨ M q ≤ c.stop} :=
      ((ha.comp measurable_fst) (measurableSet_singleton 0)).union (measurableSet_le hM measurable_const)
    have hstep : Measurable (fun q : A × ℝ => outerStopAfterMass p c (w q.1) t
        (a q.1) (M q)) :=
      Measurable.ite hstop measurable_const hbind
    letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / c.eps2)
    simp_rw [outerStopsLaw_succ_raw]
    exact measurable_bind_kernel (measurable_const (a := laplace (1 / c.eps2)))
      (show Measurable (Function.uncurry _) from hstep)

lemma measurable_outerStopResult (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a : Weights n) (t : ℕ) : Measurable (outerStopResult p c w t a) := by
  apply measurable_from_option
  exact measurable_outerStopsLaw hn p c ho he t measurable_const (by fun_prop)

lemma measurable_outerStopAfterMass (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a : Weights n) (t : ℕ) : Measurable (outerStopAfterMass p c w t a) := by
  have hm : Measurable (fun M => innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    measurable_innerLoop hn p c ho c.T2 measurable_const (by fun_prop) measurable_id
  letI : ∀ M, IsProbabilityMeasure (innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    fun M => innerLoop_probability hn p c ho _ _ _ _
  apply Measurable.ite ((MeasurableSet.const _).union (measurableSet_le measurable_id measurable_const)) measurable_const
  exact measurable_bind_kernel hm (show Measurable (Function.uncurry
    (fun (_ : ℝ) r => outerStopResult p c w t a r)) from
      (measurable_outerStopResult hn p c ho he w a t).comp measurable_snd)


theorem outerStopsLaw_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a : Weights n) : IsProbabilityMeasure (outerStopsLaw p c w t a) := by
  induction t generalizing a with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac false))
  | succ t ih =>
    rw [outerStopsLaw_succ_raw]
    letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
    letI (r : Option (Weights n × Weights n)) : IsProbabilityMeasure (outerStopResult p c w t a r) := by
      cases r <;> exact ih _
    letI (M : ℝ) : IsProbabilityMeasure (outerStopAfterMass p c w t a M) := by
      unfold outerStopAfterMass
      split_ifs
      · infer_instance
      · letI := innerLoop_probability hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)
        exact probability_bind _ _ (measurable_outerStopResult hn p c ho he w a t)
    exact probability_bind _ _ ((measurable_outerStopAfterMass hn p c ho he w a t).comp (by fun_prop))

lemma outerStopResult_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a : Weights n) (t : ℕ) (r : Option (Weights n × Weights n)) :
    IsProbabilityMeasure (outerStopResult p c w t a r) := by
  cases r <;> exact outerStopsLaw_probability hn p c ho he _ _ _

lemma outerStopAfterMass_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a : Weights n) (t : ℕ) (M : ℝ) : IsProbabilityMeasure (outerStopAfterMass p c w t a M) := by
  unfold outerStopAfterMass
  split_ifs
  · infer_instance
  · letI := innerLoop_probability hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)
    letI (r : Option (Weights n × Weights n)) := outerStopResult_probability hn p c ho he w a t r
    exact probability_bind _ _ (measurable_outerStopResult hn p c ho he w a t)

end DPCut
