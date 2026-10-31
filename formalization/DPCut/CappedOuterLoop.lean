import DPCut.CappedInnerLoop
import DPCut.CappedNoisyMass
import DPCut.OuterLoopMeasurable

/-! Actual capped outer loop and its measurable probability law. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def cappedOuterLoop (p : Parameters) (c : RunConfig) (w : Weights n) :
    ℕ → Weights n → Weights n → Measure (Weights n)
  | 0, _, output => Measure.dirac output
  | t + 1, a, output =>
      let wi := hadamard a w
      (laplace (1 / c.eps2)).bind fun noise =>
      let M := lowerBiasedMass (mass a) (mass wi) noise c.tau2
      if a = 0 ∨ M ≤ c.stop then Measure.dirac output else
      (cappedInnerLoop p c wi a M c.T2 (initialEstimate M a)).bind fun result =>
      match result with
      | none => cappedOuterLoop p c w t a output
      | some (h, r) => cappedOuterLoop p c w t (residualUpdate a r) (output + hadamard h r)

def cappedOuterResult (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (r : Option (Weights n × Weights n)) : Measure (Weights n) :=
  r.elim (cappedOuterLoop p c w t a out)
    (fun hr => cappedOuterLoop p c w t (residualUpdate a hr.2) (out + hadamard hr.1 hr.2))

def cappedOuterAfterMass (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (M : ℝ) : Measure (Weights n) :=
  if a = 0 ∨ M ≤ c.stop then Measure.dirac out else
    (cappedInnerLoop p c (hadamard a w) a M c.T2 (initialEstimate M a)).bind (cappedOuterResult p c w t a out)

lemma cappedOuterLoop_succ_raw (p : Parameters) (c : RunConfig) (w : Weights n)
    (t : ℕ) (a out : Weights n) :
    cappedOuterLoop p c w (t + 1) a out = (laplace (1 / c.eps2)).bind
      (fun noise => cappedOuterAfterMass p c w t a out (lowerBiasedMass (mass a) (mass (hadamard a w)) noise c.tau2)) := by
  rw [cappedOuterLoop]
  congr 1
  funext noise
  dsimp only [cappedOuterAfterMass]
  split_ifs
  · rfl
  · congr 1
    funext r
    cases r <;> rfl

theorem measurable_cappedOuterLoop (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w a out : A → Weights n},
      Measurable w → Measurable a → Measurable out →
      Measurable (fun x => cappedOuterLoop p c (w x) t (a x) (out x)) := by
  induction t with
  | zero => intro A _ w a out hw ha hout; exact Measure.measurable_dirac.comp hout
  | succ t ih =>
    intro A _ w a out hw ha hout
    have hnone := ih hw ha hout
    have hsome : Measurable (fun q : A × (Weights n × Weights n) =>
        cappedOuterLoop p c (w q.1) t (residualUpdate (a q.1) q.2.2)
          (out q.1 + hadamard q.2.1 q.2.2)) := by
      apply ih (hw.comp measurable_fst) <;> fun_prop
    have hresult : Measurable (fun q : A × Option (Weights n × Weights n) =>
        cappedOuterResult p c (w q.1) t (a q.1) (out q.1) q.2) :=
      measurable_option_cases hnone hsome
    let M := fun q : A × ℝ => lowerBiasedMass (mass (a q.1)) (mass (hadamard (a q.1) (w q.1))) q.2 c.tau2
    have hM : Measurable M := by dsimp [M]; fun_prop
    have hinner : Measurable (fun q : A × ℝ => cappedInnerLoop p c (hadamard (a q.1) (w q.1)) (a q.1)
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      measurable_cappedInnerLoop hn p c ho c.T2 (by fun_prop) (ha.comp measurable_fst) (by fun_prop) hM
    letI : ∀ q : A × ℝ, IsProbabilityMeasure (cappedInnerLoop p c (hadamard (a q.1) (w q.1)) (a q.1)
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      fun q => cappedInnerLoop_probability hn p c ho _ _ _ _ _
    have hcont : Measurable (fun q : (A × ℝ) × Option (Weights n × Weights n) =>
        cappedOuterResult p c (w q.1.1) t (a q.1.1) (out q.1.1) q.2) :=
      hresult.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hbind := measurable_bind_kernel
      (f := fun q r => cappedOuterResult p c (w q.1) t (a q.1) (out q.1) r) hinner hcont
    have hstop : MeasurableSet {q : A × ℝ | a q.1 = 0 ∨ M q ≤ c.stop} :=
      ((ha.comp measurable_fst) (measurableSet_singleton 0)).union (measurableSet_le hM measurable_const)
    have hstep : Measurable (fun q : A × ℝ => cappedOuterAfterMass p c (w q.1) t
        (a q.1) (out q.1) (M q)) :=
      Measurable.ite hstop (Measure.measurable_dirac.comp (hout.comp measurable_fst)) hbind
    letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / c.eps2)
    simp_rw [cappedOuterLoop_succ_raw]
    exact measurable_bind_kernel (measurable_const (a := laplace (1 / c.eps2)))
      (show Measurable (Function.uncurry _) from hstep)

lemma measurable_cappedOuterResult (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (cappedOuterResult p c w t a out) := by
  apply measurable_from_option
  exact measurable_cappedOuterLoop hn p c ho he t measurable_const (by fun_prop) (by fun_prop)

lemma measurable_cappedOuterAfterMass (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (cappedOuterAfterMass p c w t a out) := by
  have hm : Measurable (fun M => cappedInnerLoop p c (hadamard a w) a M c.T2 (initialEstimate M a)) :=
    measurable_cappedInnerLoop hn p c ho c.T2 measurable_const measurable_const (by fun_prop) measurable_id
  letI : ∀ M, IsProbabilityMeasure (cappedInnerLoop p c (hadamard a w) a M c.T2 (initialEstimate M a)) :=
    fun M => cappedInnerLoop_probability hn p c ho _ _ _ _ _
  apply Measurable.ite ((MeasurableSet.const _).union (measurableSet_le measurable_id measurable_const)) measurable_const
  exact measurable_bind_kernel hm (show Measurable (Function.uncurry
    (fun (_ : ℝ) r => cappedOuterResult p c w t a out r)) from
      (measurable_cappedOuterResult hn p c ho he w a out t).comp measurable_snd)

lemma cappedOuterLoop_succ_noisyMass (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    cappedOuterLoop p c w (t + 1) a out =
      (cappedNoisyMassLaw c.eps2 c.tau2 (mass a) (hadamard a w)).bind (cappedOuterAfterMass p c w t a out) := by
  rw [cappedOuterLoop_succ_raw, cappedNoisyMassLaw, bind_map_eq (by fun_prop)
    (measurable_cappedOuterAfterMass hn p c ho he w a out t)]

theorem cappedOuterLoop_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    IsProbabilityMeasure (cappedOuterLoop p c w t a out) := by
  induction t generalizing a out with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac out))
  | succ t ih =>
    rw [cappedOuterLoop_succ_noisyMass hn p c ho he]
    letI := cappedNoisyMassLaw_probability he c.tau2 (mass a) (hadamard a w)
    letI : ∀ r, IsProbabilityMeasure (cappedOuterResult p c w t a out r) := fun r => by
      cases r <;> exact ih _ _
    letI : ∀ M, IsProbabilityMeasure (cappedOuterAfterMass p c w t a out M) := fun M => by
      unfold cappedOuterAfterMass
      split_ifs
      · infer_instance
      · letI := cappedInnerLoop_probability hn p c ho (hadamard a w) a M c.T2 (initialEstimate M a)
        exact probability_bind _ _ (measurable_cappedOuterResult hn p c ho he w a out t)
    exact probability_bind _ _ (measurable_cappedOuterAfterMass hn p c ho he w a out t)

lemma cappedOuterResult_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (r : Option (Weights n × Weights n)) :
    IsProbabilityMeasure (cappedOuterResult p c w t a out r) := by
  cases r <;> exact cappedOuterLoop_probability hn p c ho he _ _ _ _

lemma cappedOuterAfterMass_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (M : ℝ) :
    IsProbabilityMeasure (cappedOuterAfterMass p c w t a out M) := by
  unfold cappedOuterAfterMass
  split_ifs
  · infer_instance
  · letI := cappedInnerLoop_probability hn p c ho (hadamard a w) a M c.T2 (initialEstimate M a)
    letI : ∀ r, IsProbabilityMeasure (cappedOuterResult p c w t a out r) :=
      cappedOuterResult_probability hn p c ho he w a out t
    exact probability_bind _ _ (measurable_cappedOuterResult hn p c ho he w a out t)

end DPCut
