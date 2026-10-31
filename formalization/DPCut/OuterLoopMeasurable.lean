import DPCut.InnerLoopMeasurable
import DPCut.NoisyMassPrivacy

/-! Measurable continuation and probability semantics of CutRelease. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DPCut
attribute [local instance] Classical.propDecidable

variable {A : Type*} [MeasurableSpace A] {n : ℕ}

@[fun_prop] lemma measurable_hadamard {a w : A → Weights n} (ha : Measurable a) (hw : Measurable w) :
    Measurable (fun x => hadamard (a x) (w x)) := by unfold hadamard; fun_prop

@[fun_prop] lemma measurable_mass {w : A → Weights n} (hw : Measurable w) :
    Measurable (fun x => mass (w x)) := by unfold mass; fun_prop

@[fun_prop] lemma measurable_initialEstimate {M : A → ℝ} {a : A → Weights n}
    (hM : Measurable M) (ha : Measurable a) : Measurable (fun x => initialEstimate (M x) (a x)) := by
  unfold initialEstimate
  fun_prop

@[fun_prop] lemma measurable_residualUpdate {a r : A → Weights n} (ha : Measurable a) (hr : Measurable r) :
    Measurable (fun x => residualUpdate (a x) (r x)) := by unfold residualUpdate; fun_prop

def outerResult (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (r : Option (Weights n × Weights n)) : Measure (Weights n) :=
  r.elim (outerLoop p c w t a out)
    (fun hr => outerLoop p c w t (residualUpdate a hr.2) (out + hadamard hr.1 hr.2))

def outerAfterMass (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (M : ℝ) : Measure (Weights n) :=
  if a = 0 ∨ M ≤ c.stop then Measure.dirac out else
    (innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)).bind (outerResult p c w t a out)

lemma outerLoop_succ_raw (p : Parameters) (c : RunConfig) (w : Weights n)
    (t : ℕ) (a out : Weights n) :
    outerLoop p c w (t + 1) a out = (laplace (1 / c.eps2)).bind
      (fun noise => outerAfterMass p c w t a out (clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2)) := by
  rw [outerLoop]
  congr 1
  funext noise
  dsimp only [outerAfterMass]
  split_ifs
  · rfl
  · congr 1
    funext r
    cases r <;> rfl

theorem measurable_outerLoop (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w a out : A → Weights n},
      Measurable w → Measurable a → Measurable out →
      Measurable (fun x => outerLoop p c (w x) t (a x) (out x)) := by
  induction t with
  | zero => intro A _ w a out hw ha hout; exact Measure.measurable_dirac.comp hout
  | succ t ih =>
    intro A _ w a out hw ha hout
    have hnone := ih hw ha hout
    have hsome : Measurable (fun q : A × (Weights n × Weights n) =>
        outerLoop p c (w q.1) t (residualUpdate (a q.1) q.2.2)
          (out q.1 + hadamard q.2.1 q.2.2)) := by
      apply ih (hw.comp measurable_fst) <;> fun_prop
    have hresult : Measurable (fun q : A × Option (Weights n × Weights n) =>
        outerResult p c (w q.1) t (a q.1) (out q.1) q.2) :=
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
        outerResult p c (w q.1.1) t (a q.1.1) (out q.1.1) q.2) :=
      hresult.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hbind := measurable_bind_kernel
      (f := fun q r => outerResult p c (w q.1) t (a q.1) (out q.1) r) hinner hcont
    have hstop : MeasurableSet {q : A × ℝ | a q.1 = 0 ∨ M q ≤ c.stop} :=
      ((ha.comp measurable_fst) (measurableSet_singleton 0)).union (measurableSet_le hM measurable_const)
    have hstep : Measurable (fun q : A × ℝ => outerAfterMass p c (w q.1) t
        (a q.1) (out q.1) (M q)) :=
      Measurable.ite hstop (Measure.measurable_dirac.comp (hout.comp measurable_fst)) hbind
    letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / c.eps2)
    simp_rw [outerLoop_succ_raw]
    exact measurable_bind_kernel (measurable_const (a := laplace (1 / c.eps2)))
      (show Measurable (Function.uncurry _) from hstep)

lemma measurable_outerResult (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerResult p c w t a out) := by
  apply measurable_from_option
  exact measurable_outerLoop hn p c ho he t measurable_const (by fun_prop) (by fun_prop)

lemma measurable_outerAfterMass (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerAfterMass p c w t a out) := by
  have hm : Measurable (fun M => innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    measurable_innerLoop hn p c ho c.T2 measurable_const (by fun_prop) measurable_id
  letI : ∀ M, IsProbabilityMeasure (innerLoop p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    fun M => innerLoop_probability hn p c ho _ _ _ _
  apply Measurable.ite ((MeasurableSet.const _).union (measurableSet_le measurable_id measurable_const)) measurable_const
  exact measurable_bind_kernel hm (show Measurable (Function.uncurry
    (fun (_ : ℝ) r => outerResult p c w t a out r)) from
      (measurable_outerResult hn p c ho he w a out t).comp measurable_snd)

lemma outerLoop_succ_noisyMass (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    outerLoop p c w (t + 1) a out =
      (noisyMassLaw c.eps2 c.tau2 c.massCap (hadamard a w)).bind (outerAfterMass p c w t a out) := by
  rw [outerLoop_succ_raw, noisyMassLaw, bind_map_eq (by fun_prop)
    (measurable_outerAfterMass hn p c ho he w a out t)]

theorem outerLoop_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    IsProbabilityMeasure (outerLoop p c w t a out) := by
  induction t generalizing a out with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac out))
  | succ t ih =>
    rw [outerLoop_succ_noisyMass hn p c ho he]
    letI := noisyMassLaw_probability he c.tau2 c.massCap (hadamard a w)
    letI : ∀ r, IsProbabilityMeasure (outerResult p c w t a out r) := fun r => by
      cases r <;> exact ih _ _
    letI : ∀ M, IsProbabilityMeasure (outerAfterMass p c w t a out M) := fun M => by
      unfold outerAfterMass
      split_ifs
      · infer_instance
      · letI := innerLoop_probability hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)
        exact probability_bind _ _ (measurable_outerResult hn p c ho he w a out t)
    exact probability_bind _ _ (measurable_outerAfterMass hn p c ho he w a out t)

lemma outerResult_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (r : Option (Weights n × Weights n)) :
    IsProbabilityMeasure (outerResult p c w t a out r) := by
  cases r <;> exact outerLoop_probability hn p c ho he _ _ _ _

lemma outerAfterMass_probability (hn : 2 ≤ n) (p : Parameters) (c : RunConfig)
    (ho : OraclePrivacyBounds n c.oracle) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (M : ℝ) :
    IsProbabilityMeasure (outerAfterMass p c w t a out M) := by
  unfold outerAfterMass
  split_ifs
  · infer_instance
  · letI := innerLoop_probability hn p c ho (hadamard a w) M c.T2 (initialEstimate M a)
    letI : ∀ r, IsProbabilityMeasure (outerResult p c w t a out r) :=
      outerResult_probability hn p c ho he w a out t
    exact probability_bind _ _ (measurable_outerResult hn p c ho he w a out t)

end DPCut
