import DPCut.BoundedObjectiveRelease
import DPCut.CappedCosted

/-! The capped release with its witness kernel exposed for verified replacement. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.CappedReplacement
attribute [local instance] Classical.propDecidable

def innerLoop {n : ℕ} (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig) (w a : Weights n) (H : ℝ) :
    ℕ → Weights n → Measure (Option (Weights n × Weights n))
  | 0, _ => Measure.dirac none
  | t + 1, h => (OracleReplacement.aggregateLaw K p.gamma w h).bind fun b =>
      if b.Accepts h then Measure.dirac (some (h, b.residual))
      else innerLoop K p c w a H t (cappedNext c a H h b)

theorem measurable_innerLoop {n : ℕ} (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (t : ℕ) :
    ∀ {X : Type} [MeasurableSpace X] {w a h : X → Weights n} {H : X → ℝ},
      Measurable w → Measurable a → Measurable h → Measurable H →
      Measurable (fun x => innerLoop K p c (w x) (a x) (H x) t (h x)) := by
  induction t with
  | zero => intro X _ w a h H hw ha hh hH; exact measurable_const
  | succ t ih =>
    intro X _ w a h H hw ha hh hH
    have hm : Measurable (fun x => OracleReplacement.aggregateLaw K p.gamma (w x) (h x)) :=
      (OracleReplacement.measurable_aggregateLaw K p.gamma).comp
        (hw.prodMk hh)
    letI : ∀ x, IsProbabilityMeasure (OracleReplacement.aggregateLaw K p.gamma (w x) (h x)) :=
      fun _ => OracleReplacement.aggregateLaw_probability K p.gamma _ _
    change Measurable (fun x => (OracleReplacement.aggregateLaw K p.gamma (w x) (h x)).bind _)
    apply measurable_bind_kernel hm
    apply Measurable.ite (measurableSet_aggregateAccepts (hh.comp measurable_fst) measurable_snd)
    · exact Measure.measurable_dirac.comp (measurable_some.comp
        ((hh.comp measurable_fst).prodMk (measurable_aggregate_residual.comp measurable_snd)))
    · exact ih (hw.comp measurable_fst) (ha.comp measurable_fst)
        (measurable_cappedNext c (ha.comp measurable_fst) (hh.comp measurable_fst)
          (hH.comp measurable_fst) measurable_snd) (hH.comp measurable_fst)

lemma measurable_inner_continuation {n : ℕ} (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (w a h : Weights n) (H : ℝ) (t : ℕ) :
    Measurable (fun b : Aggregate n => if b.Accepts h then Measure.dirac (some (h, b.residual))
      else innerLoop K p c w a H t (cappedNext c a H h b)) := by
  apply Measurable.ite (measurableSet_aggregateAccepts measurable_const measurable_id)
  · exact Measure.measurable_dirac.comp (measurable_some.comp
      (measurable_const.prodMk measurable_aggregate_residual))
  · exact measurable_innerLoop K p c t measurable_const measurable_const
      (measurable_cappedNext c measurable_const measurable_const measurable_const measurable_id) measurable_const

theorem innerLoop_probability {n : ℕ} (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (w a : Weights n) (H : ℝ) (t : ℕ) (h : Weights n) :
    IsProbabilityMeasure (innerLoop K p c w a H t h) := by
  induction t generalizing h with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | succ t ih =>
    letI := OracleReplacement.aggregateLaw_probability K p.gamma w h
    letI : ∀ b : Aggregate n, IsProbabilityMeasure
        (if b.Accepts h then Measure.dirac (some (h, b.residual))
          else innerLoop K p c w a H t (cappedNext c a H h b)) := fun b => by
      split_ifs
      · infer_instance
      · exact ih _
    exact probability_bind _ _ (measurable_inner_continuation K p c w a h H t)


variable {n : ℕ}

def outerLoop (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig) (w : Weights n) :
    ℕ → Weights n → Weights n → Measure (Weights n)
  | 0, _, output => Measure.dirac output
  | t + 1, a, output =>
      let wi := hadamard a w
      (laplace (1 / c.eps2)).bind fun noise =>
      let M := lowerBiasedMass (mass a) (mass wi) noise c.tau2
      if a = 0 ∨ M ≤ c.stop then Measure.dirac output else
      (innerLoop K p c wi a M c.T2 (initialEstimate M a)).bind fun result =>
      match result with
      | none => outerLoop K p c w t a output
      | some (h, r) => outerLoop K p c w t (residualUpdate a r) (output + hadamard h r)

def outerResult (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (r : Option (Weights n × Weights n)) : Measure (Weights n) :=
  r.elim (outerLoop K p c w t a out)
    (fun hr => outerLoop K p c w t (residualUpdate a hr.2) (out + hadamard hr.1 hr.2))

def outerAfterMass (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig) (w : Weights n) (t : ℕ) (a out : Weights n)
    (M : ℝ) : Measure (Weights n) :=
  if a = 0 ∨ M ≤ c.stop then Measure.dirac out else
    (innerLoop K p c (hadamard a w) a M c.T2 (initialEstimate M a)).bind (outerResult K p c w t a out)

lemma outerLoop_succ_raw (K : OracleReplacement.WitnessKernel n) (p : Parameters) (c : RunConfig) (w : Weights n)
    (t : ℕ) (a out : Weights n) :
    outerLoop K p c w (t + 1) a out = (laplace (1 / c.eps2)).bind
      (fun noise => outerAfterMass K p c w t a out (lowerBiasedMass (mass a) (mass (hadamard a w)) noise c.tau2)) := by
  rw [outerLoop]
  congr 1
  funext noise
  dsimp only [outerAfterMass]
  split_ifs
  · rfl
  · congr 1
    funext r
    cases r <;> rfl

theorem measurable_outerLoop (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w a out : A → Weights n},
      Measurable w → Measurable a → Measurable out →
      Measurable (fun x => outerLoop K p c (w x) t (a x) (out x)) := by
  induction t with
  | zero => intro A _ w a out hw ha hout; exact Measure.measurable_dirac.comp hout
  | succ t ih =>
    intro A _ w a out hw ha hout
    have hnone := ih hw ha hout
    have hsome : Measurable (fun q : A × (Weights n × Weights n) =>
        outerLoop K p c (w q.1) t (residualUpdate (a q.1) q.2.2)
          (out q.1 + hadamard q.2.1 q.2.2)) := by
      apply ih (hw.comp measurable_fst) <;> fun_prop
    have hresult : Measurable (fun q : A × Option (Weights n × Weights n) =>
        outerResult K p c (w q.1) t (a q.1) (out q.1) q.2) :=
      measurable_option_cases hnone hsome
    let M := fun q : A × ℝ => lowerBiasedMass (mass (a q.1)) (mass (hadamard (a q.1) (w q.1))) q.2 c.tau2
    have hM : Measurable M := by dsimp [M]; fun_prop
    have hinner : Measurable (fun q : A × ℝ => innerLoop K p c (hadamard (a q.1) (w q.1)) (a q.1)
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      measurable_innerLoop K p c c.T2 (by fun_prop) (ha.comp measurable_fst) (by fun_prop) hM
    letI : ∀ q : A × ℝ, IsProbabilityMeasure (innerLoop K p c (hadamard (a q.1) (w q.1)) (a q.1)
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      fun q => innerLoop_probability K p c _ _ _ _ _
    have hcont : Measurable (fun q : (A × ℝ) × Option (Weights n × Weights n) =>
        outerResult K p c (w q.1.1) t (a q.1.1) (out q.1.1) q.2) :=
      hresult.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hbind := measurable_bind_kernel
      (f := fun q r => outerResult K p c (w q.1) t (a q.1) (out q.1) r) hinner hcont
    have hstop : MeasurableSet {q : A × ℝ | a q.1 = 0 ∨ M q ≤ c.stop} :=
      ((ha.comp measurable_fst) (measurableSet_singleton 0)).union (measurableSet_le hM measurable_const)
    have hstep : Measurable (fun q : A × ℝ => outerAfterMass K p c (w q.1) t
        (a q.1) (out q.1) (M q)) :=
      Measurable.ite hstop (Measure.measurable_dirac.comp (hout.comp measurable_fst)) hbind
    letI := laplace_isProbabilityMeasure (by positivity : 0 < 1 / c.eps2)
    simp_rw [outerLoop_succ_raw]
    exact measurable_bind_kernel (measurable_const (a := laplace (1 / c.eps2)))
      (show Measurable (Function.uncurry _) from hstep)

lemma measurable_outerResult (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerResult K p c w t a out) := by
  apply measurable_from_option
  exact measurable_outerLoop K p c he t measurable_const (by fun_prop) (by fun_prop)

lemma measurable_outerAfterMass (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerAfterMass K p c w t a out) := by
  have hm : Measurable (fun M => innerLoop K p c (hadamard a w) a M c.T2 (initialEstimate M a)) :=
    measurable_innerLoop K p c c.T2 measurable_const measurable_const (by fun_prop) measurable_id
  letI : ∀ M, IsProbabilityMeasure (innerLoop K p c (hadamard a w) a M c.T2 (initialEstimate M a)) :=
    fun M => innerLoop_probability K p c _ _ _ _ _
  apply Measurable.ite ((MeasurableSet.const _).union (measurableSet_le measurable_id measurable_const)) measurable_const
  exact measurable_bind_kernel hm (show Measurable (Function.uncurry
    (fun (_ : ℝ) r => outerResult K p c w t a out r)) from
      (measurable_outerResult K p c he w a out t).comp measurable_snd)

lemma outerLoop_succ_noisyMass (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    outerLoop K p c w (t + 1) a out =
      (cappedNoisyMassLaw c.eps2 c.tau2 (mass a) (hadamard a w)).bind (outerAfterMass K p c w t a out) := by
  rw [outerLoop_succ_raw, cappedNoisyMassLaw, bind_map_eq (by fun_prop)
    (measurable_outerAfterMass K p c he w a out t)]

theorem outerLoop_probability (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    IsProbabilityMeasure (outerLoop K p c w t a out) := by
  induction t generalizing a out with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac out))
  | succ t ih =>
    rw [outerLoop_succ_noisyMass K p c he]
    letI := cappedNoisyMassLaw_probability he c.tau2 (mass a) (hadamard a w)
    letI : ∀ r, IsProbabilityMeasure (outerResult K p c w t a out r) := fun r => by
      cases r <;> exact ih _ _
    letI : ∀ M, IsProbabilityMeasure (outerAfterMass K p c w t a out M) := fun M => by
      unfold outerAfterMass
      split_ifs
      · infer_instance
      · letI := innerLoop_probability K p c (hadamard a w) a M c.T2 (initialEstimate M a)
        exact probability_bind _ _ (measurable_outerResult K p c he w a out t)
    exact probability_bind _ _ (measurable_outerAfterMass K p c he w a out t)

lemma outerResult_probability (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (r : Option (Weights n × Weights n)) :
    IsProbabilityMeasure (outerResult K p c w t a out r) := by
  cases r <;> exact outerLoop_probability K p c he _ _ _ _

lemma outerAfterMass_probability (K : OracleReplacement.WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig)
    (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (M : ℝ) :
    IsProbabilityMeasure (outerAfterMass K p c w t a out M) := by
  unfold outerAfterMass
  split_ifs
  · infer_instance
  · letI := innerLoop_probability K p c (hadamard a w) a M c.T2 (initialEstimate M a)
    letI : ∀ r, IsProbabilityMeasure (outerResult K p c w t a out r) :=
      outerResult_probability K p c he w a out t
    exact probability_bind _ _ (measurable_outerResult K p c he w a out t)


end DPCut.CappedReplacement
