import DPCut.OracleReplacement

/-! Joint measurability and probability preservation for an arbitrary Markov witness oracle. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut.OracleReplacement
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

theorem measurable_aggregateLoop {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (γ : ℝ) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w h : A → Weights n} {a : A → Aggregate n},
      Measurable w → Measurable h → Measurable a →
      Measurable (fun x => aggregateLoop K γ (w x) (h x) t (a x)) := by
  induction t with
  | zero =>
    intro A _ w h a hw hh ha
    exact Measure.measurable_dirac.comp ha
  | succ t ih =>
    intro A _ w h a hw hh ha
    have hr := measurable_aggregate_residual.comp ha
    have hplus : Measurable (fun x => K (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)) := by
      have hD : Measurable (fun x => plusDiscrepancy γ (w x) (h x) (a x).residual) := by
        unfold plusDiscrepancy
        fun_prop
      change Measurable ((fun p : Weights n × Weights n => K p) ∘
        (fun x => (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)))
      exact K.measurable.comp (hD.prodMk hr)
    have hminus : Measurable (fun x => K (minusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)) := by
      have hD : Measurable (fun x => minusDiscrepancy γ (w x) (h x) (a x).residual) := by
        unfold minusDiscrepancy
        fun_prop
      change Measurable ((fun p : Weights n × Weights n => K p) ∘
        (fun x => (minusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)))
      exact K.measurable.comp (hD.prodMk hr)
    have hpcont : Measurable (fun p : A × Weights n => aggregateLoop K γ
        (w p.1) (h p.1) t ⟨(a p.1).plus + p.2, (a p.1).minus, (a p.1).residual - p.2⟩) := by
      apply ih (hw.comp measurable_fst) (hh.comp measurable_fst)
      apply measurable_aggregate_mk <;> fun_prop
    have hmcont : Measurable (fun p : A × Weights n => aggregateLoop K γ
        (w p.1) (h p.1) t ⟨(a p.1).plus, (a p.1).minus + p.2, (a p.1).residual - p.2⟩) := by
      apply ih (hw.comp measurable_fst) (hh.comp measurable_fst)
      apply measurable_aggregate_mk <;> fun_prop
    letI : ∀ x : A, IsProbabilityMeasure (K (minusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)) :=
      fun x => inferInstance
    letI : ∀ x : A, IsProbabilityMeasure (K (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)) :=
      fun x => inferInstance
    let fm := fun x (gm : Option (Weights n)) => gm.elim (Measure.dirac (a x))
      (fun g => aggregateLoop K γ (w x) (h x) t ⟨(a x).plus, (a x).minus + g, (a x).residual - g⟩)
    have hfm : Measurable (Function.uncurry fm) :=
      measurable_option_cases (Measure.measurable_dirac.comp ha) hmcont
    have hmc := measurable_bind_kernel (f := fm) hminus hfm
    let fp := fun x (gp : Option (Weights n)) => gp.elim
      ((K (minusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)).bind (fm x))
      (fun g => aggregateLoop K γ (w x) (h x) t ⟨(a x).plus + g, (a x).minus, (a x).residual - g⟩)
    have hfp : Measurable (Function.uncurry fp) := measurable_option_cases hmc hpcont
    have hpc := measurable_bind_kernel (f := fp) hplus hfp
    have hzero : MeasurableSet {x | (a x).residual = 0} := hr (measurableSet_singleton 0)
    have hite : Measurable (fun x => if (a x).residual = 0 then Measure.dirac (a x)
        else (K (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)).bind (fp x)) :=
      Measurable.ite hzero (Measure.measurable_dirac.comp ha) hpc
    change Measurable (fun x => if (a x).residual = 0 then Measure.dirac (a x)
      else (K (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)).bind (fp x))
    exact hite

lemma measurable_aggregateLaw {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (γ : ℝ) :
    Measurable (fun p : Weights n × Weights n => aggregateLaw K γ p.1 p.2) :=
  measurable_aggregateLoop K γ _ measurable_fst measurable_snd measurable_const

theorem aggregateLoop_probability {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K] (γ : ℝ) (w h : Weights n) (t : ℕ)
    (a : Aggregate n) : IsProbabilityMeasure (aggregateLoop K γ w h t a) := by
  induction t generalizing a with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac a))
  | succ t ih =>
    rw [aggregateLoop]
    split_ifs
    · infer_instance
    · have hm := measurable_option_elim (Measure.dirac a)
        (measurable_aggregateLoop K γ t (measurable_const (a := w)) (measurable_const (a := h))
          (measurable_aggregateMinusStep a))
      have hp := measurable_option_elim
        ((K (minusDiscrepancy γ w h a.residual, a.residual)).bind fun gm =>
          gm.elim (Measure.dirac a) (fun g => aggregateLoop K γ w h t (aggregateMinusStep a g)))
        (measurable_aggregateLoop K γ t (measurable_const (a := w)) (measurable_const (a := h))
          (measurable_aggregatePlusStep a))
      letI (gm : Option (Weights n)) : IsProbabilityMeasure
          (gm.elim (Measure.dirac a) (fun g => aggregateLoop K γ w h t (aggregateMinusStep a g))) := by
        cases gm with
        | none => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac a))
        | some g => exact ih _
      letI (gp : Option (Weights n)) : IsProbabilityMeasure
          (gp.elim ((K (minusDiscrepancy γ w h a.residual, a.residual)).bind fun gm =>
            gm.elim (Measure.dirac a) (fun g => aggregateLoop K γ w h t (aggregateMinusStep a g)))
            (fun g => aggregateLoop K γ w h t (aggregatePlusStep a g))) := by
        cases gp with
        | none => exact probability_bind _ _ hm
        | some g => exact ih _
      exact probability_bind _ _ hp

instance aggregateLaw_probability {n : ℕ} (K : WitnessKernel n) [IsMarkovKernel K]
    (γ : ℝ) (w h : Weights n) : IsProbabilityMeasure (aggregateLaw K γ w h) :=
  aggregateLoop_probability K γ w h _ _

theorem measurable_innerLoop (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w h : A → Weights n} {M : A → ℝ},
      Measurable w → Measurable h → Measurable M →
      Measurable (fun x => innerLoop K p c (w x) (M x) t (h x)) := by
  induction t with
  | zero => intro A _ w h M hw hh hM; exact measurable_const
  | succ t ih =>
    intro A _ w h M hw hh hM
    have hm : Measurable (fun x => aggregateLaw K p.gamma (w x) (h x)) := by
      change Measurable ((fun q : Weights n × Weights n => aggregateLaw K p.gamma q.1 q.2) ∘
        (fun x => (w x, h x)))
      exact (measurable_aggregateLaw K p.gamma).comp (hw.prodMk hh)
    letI : ∀ x, IsProbabilityMeasure (aggregateLaw K p.gamma (w x) (h x)) :=
      fun x => aggregateLaw_probability K p.gamma _ _
    have hc : Measurable (fun q : A × Aggregate n => if q.2.Accepts (h q.1)
        then Measure.dirac (some (h q.1, q.2.residual))
        else innerLoop K p c (w q.1) (M q.1) t (innerNext c (M q.1) (h q.1) q.2)) := by
      apply Measurable.ite (measurableSet_aggregateAccepts (hh.comp measurable_fst) measurable_snd)
      · apply Measure.measurable_dirac.comp
        apply measurable_some.comp
        exact (hh.comp measurable_fst).prodMk (measurable_aggregate_residual.comp measurable_snd)
      · exact ih (hw.comp measurable_fst)
          (measurable_innerNext c (hM.comp measurable_fst) (hh.comp measurable_fst) measurable_snd)
          (hM.comp measurable_fst)
    simp_rw [innerLoop]
    exact measurable_bind_kernel hm (show Measurable (Function.uncurry _) from hc)

lemma measurable_inner_continuation (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (w h : Weights n) (M : ℝ) (t : ℕ) :
    Measurable (fun a : Aggregate n => if a.Accepts h then Measure.dirac (some (h, a.residual))
      else innerLoop K p c w M t (innerNext c M h a)) := by
  apply Measurable.ite (measurableSet_aggregateAccepts measurable_const measurable_id)
  · exact Measure.measurable_dirac.comp (measurable_some.comp
      (measurable_const.prodMk measurable_aggregate_residual))
  · exact measurable_innerLoop K p c t measurable_const
      (measurable_innerNext c measurable_const measurable_const measurable_id) measurable_const

theorem innerLoop_probability (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (w : Weights n) (M : ℝ) (t : ℕ) (h : Weights n) :
    IsProbabilityMeasure (innerLoop K p c w M t h) := by
  induction t generalizing h with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac none))
  | succ t ih =>
    rw [innerLoop]
    letI := aggregateLaw_probability K p.gamma w h
    letI : ∀ a : Aggregate n, IsProbabilityMeasure
        (if a.Accepts h then Measure.dirac (some (h, a.residual))
          else innerLoop K p c w M t (innerNext c M h a)) := fun a => by
      split_ifs
      · infer_instance
      · exact ih _
    exact probability_bind _ _ (measurable_inner_continuation K p c w h M t)

theorem measurable_outerLoop (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (he : 0 < c.eps2) (t : ℕ) :
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
    let M := fun q : A × ℝ => clipNoisyMass c.massCap (mass (hadamard (a q.1) (w q.1))) q.2 c.tau2
    have hM : Measurable M := by dsimp [M]; fun_prop
    have hinner : Measurable (fun q : A × ℝ => innerLoop K p c (hadamard (a q.1) (w q.1))
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      measurable_innerLoop K p c c.T2 (by fun_prop) (by fun_prop) hM
    letI : ∀ q : A × ℝ, IsProbabilityMeasure (innerLoop K p c (hadamard (a q.1) (w q.1))
        (M q) c.T2 (initialEstimate (M q) (a q.1))) :=
      fun q => innerLoop_probability K p c _ _ _ _
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
    simp_rw [outerLoop]
    exact measurable_bind_kernel (measurable_const (a := laplace (1 / c.eps2)))
      (show Measurable (Function.uncurry _) from hstep)

lemma measurable_outerResult (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerResult K p c w t a out) := by
  apply measurable_from_option
  exact measurable_outerLoop K p c he t measurable_const (by fun_prop) (by fun_prop)

lemma measurable_outerAfterMass (K : WitnessKernel n) [IsMarkovKernel K] (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) : Measurable (outerAfterMass K p c w t a out) := by
  have hm : Measurable (fun M => innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    measurable_innerLoop K p c c.T2 measurable_const (by fun_prop) measurable_id
  letI : ∀ M, IsProbabilityMeasure (innerLoop K p c (hadamard a w) M c.T2 (initialEstimate M a)) :=
    fun M => innerLoop_probability K p c _ _ _ _
  apply Measurable.ite ((MeasurableSet.const _).union (measurableSet_le measurable_id measurable_const)) measurable_const
  exact measurable_bind_kernel hm (show Measurable (Function.uncurry
    (fun (_ : ℝ) r => outerResult K p c w t a out r)) from
      (measurable_outerResult K p c he w a out t).comp measurable_snd)

instance outerLoop_probability (K : WitnessKernel n) [IsMarkovKernel K]
    (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w : Weights n) (t : ℕ) (a out : Weights n) :
    IsProbabilityMeasure (outerLoop K p c w t a out) := by
  induction t generalizing a out with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac out))
  | succ t ih =>
    rw [outerLoop]
    letI := laplace_isProbabilityMeasure (one_div_pos.mpr he)
    letI : ∀ r, IsProbabilityMeasure (outerResult K p c w t a out r) := fun r => by
      cases r <;> exact ih _ _
    letI : ∀ M, IsProbabilityMeasure (outerAfterMass K p c w t a out M) := fun M => by
      unfold outerAfterMass
      split_ifs
      · infer_instance
      · letI := innerLoop_probability K p c (hadamard a w) M c.T2 (initialEstimate M a)
        exact probability_bind _ _ (measurable_outerResult K p c he w a out t)
    change IsProbabilityMeasure ((laplace (1 / c.eps2)).bind
      (fun noise => outerAfterMass K p c w t a out
        (clipNoisyMass c.massCap (mass (hadamard a w)) noise c.tau2)))
    exact probability_bind _ _ ((measurable_outerAfterMass K p c he w a out t).comp (by fun_prop))

instance outerResult_probability (K : WitnessKernel n) [IsMarkovKernel K]
    (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (r : Option (Weights n × Weights n)) :
    IsProbabilityMeasure (outerResult K p c w t a out r) := by
  cases r <;> exact outerLoop_probability K p c he _ _ _ _

instance outerAfterMass_probability (K : WitnessKernel n) [IsMarkovKernel K]
    (p : Parameters) (c : RunConfig) (he : 0 < c.eps2)
    (w a out : Weights n) (t : ℕ) (M : ℝ) :
    IsProbabilityMeasure (outerAfterMass K p c w t a out M) := by
  unfold outerAfterMass
  split_ifs
  · infer_instance
  · letI := innerLoop_probability K p c (hadamard a w) M c.T2 (initialEstimate M a)
    letI : ∀ r, IsProbabilityMeasure (outerResult K p c w t a out r) :=
      outerResult_probability K p c he w a out t
    exact probability_bind _ _ (measurable_outerResult K p c he w a out t)

end DPCut.OracleReplacement
