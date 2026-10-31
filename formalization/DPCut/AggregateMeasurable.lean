import DPCut.Lemma17

/-! Measurability and residual-mask support of AggregateWitnesses. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut
attribute [local instance] Classical.propDecidable

lemma measurable_option_cases {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [Inhabited C] {f : A → B} {g : A × C → B}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p : A × Option C => p.2.elim (f p.1) (fun c => g (p.1, c))) := by
  have hm : Measurable (fun p : A × Option C => if p.2 = none then f p.1
      else g (p.1, p.2.getD default)) :=
    Measurable.ite (measurable_snd measurableSet_option_none) (hf.comp measurable_fst)
      (hg.comp (measurable_fst.prodMk ((measurable_option_getD default).comp measurable_snd)))
  convert hm using 1
  funext p
  cases p.2 <;> simp

def aggregateMeasurableEquiv (n : ℕ) : Aggregate n ≃ᵐ Weights n × Weights n × Weights n where
  toFun a := (a.plus, a.minus, a.residual)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro p; rfl
  measurable_toFun := comap_measurable _
  measurable_invFun := measurable_aggregate_mk measurable_fst
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)

instance aggregate_standardBorel (n : ℕ) : StandardBorelSpace (Aggregate n) :=
  standardBorel_of_equiv (aggregateMeasurableEquiv n)

@[fun_prop] lemma measurable_aggregate_plus {n : ℕ} :
    Measurable (Aggregate.plus : Aggregate n → Weights n) :=
  measurable_fst.comp (aggregateMeasurableEquiv n).measurable

@[fun_prop] lemma measurable_aggregate_minus {n : ℕ} :
    Measurable (Aggregate.minus : Aggregate n → Weights n) :=
  (measurable_fst.comp measurable_snd).comp (aggregateMeasurableEquiv n).measurable

@[fun_prop] lemma measurable_aggregate_residual {n : ℕ} :
    Measurable (Aggregate.residual : Aggregate n → Weights n) :=
  (measurable_snd.comp measurable_snd).comp (aggregateMeasurableEquiv n).measurable

theorem measurable_aggregateLoop {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (γ : ℝ) (t : ℕ) :
    ∀ {A : Type} [MeasurableSpace A] {w h : A → Weights n} {a : A → Aggregate n},
      Measurable w → Measurable h → Measurable a →
      Measurable (fun x => aggregateLoop o γ (w x) (h x) t (a x)) := by
  induction t with
  | zero =>
    intro A _ w h a hw hh ha
    exact Measure.measurable_dirac.comp ha
  | succ t ih =>
    intro A _ w h a hw hh ha
    have hr := measurable_aggregate_residual.comp ha
    have hplus : Measurable (fun x => findWitness o
        (plusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual) := by
      have hD : Measurable (fun x => plusDiscrepancy γ (w x) (h x) (a x).residual) := by
        unfold plusDiscrepancy
        fun_prop
      change Measurable ((fun p : Weights n × Weights n => findWitness o p.1 p.2) ∘
        (fun x => (plusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)))
      exact (measurable_findWitness hn o hl he).comp (hD.prodMk hr)
    have hminus : Measurable (fun x => findWitness o
        (minusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual) := by
      have hD : Measurable (fun x => minusDiscrepancy γ (w x) (h x) (a x).residual) := by
        unfold minusDiscrepancy
        fun_prop
      change Measurable ((fun p : Weights n × Weights n => findWitness o p.1 p.2) ∘
        (fun x => (minusDiscrepancy γ (w x) (h x) (a x).residual, (a x).residual)))
      exact (measurable_findWitness hn o hl he).comp (hD.prodMk hr)
    have hpcont : Measurable (fun p : A × Weights n => aggregateLoop o γ
        (w p.1) (h p.1) t ⟨(a p.1).plus + p.2, (a p.1).minus, (a p.1).residual - p.2⟩) := by
      apply ih (hw.comp measurable_fst) (hh.comp measurable_fst)
      apply measurable_aggregate_mk <;> fun_prop
    have hmcont : Measurable (fun p : A × Weights n => aggregateLoop o γ
        (w p.1) (h p.1) t ⟨(a p.1).plus, (a p.1).minus + p.2, (a p.1).residual - p.2⟩) := by
      apply ih (hw.comp measurable_fst) (hh.comp measurable_fst)
      apply measurable_aggregate_mk <;> fun_prop
    letI : ∀ x : A, IsProbabilityMeasure (findWitness o
        (minusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual) :=
      fun x => findWitness_probability o he _ _
    letI : ∀ x : A, IsProbabilityMeasure (findWitness o
        (plusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual) :=
      fun x => findWitness_probability o he _ _
    let fm := fun x (gm : Option (Weights n)) => gm.elim (Measure.dirac (a x))
      (fun g => aggregateLoop o γ (w x) (h x) t ⟨(a x).plus, (a x).minus + g, (a x).residual - g⟩)
    have hfm : Measurable (Function.uncurry fm) :=
      measurable_option_cases (Measure.measurable_dirac.comp ha) hmcont
    have hmc := measurable_bind_kernel (f := fm) hminus hfm
    let fp := fun x (gp : Option (Weights n)) => gp.elim
      ((findWitness o (minusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual).bind (fm x))
      (fun g => aggregateLoop o γ (w x) (h x) t ⟨(a x).plus + g, (a x).minus, (a x).residual - g⟩)
    have hfp : Measurable (Function.uncurry fp) := measurable_option_cases hmc hpcont
    have hpc := measurable_bind_kernel (f := fp) hplus hfp
    have hzero : MeasurableSet {x | (a x).residual = 0} := hr (measurableSet_singleton 0)
    have hite : Measurable (fun x => if (a x).residual = 0 then Measure.dirac (a x)
        else (findWitness o (plusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual).bind (fp x)) :=
      Measurable.ite hzero (Measure.measurable_dirac.comp ha) hpc
    have heq : (fun x => aggregateLoop o γ (w x) (h x) (t + 1) (a x)) =
        (fun x => if (a x).residual = 0 then Measure.dirac (a x)
        else (findWitness o (plusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual).bind (fp x)) := by
      funext x
      rw [aggregateLoop]
      split_ifs
      · rfl
      · congr 1
        funext gp
        cases gp with
        | some g => rfl
        | none =>
          change (findWitness o (minusDiscrepancy γ (w x) (h x) (a x).residual) (a x).residual).bind _ = _
          congr 1
          funext gm
          cases gm <;> rfl
    rw [heq]
    exact hite

theorem measurable_aggregateLaw {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (γ : ℝ) :
    Measurable (fun p : Weights n × Weights n => aggregateLaw o γ p.1 p.2) :=
  measurable_aggregateLoop hn o hl he γ _ measurable_fst measurable_snd measurable_const

theorem aggregateLoop_residual_mask {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (γ : ℝ) (w h : Weights n)
    (t : ℕ) (a : Aggregate n) (ha : IsMask a.residual) :
    ∀ᵐ b ∂aggregateLoop o γ w h t a, IsMask b.residual := by
  have hset : MeasurableSet {b : Aggregate n | IsMask b.residual} :=
    measurableSet_isMask measurable_aggregate_residual
  induction t generalizing a with
  | zero => exact (ae_dirac_iff hset).mpr ha
  | succ t ih =>
    rw [aggregateLoop]
    split_ifs with hz
    · exact (ae_dirac_iff hset).mpr ha
    · have hm (side : Bool) : Measurable (fun y : Option (Weights n) =>
          y.elim (Measure.dirac a) (fun g => aggregateLoop o γ w h t
            (if side then {a with plus := a.plus + g, residual := a.residual - g}
              else {a with minus := a.minus + g, residual := a.residual - g}))) := by
        apply measurable_from_option
        simp only [Option.elim_some]
        apply measurable_aggregateLoop hn o hl he γ t measurable_const measurable_const
        cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
          apply measurable_aggregate_mk <;> fun_prop
      have hpcont : Measurable (fun gp : Option (Weights n) =>
          match gp with
          | some g => aggregateLoop o γ w h t {a with plus := a.plus + g, residual := a.residual - g}
          | none => (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
              match gm with
              | some g => aggregateLoop o γ w h t {a with minus := a.minus + g, residual := a.residual - g}
              | none => Measure.dirac a) := by
        apply measurable_from_option
        exact measurable_aggregateLoop hn o hl he γ t measurable_const measurable_const
          (measurable_aggregate_mk (measurable_const.add measurable_id) measurable_const
            (measurable_const.sub measurable_id))
      apply ae_bind_of_ae_ae hpcont hset
      filter_upwards [findWitness_supported o he (plusDiscrepancy γ w h a.residual) a.residual ha]
        with gp hgp
      cases gp with
      | some g => exact ih _ (witness_supported_residual _ _ _ ha hgp)
      | none =>
        have hm' : Measurable (fun gm : Option (Weights n) => match gm with
            | some g => aggregateLoop o γ w h t {a with minus := a.minus + g, residual := a.residual - g}
            | none => Measure.dirac a) := by
          convert hm false using 1
          funext y
          cases y <;> simp
        apply ae_bind_of_ae_ae hm' hset
        filter_upwards [findWitness_supported o he (minusDiscrepancy γ w h a.residual) a.residual ha]
          with gm hgm
        cases gm with
        | some g => exact ih _ (witness_supported_residual _ _ _ ha hgm)
        | none => exact (ae_dirac_iff hset).mpr ha

theorem aggregateLaw_residual_mask {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (γ : ℝ) (w h : Weights n) :
    ∀ᵐ a ∂aggregateLaw o γ w h, IsMask a.residual :=
  aggregateLoop_residual_mask hn o hl he γ w h _ _ (by simp [IsMask, Bounded])

end DPCut
