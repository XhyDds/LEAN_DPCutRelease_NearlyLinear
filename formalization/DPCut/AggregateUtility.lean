import DPCut.OracleUtility
import DPCut.InnerLoopMeasurable

/-! Adaptive utility and the finite-retirement invariant for AggregateWitnesses. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace DPCut
attribute [local instance] Classical.propDecidable

def aggregatePlusStep {n : ℕ} (a : Aggregate n) (g : Weights n) : Aggregate n :=
  ⟨a.plus + g, a.minus, a.residual - g⟩

def aggregateMinusStep {n : ℕ} (a : Aggregate n) (g : Weights n) : Aggregate n :=
  ⟨a.plus, a.minus + g, a.residual - g⟩

@[fun_prop] lemma measurable_aggregatePlusStep {n : ℕ} (a : Aggregate n) :
    Measurable (aggregatePlusStep a) :=
  measurable_aggregate_mk (measurable_const.add measurable_id) measurable_const
    (measurable_const.sub measurable_id)

@[fun_prop] lemma measurable_aggregateMinusStep {n : ℕ} (a : Aggregate n) :
    Measurable (aggregateMinusStep a) :=
  measurable_aggregate_mk measurable_const (measurable_const.add measurable_id)
    (measurable_const.sub measurable_id)

lemma aggregateLoop_succ_eq {n : ℕ} (o : OracleConfig) (γ : ℝ) (w h : Weights n)
    (t : ℕ) (a : Aggregate n) :
    aggregateLoop o γ w h (t + 1) a = if a.residual = 0 then Measure.dirac a else
      (findWitness o (plusDiscrepancy γ w h a.residual) a.residual).bind fun gp => gp.elim
        ((findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
          gm.elim (Measure.dirac a) (fun g => aggregateLoop o γ w h t (aggregateMinusStep a g)))
        (fun g => aggregateLoop o γ w h t (aggregatePlusStep a g)) := by
  rw [aggregateLoop]
  split_ifs
  · rfl
  · congr 1
    funext gp
    cases gp with
    | some g => rfl
    | none =>
      change (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind _ =
        (findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind _
      congr 1
      funext gm
      cases gm <;> rfl

theorem aggregateLoop_probability {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (hl : 0 < o.lam) (he : 0 < o.eps1) (γ : ℝ) (w h : Weights n) (t : ℕ)
    (a : Aggregate n) : IsProbabilityMeasure (aggregateLoop o γ w h t a) := by
  induction t generalizing a with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac a))
  | succ t ih =>
    rw [aggregateLoop_succ_eq]
    split_ifs
    · infer_instance
    · have hm := measurable_option_elim (Measure.dirac a)
        (measurable_aggregateLoop hn o hl he γ t (measurable_const (a := w)) (measurable_const (a := h))
          (measurable_aggregateMinusStep a))
      have hp := measurable_option_elim
        ((findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
          gm.elim (Measure.dirac a) (fun g => aggregateLoop o γ w h t (aggregateMinusStep a g)))
        (measurable_aggregateLoop hn o hl he γ t (measurable_const (a := w)) (measurable_const (a := h))
          (measurable_aggregatePlusStep a))
      letI := findWitness_probability o he (plusDiscrepancy γ w h a.residual) a.residual
      letI := findWitness_probability o he (minusDiscrepancy γ w h a.residual) a.residual
      letI (gm : Option (Weights n)) : IsProbabilityMeasure
          (gm.elim (Measure.dirac a) (fun g => aggregateLoop o γ w h t (aggregateMinusStep a g))) := by
        cases gm with
        | none => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac a))
        | some g => exact ih _
      letI (gp : Option (Weights n)) : IsProbabilityMeasure
          (gp.elim ((findWitness o (minusDiscrepancy γ w h a.residual) a.residual).bind fun gm =>
            gm.elim (Measure.dirac a) (fun g => aggregateLoop o γ w h t (aggregateMinusStep a g)))
            (fun g => aggregateLoop o γ w h t (aggregatePlusStep a g))) := by
        cases gp with
        | none => exact probability_bind _ _ hm
        | some g => exact ih _
      exact probability_bind _ _ hp

lemma Aggregate.Partition.plus_step {n : ℕ} {a : Aggregate n} (ha : a.Partition)
    {g : Weights n} (hg : Retires a.residual g) : (aggregatePlusStep a g).Partition := by
  refine ⟨?_, ha.2.1, hg.residual_mask ha.2.2.1, ?_⟩
  · intro e
    change 0 ≤ a.plus e + g e ∧ a.plus e + g e ≤ 1
    constructor <;> linarith [(ha.1 e).1, (ha.2.1 e).1, (hg.1 e).1, (hg.1 e).2, ha.2.2.2 e]
  · intro e
    change a.plus e + g e + a.minus e + (a.residual e - g e) = 1
    linarith [ha.2.2.2 e]

lemma Aggregate.Partition.minus_step {n : ℕ} {a : Aggregate n} (ha : a.Partition)
    {g : Weights n} (hg : Retires a.residual g) : (aggregateMinusStep a g).Partition := by
  refine ⟨ha.1, ?_, hg.residual_mask ha.2.2.1, ?_⟩
  · intro e
    change 0 ≤ a.minus e + g e ∧ a.minus e + g e ≤ 1
    constructor <;> linarith [(ha.1 e).1, (ha.2.1 e).1, (hg.1 e).1, (hg.1 e).2, ha.2.2.2 e]
  · intro e
    change a.plus e + (a.minus e + g e) + (a.residual e - g e) = 1
    linarith [ha.2.2.2 e]

def AggregateInvariant {n : ℕ} (γ : ℝ) (w h : Weights n) (a : Aggregate n) : Prop :=
  a.Partition ∧ 0 ≤ pairing (fun e => h e - (1 + γ) * w e) a.plus ∧
    0 ≤ pairing (fun e => (1 - γ) * w e - h e) a.minus

lemma AggregateInvariant.plus_step {n : ℕ} {γ : ℝ} {w h : Weights n} {a : Aggregate n}
    (ha : AggregateInvariant γ w h a) {g : Weights n} (hg : Retires a.residual g)
    (hs : 0 ≤ pairing (fun e => h e - (1 + γ) * w e) g) :
    AggregateInvariant γ w h (aggregatePlusStep a g) := by
  refine ⟨ha.1.plus_step hg, ?_, ha.2.2⟩
  change 0 ≤ pairing _ (a.plus + g)
  rw [pairing_add_right]
  exact add_nonneg ha.2.1 hs

lemma AggregateInvariant.minus_step {n : ℕ} {γ : ℝ} {w h : Weights n} {a : Aggregate n}
    (ha : AggregateInvariant γ w h a) {g : Weights n} (hg : Retires a.residual g)
    (hs : 0 ≤ pairing (fun e => (1 - γ) * w e - h e) g) :
    AggregateInvariant γ w h (aggregateMinusStep a g) := by
  refine ⟨ha.1.minus_step hg, ha.2.1, ?_⟩
  change 0 ≤ pairing _ (a.minus + g)
  rw [pairing_add_right]
  exact add_nonneg ha.2.2 hs

lemma AggregateInvariant.accurate {n : ℕ} {γ B : ℝ} {w h : Weights n} {a : Aggregate n}
    (ha : AggregateInvariant γ w h a)
    (hc : AllCuts (hadamard w a.residual) (hadamard h a.residual) γ B) :
    a.Partition ∧ a.Accurate w h γ B := by
  refine ⟨ha.1, ?_, ?_, hc⟩
  · have hp := ha.2.1
    simp only [pairing, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum] at hp
    change (1 + γ) * pairing w a.plus ≤ pairing h a.plus
    dsimp [pairing]
    linarith
  · have hm := ha.2.2
    simp only [pairing, sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum] at hm
    change pairing h a.minus ≤ (1 - γ) * pairing w a.minus
    dsimp [pairing]
    linarith

lemma AggregateInvariant.accurate_of_zero {n : ℕ} {γ B : ℝ} {w h : Weights n}
    {a : Aggregate n} (ha : AggregateInvariant γ w h a) (hr : a.residual = 0) (hB : 0 ≤ B) :
    a.Partition ∧ a.Accurate w h γ B := by
  apply ha.accurate
  intro S
  simpa [hr, hadamard, cut, pairing] using hB

lemma measurableSet_aggregate_accurate {n : ℕ} (w h : Weights n) (γ B : ℝ) :
    MeasurableSet {a : Aggregate n | a.Partition ∧ a.Accurate w h γ B} := by
  have hp : MeasurableSet {a : Aggregate n | a.Partition} := by
    unfold Aggregate.Partition
    simp only [Set.setOf_and, Set.setOf_forall]
    refine (measurableSet_isMask measurable_aggregate_plus).inter
      ((measurableSet_isMask measurable_aggregate_minus).inter
        ((measurableSet_isMask measurable_aggregate_residual).inter ?_))
    apply MeasurableSet.iInter
    intro e
    apply measurableSet_eq_fun <;> fun_prop
  have hplus : MeasurableSet {a : Aggregate n |
      (1 + γ) * pairing w a.plus ≤ pairing h a.plus} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hminus : MeasurableSet {a : Aggregate n |
      pairing h a.minus ≤ (1 - γ) * pairing w a.minus} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hcuts : MeasurableSet {a : Aggregate n |
      AllCuts (hadamard w a.residual) (hadamard h a.residual) γ B} := by
    unfold AllCuts
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro S
    unfold cut hadamard
    apply measurableSet_le <;> fun_prop
  exact hp.inter (hplus.inter (hminus.inter hcuts))

def oracleUtilityError (o : OracleConfig) : ℝ :=
  o.K * (o.beta1 / 2) + (1 - 3 / 8192 : ℝ) ^ o.K

lemma oracleUtilityError_nonneg {n : ℕ} {o : OracleConfig} (ho : OracleUtilityBounds n o) :
    0 ≤ oracleUtilityError o := by
  have := ho.beta_pos
  unfold oracleUtilityError
  positivity

/-- The induction tracks active coordinates, so exhaustion of the fuel is harmless. -/
theorem aggregateLoop_utility {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OracleUtilityBounds n o) (hl : 0 < o.lam) {U γ : ℝ}
    (hU : 0 ≤ U) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (w h : Weights n)
    (hw : Bounded U w) (hh : Nonnegative h) (t : ℕ) (a : Aggregate n)
    (ha : AggregateInvariant γ w h a) (hcard : (activeEdges a.residual).card ≤ t) :
    aggregateLoop o γ w h t a {b | ¬(b.Partition ∧ b.Accurate w h γ
      (16 * (o.tau1 + o.lam * n * Real.log n + n * U)))} ≤
      ENNReal.ofReal (2 * t * oracleUtilityError o) := by
  let B := 16 * (o.tau1 + o.lam * n * Real.log n + n * U)
  let P := fun b : Aggregate n => b.Partition ∧ b.Accurate w h γ B
  have hP : MeasurableSet {b | P b} := measurableSet_aggregate_accurate w h γ B
  have hbad : MeasurableSet {b | ¬P b} := hP.compl
  have hτ := ho.tau_pos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd := oracleUtilityError_nonneg ho
  change aggregateLoop o γ w h t a {b | ¬P b} ≤ _
  induction t generalizing a with
  | zero =>
    have hz := activeEdges_zero ha.1.2.2.1 (Nat.eq_zero_of_le_zero hcard)
    have hp : P a := ha.accurate_of_zero hz hB
    simp [aggregateLoop, Measure.dirac_apply' _ hbad, hp]
  | succ t ih =>
    rw [aggregateLoop_succ_eq]
    split_ifs with hz
    · have hp : P a := ha.accurate_of_zero hz hB
      simp [Measure.dirac_apply' _ hbad, hp]
    · let vp : Weights n := fun e => h e - (1 + γ) * w e
      let vm : Weights n := fun e => (1 - γ) * w e - h e
      let μp := findWitness o (plusDiscrepancy γ w h a.residual) a.residual
      let μm := findWitness o (minusDiscrepancy γ w h a.residual) a.residual
      let fm := fun gm : Option (Weights n) => gm.elim (Measure.dirac a)
        (fun g => aggregateLoop o γ w h t (aggregateMinusStep a g))
      let fp := fun gp : Option (Weights n) => gp.elim (μm.bind fm)
        (fun g => aggregateLoop o γ w h t (aggregatePlusStep a g))
      have hfm : Measurable fm := measurable_option_elim _
        (measurable_aggregateLoop hn o hl ho.eps_pos γ t measurable_const measurable_const
          (measurable_aggregateMinusStep a))
      have hfp : Measurable fp := measurable_option_elim _
        (measurable_aggregateLoop hn o hl ho.eps_pos γ t measurable_const measurable_const
          (measurable_aggregatePlusStep a))
      letI : IsProbabilityMeasure μp := findWitness_probability o ho.eps_pos _ _
      letI : IsProbabilityMeasure μm := findWitness_probability o ho.eps_pos _ _
      letI (gm : Option (Weights n)) : IsProbabilityMeasure (fm gm) := by
        cases gm with
        | none => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac a))
        | some g => exact aggregateLoop_probability hn o hl ho.eps_pos γ w h t _
      letI (gp : Option (Weights n)) : IsProbabilityMeasure (fp gp) := by
        cases gp with
        | none => exact probability_bind μm fm hfm
        | some g => exact aggregateLoop_probability hn o hl ho.eps_pos γ w h t _
      have hpbad := findWitness_utility hn o ho a.residual vp ha.1.2.2.1 hz
      have hmbad := findWitness_utility hn o ho a.residual vm ha.1.2.2.1 hz
      have hstep : μp.bind fp {b | ¬P b} ≤
          ENNReal.ofReal (oracleUtilityError o + (oracleUtilityError o + 2 * t * oracleUtilityError o)) := by
        apply measure_bind_le_of_good (μ := μp) hfp (measurableSet_witnessUseful o a.residual vp) hbad
          hd (by positivity) hpbad
        intro gp hgp
        cases gp with
        | some g =>
          change Retires a.residual g ∧ 0 ≤ pairing vp g at hgp
          have hc : (activeEdges (a.residual - g)).card ≤ t := by
            have := hgp.1.active_card_lt
            omega
          exact (ih _ (ha.plus_step hgp.1 hgp.2) hc).trans
            (ENNReal.ofReal_le_ofReal (by linarith))
        | none =>
          change optimum o.lam (plusDiscrepancy γ w h a.residual) < 4 * o.tau1 at hgp
          apply measure_bind_le_of_good (μ := μm) hfm (measurableSet_witnessUseful o a.residual vm) hbad
            hd (by positivity) hmbad
          intro gm hgm
          cases gm with
          | some g =>
            change Retires a.residual g ∧ 0 ≤ pairing vm g at hgm
            have hc : (activeEdges (a.residual - g)).card ≤ t := by
              have := hgm.1.active_card_lt
              omega
            exact ih _ (ha.minus_step hgm.1 hgm.2) hc
          | none =>
            change optimum o.lam (minusDiscrepancy γ w h a.residual) < 4 * o.tau1 at hgm
            have hc := residual_cut_certificate hn hU hγ hγ1 ho.lam_nonneg hτ.le hw hh
              ha.1.2.2.1 hgp.le hgm.le
            have hp : P a := ha.accurate hc
            change Measure.dirac a {b | ¬P b} ≤ _
            simp [Measure.dirac_apply' _ hbad, hp]
      convert hstep using 1
      push_cast
      congr 1
      ring

end DPCut
