import DPCut.WitnessTranscript

/-! Success-charged privacy for adaptive calls to the concrete witness oracle. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

structure WitnessSchedule (n : ℕ) where
  active : ℕ → WitnessHistory n → Prop
  active_measurable : ∀ t, MeasurableSet {h | active t h}
  discrepancy : Bool → ℕ → WitnessHistory n → Weights n
  discrepancy_measurable : ∀ side t, Measurable (discrepancy side t)

def WitnessSchedule.enabled {n : ℕ} (s : WitnessSchedule n) (t : ℕ) (h : WitnessHistory n) : Prop :=
  s.active t h ∧ IsMask (witnessResidual h)

lemma WitnessSchedule.enabled_measurable {n : ℕ} (s : WitnessSchedule n) (t : ℕ) :
    MeasurableSet {h | s.enabled t h} :=
  (s.active_measurable t).inter (measurableSet_isMask measurable_witnessResidual)

def witnessActualKernel {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (ho : OraclePrivacyBounds n o)
    (s : WitnessSchedule n) (side : Bool) (t : ℕ) : Kernel (WitnessHistory n) (Option (Weights n)) where
  toFun h := if s.enabled t h then
    findWitness o (s.discrepancy side t h) (witnessResidual h) else Measure.dirac none
  measurable' := by
    have hm : Measurable (fun h => findWitness o (s.discrepancy side t h) (witnessResidual h)) := by
      change Measurable ((fun p : Weights n × Weights n => findWitness o p.1 p.2) ∘
        (fun h => (s.discrepancy side t h, witnessResidual h)))
      exact (measurable_findWitness hn o (by linarith [ho.lam_lower]) ho.eps_pos).comp
        ((s.discrepancy_measurable side t).prodMk measurable_witnessResidual)
    exact Measurable.ite (s.enabled_measurable t) hm measurable_const

def witnessAuxKernel {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig) (ho : OraclePrivacyBounds n o)
    (s : WitnessSchedule n) (ζ : Weights n) (side : Bool) (t : ℕ) :
    Kernel (WitnessHistory n) (Option (Weights n)) where
  toFun h := if s.enabled t h then auxiliaryFindWitness o
    (s.discrepancy side t h) (s.discrepancy (!side) t h) ζ (witnessResidual h)
    else Measure.dirac none
  measurable' := Measurable.ite (s.enabled_measurable t)
    (measurable_auxiliaryFindWitness hn o (by linarith [ho.lam_lower]) ho.eps_pos
      (s.discrepancy_measurable side t) (s.discrepancy_measurable (!side) t)
      measurable_const measurable_witnessResidual) measurable_const

def witnessCharge {n : ℕ} (o : OracleConfig) (s : WitnessSchedule n) (ζ : Weights n)
    (t : ℕ) (h : WitnessHistory n) : ℝ :=
  if s.enabled t h then 10 * o.K * o.eps1 * oracleSensitivity ζ (witnessResidual h)
    (optimizer o.lam (s.discrepancy false t h)) (optimizer o.lam (s.discrepancy true t h)) else 0

lemma measurable_witnessCharge {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (ζ : Weights n) (t : ℕ) :
    Measurable (witnessCharge o s ζ t) := by
  have hl : 0 < o.lam := by linarith [ho.lam_lower]
  exact Measurable.ite (s.enabled_measurable t)
    ((measurable_oracleSensitivity
      ((measurable_optimizer hn hl).comp (s.discrepancy_measurable false t))
      ((measurable_optimizer hn hl).comp (s.discrepancy_measurable true t))
      measurable_const measurable_witnessResidual).const_mul _) measurable_const

instance witnessActualKernel_markov {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (side : Bool) (t : ℕ) :
    IsMarkovKernel (witnessActualKernel hn o ho s side t) := by
  constructor
  intro h
  change IsProbabilityMeasure (if s.enabled t h then _ else _)
  split_ifs
  · exact findWitness_probability o ho.eps_pos _ _
  · infer_instance

def WitnessSchedule.Sensitive {n : ℕ} (s : WitnessSchedule n) (ζ : Weights n) : Prop :=
  ∀ t h, IsMask (witnessResidual h) → ∀ e,
    |s.discrepancy true t h e - s.discrepancy false t h e| ≤ 2 * |ζ e| * witnessResidual h e

lemma witnessAuxKernel_markov {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (ζ : Weights n)
    (hζ : l1 ζ ≤ 1) (hs : s.Sensitive ζ) (side : Bool) (t : ℕ) :
    IsMarkovKernel (witnessAuxKernel hn o ho s ζ side t) := by
  constructor
  intro h
  change IsProbabilityMeasure (if s.enabled t h then _ else _)
  split_ifs with ha
  · have hp := findWitness_auxiliary hn o ho (s.discrepancy false t h)
      (s.discrepancy true t h) ζ (witnessResidual h) ha.2 hζ (hs t h ha.2)
    cases side
    · exact hp.1
    · exact hp.2.1
  · infer_instance

lemma witnessKernels_local {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (ζ : Weights n)
    (hζ : l1 ζ ≤ 1) (hs : s.Sensitive ζ) (t : ℕ) (h : WitnessHistory n) :
    0 ≤ witnessCharge o s ζ t h ∧ witnessCharge o s ζ t h ≤ 10 * o.K * o.eps1 ∧
    witnessAuxKernel hn o ho s ζ false t h ≪ witnessActualKernel hn o ho s false t h ∧
    witnessAuxKernel hn o ho s ζ true t h ≪ witnessActualKernel hn o ho s true t h ∧
    TVClose (witnessActualKernel hn o ho s false t h) (witnessAuxKernel hn o ho s ζ false t h)
      (2 * o.K * o.delta1) ∧
    TVClose (witnessActualKernel hn o ho s true t h) (witnessAuxKernel hn o ho s ζ true t h)
      (2 * o.K * o.delta1) ∧
    Indistinguishable (witnessAuxKernel hn o ho s ζ false t h)
      (witnessAuxKernel hn o ho s ζ true t h) (witnessCharge o s ζ t h) 0 := by
  have he := ho.eps_pos
  have hd := ho.delta_pos
  by_cases ha : s.enabled t h
  · have hp := findWitness_auxiliary hn o ho (s.discrepancy false t h)
      (s.discrepancy true t h) ζ (witnessResidual h) ha.2 hζ (hs t h ha.2)
    have hW := oracleSensitivity_bounds hn ha.2 ζ
      (optimizer_isOptimizer hn o.lam (s.discrepancy false t h)).1
      (optimizer_isOptimizer hn o.lam (s.discrepancy true t h)).1
    simp only [witnessCharge, witnessActualKernel, witnessAuxKernel, Kernel.coe_mk,
      if_pos ha, Bool.not_false, Bool.not_true]
    exact ⟨mul_nonneg (by positivity) hW.1,
      mul_le_of_le_one_right (by positivity) (hW.2.trans hζ), hp.2.2⟩
  · simp only [witnessCharge, witnessActualKernel, witnessAuxKernel, Kernel.coe_mk, if_neg ha]
    exact ⟨le_rfl, by positivity, Measure.AbsolutelyContinuous.rfl,
      Measure.AbsolutelyContinuous.rfl, TVClose.refl _ (by positivity),
      TVClose.refl _ (by positivity), Indistinguishable.of_eq rfl le_rfl le_rfl⟩

lemma witnessAuxKernel_step {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (ζ : Weights n)
    (side : Bool) (t : ℕ) (h : WitnessHistory n) (hr : IsMask (witnessResidual h)) :
    ∀ᵐ y ∂witnessAuxKernel hn o ho s ζ side t h,
      IsMask (witnessResidual h - y.getD 0) ∧
      stepCharge none (witnessCharge o s ζ t h) y ≤
        (80 * o.K * o.eps1) * pairing (fun e => |ζ e|) (y.getD 0) := by
  have he := ho.eps_pos
  by_cases ha : s.enabled t h
  · change ∀ᵐ y ∂(if s.enabled t h then _ else _), _
    rw [if_pos ha]
    have hsup := auxiliaryFindWitness_supported o (s.discrepancy side t h)
      (s.discrepancy (!side) t h) ζ (witnessResidual h) hr
    filter_upwards [hsup] with y hy
    refine ⟨witnessSupported_none_residual _ _ hr y hy, ?_⟩
    have hc := witnessSupported_stepCharge o he.le ζ (witnessResidual h)
      (queryMax (optimizer o.lam (s.discrepancy side t h))
        (optimizer o.lam (s.discrepancy (!side) t h))) y hy
    cases side <;> simpa only [witnessCharge, if_pos ha, oracleSensitivity,
      queryMax, Bool.not_false, Bool.not_true, max_comm] using hc
  · change ∀ᵐ y ∂(if s.enabled t h then _ else _), _
    rw [if_neg ha]
    simpa [ae_dirac_eq, stepCharge, pairing] using hr

theorem adaptive_witness_privacy {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (s : WitnessSchedule n) (ζ : Weights n)
    (hζ : l1 ζ ≤ 1) (hs : s.Sensitive ζ) (k : ℕ) {δ : ℝ}
    (hsmall : 10 * o.K * o.eps1 < 1 / 10) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let ε := 320 * o.K * o.eps1 + 40 * o.K * o.eps1 * Real.log (1 / δ)
    Indistinguishable (sequentialLaw (witnessActualKernel hn o ho s false) k)
      (sequentialLaw (witnessActualKernel hn o ho s true) k)
      ε (δ + (1 + Real.exp ε) * k * (2 * o.K * o.delta1)) := by
  have he := ho.eps_pos
  have hd := ho.delta_pos
  letI (side : Bool) (t : ℕ) := witnessAuxKernel_markov hn o ho s ζ hζ hs side t
  have hb (side : Bool) : ∀ᵐ h ∂sequentialLaw (witnessAuxKernel hn o ho s ζ side) k,
      successCharge none (witnessCharge o s ζ) h ≤ 80 * o.K * o.eps1 := by
    have hh := witnessTranscript_budget (witnessAuxKernel hn o ho s ζ side)
      (witnessCharge o s ζ) (measurable_witnessCharge hn o ho s ζ) ζ
      (by positivity : 0 ≤ 80 * o.K * o.eps1) (witnessAuxKernel_step hn o ho s ζ side) k
    exact hh.mono fun _ h => h.2.trans (mul_le_of_le_one_right (by positivity) hζ)
  have hp := lemma16 (Option (Weights n)) none
    (witnessActualKernel hn o ho s false) (witnessActualKernel hn o ho s true)
    (witnessAuxKernel hn o ho s ζ false) (witnessAuxKernel hn o ho s ζ true) k
    (witnessCharge o s ζ) (10 * o.K * o.eps1) (80 * o.K * o.eps1) (2 * o.K * o.delta1) δ
    (fun t => ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩)
    (measurable_witnessCharge hn o ho s ζ) (by positivity) hsmall (by positivity)
    (by positivity) hδ hδ1 (fun t _ h _ => witnessKernels_local hn o ho s ζ hζ hs t h)
    (hb false) (hb true)
  have heq : 4 * (80 * o.K * o.eps1) + 4 * (10 * o.K * o.eps1) * Real.log (1 / δ) =
      320 * o.K * o.eps1 + 40 * o.K * o.eps1 * Real.log (1 / δ) := by ring
  dsimp only at hp ⊢
  rw [heq] at hp
  exact hp

end DPCut
