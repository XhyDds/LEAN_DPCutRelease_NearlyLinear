import DPCut.AggregateTranscript

/-! Identification of the padded oracle transcript with the original aggregate loop. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

lemma pairsAlive_prefix {n t : ℕ} (h : WitnessHistory n) (hlen : h.length = t)
    (y : Option (Weights n)) (ha : pairsAlive (t + 1) (h ++ [y])) : pairsAlive t h := by
  intro j hj
  have hi : 2 * j < h.length := by omega
  have hi' : 2 * j + 1 < h.length := by omega
  simpa only [List.getElem?_append_left hi, List.getElem?_append_left hi'] using
    ha j (by omega)

lemma aggregateKernel_dead {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (t : ℕ) (h : WitnessHistory n) (ha : ¬pairsAlive t h) :
    witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side t h =
      Measure.dirac none := by
  have he : ¬(aggregateWitnessSchedule γ w w' h0).enabled t h := fun hh => ha hh.1.1
  simp only [witnessActualKernel, Kernel.coe_mk, if_neg he]

lemma aggregateContinuation_dead {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (t m : ℕ) (h : WitnessHistory n) (hlen : h.length = t) (ha : ¬pairsAlive t h) :
    sequentialContinuation (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
      witnessAggregate t m h = Measure.dirac (witnessAggregate h) := by
  induction m generalizing t h with
  | zero => rfl
  | succ m ih =>
    have hm : Measurable (fun y : Option (Weights n) => sequentialContinuation
        (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
        witnessAggregate (t + 1) m (h ++ [y])) :=
      (measurable_sequentialContinuation _ measurable_witnessAggregate
        (t + 1) m).comp ((measurable_list_append_one none).comp measurable_prodMk_left)
    rw [sequentialContinuation, aggregateKernel_dead hn o ho γ w w' h0 side t h ha,
      Measure.dirac_bind hm]
    rw [ih (t + 1) (h ++ [none]) (by simp [hlen])
      (fun hh => ha (pairsAlive_prefix h hlen none hh)), witnessAggregate_append_none]

lemma aggregateKernel_even {n l : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (h : WitnessHistory n) (ha : pairsAlive (2 * l) h) (hr : IsMask (witnessResidual h)) :
    witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side (2 * l) h =
      findWitness o (plusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h))
        (witnessResidual h) := by
  have he : (aggregateWitnessSchedule γ w w' h0).enabled (2 * l) h :=
    ⟨(aggregateCallActive_even h).mpr ha, hr⟩
  simp only [witnessActualKernel, Kernel.coe_mk, if_pos he]
  simp [aggregateWitnessSchedule]

lemma aggregateKernel_odd_some {n l : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (h : WitnessHistory n) (hlen : h.length = 2 * l) (g : Weights n) :
    witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side (2 * l + 1)
      (h ++ [some g]) = Measure.dirac none := by
  have he : ¬(aggregateWitnessSchedule γ w w' h0).enabled (2 * l + 1) (h ++ [some g]) := by
    intro hh
    exact Option.noConfusion ((aggregateCallActive_odd h hlen (some g)).mp hh.1).2
  simp only [witnessActualKernel, Kernel.coe_mk, if_neg he]

lemma aggregateKernel_odd_none {n l : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (h : WitnessHistory n) (hlen : h.length = 2 * l) (ha : pairsAlive (2 * l) h)
    (hr : IsMask (witnessResidual h)) :
    witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side (2 * l + 1)
      (h ++ [none]) = findWitness o
        (minusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h)) (witnessResidual h) := by
  have hr' : witnessResidual (h ++ [none]) = witnessResidual h := by simp [witnessResidual_append]
  have he : (aggregateWitnessSchedule γ w w' h0).enabled (2 * l + 1) (h ++ [none]) :=
    ⟨(aggregateCallActive_odd h hlen none).mpr ⟨ha, rfl⟩, by rwa [hr']⟩
  simp only [witnessActualKernel, Kernel.coe_mk, if_pos he]
  simp [aggregateWitnessSchedule, hr']

lemma aggregateKernel_zero {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (t : ℕ) (h : WitnessHistory n) (hr : witnessResidual h = 0) :
    witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side t h =
      Measure.dirac none := by
  simp [witnessActualKernel, findWitness, hr]

lemma aggregateContinuation_zero {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (t m : ℕ) (h : WitnessHistory n) (hr : witnessResidual h = 0) :
    sequentialContinuation (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
      witnessAggregate t m h = Measure.dirac (witnessAggregate h) := by
  induction m generalizing t h with
  | zero => rfl
  | succ m ih =>
    have hm : Measurable (fun y : Option (Weights n) => sequentialContinuation
        (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
        witnessAggregate (t + 1) m (h ++ [y])) :=
      (measurable_sequentialContinuation _ measurable_witnessAggregate
        (t + 1) m).comp ((measurable_list_append_one none).comp measurable_prodMk_left)
    rw [sequentialContinuation, aggregateKernel_zero hn o ho γ w w' h0 side t h hr,
      Measure.dirac_bind hm]
    rw [ih (t + 1) (h ++ [none]) (by simpa [witnessResidual_append] using hr),
      witnessAggregate_append_none]

theorem aggregateContinuation_eq_loop {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool)
    (m l : ℕ) (h : WitnessHistory n) (hlen : h.length = 2 * l)
    (ha : pairsAlive (2 * l) h) (hr : IsMask (witnessResidual h)) :
    sequentialContinuation (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
      witnessAggregate (2 * l) (2 * m) h =
      aggregateLoop o γ (if side then w' else w) h0 m (witnessAggregate h) := by
  induction m generalizing l h with
  | zero => rfl
  | succ m ih =>
    by_cases hr0 : witnessResidual h = 0
    · rw [aggregateContinuation_zero hn o ho γ w w' h0 side _ _ h hr0, aggregateLoop]
      simp [show (witnessAggregate h).residual = 0 from hr0]
    have hcount : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hcount, sequentialContinuation, aggregateKernel_even hn o ho γ w w' h0 side h ha hr,
      aggregateLoop, if_neg (show (witnessAggregate h).residual ≠ 0 from hr0)]
    apply Measure.bind_congr_right
    filter_upwards [findWitness_supported o ho.eps_pos
      (plusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h)) (witnessResidual h) hr]
      with gp hgp
    cases gp with
    | none =>
      dsimp only
      rw [sequentialContinuation, aggregateKernel_odd_none hn o ho γ w w' h0 side h hlen ha hr]
      apply Measure.bind_congr_right
      filter_upwards [findWitness_supported o ho.eps_pos
        (minusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h)) (witnessResidual h) hr]
        with gm hgm
      cases gm with
      | none =>
        have hd : ¬pairsAlive (2 * (l + 1)) (h ++ [none, none]) := by
          simp [pairsAlive_two h hlen]
        have hh := aggregateContinuation_dead hn o ho γ w w' h0 side (2 * (l + 1)) (2 * m)
          (h ++ [none, none]) (by simp [hlen]; omega) hd
        have he : witnessAggregate (h ++ [none, none]) = witnessAggregate h := by
          simpa only [List.append_assoc, List.singleton_append] using
            (witnessAggregate_append_none (h ++ [none])).trans (witnessAggregate_append_none h)
        simpa only [show 2 * (l + 1) = 2 * l + 1 + 1 by omega,
          List.append_assoc, List.singleton_append, he] using hh
      | some g =>
        have hr' : IsMask (witnessResidual (h ++ [none, some g])) := by
          have he : witnessResidual (h ++ [none, some g]) = witnessResidual h - g := by
            rw [show h ++ [none, some g] = (h ++ [none]) ++ [some g] by simp,
              witnessResidual_append, witnessResidual_append]
            simp
          rw [he]
          exact witness_supported_residual _ _ _ hr hgm
        have hh := ih (l + 1) (h ++ [none, some g]) (by simp [hlen]; omega)
          ((pairsAlive_two h hlen none (some g)).mpr ⟨ha, by simp⟩) hr'
        rw [witnessAggregate_append_two h hlen] at hh
        simpa only [show 2 * (l + 1) = 2 * l + 1 + 1 by omega,
          List.append_assoc, List.singleton_append, Option.getD_none, Option.getD_some,
          add_zero, sub_zero] using hh
    | some g =>
      dsimp only
      rw [sequentialContinuation, aggregateKernel_odd_some hn o ho γ w w' h0 side h hlen g]
      have hm : Measurable (fun y : Option (Weights n) => sequentialContinuation
          (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
          witnessAggregate (2 * l + 1 + 1) (2 * m) ((h ++ [some g]) ++ [y])) :=
        (measurable_sequentialContinuation _ measurable_witnessAggregate _ _).comp
          ((measurable_list_append_one none).comp measurable_prodMk_left)
      rw [Measure.dirac_bind hm]
      have hr' : IsMask (witnessResidual (h ++ [some g, none])) := by
        have he : witnessResidual (h ++ [some g, none]) = witnessResidual h - g := by
          rw [show h ++ [some g, none] = (h ++ [some g]) ++ [none] by simp,
            witnessResidual_append, witnessResidual_append]
          simp
        rw [he]
        exact witness_supported_residual _ _ _ hr hgp
      have hh := ih (l + 1) (h ++ [some g, none]) (by simp [hlen]; omega)
        ((pairsAlive_two h hlen (some g) none).mpr ⟨ha, by simp⟩) hr'
      rw [witnessAggregate_append_two h hlen] at hh
      simpa only [show 2 * (l + 1) = 2 * l + 1 + 1 by omega,
        List.append_assoc, List.singleton_append, Option.getD_none, Option.getD_some,
        add_zero, sub_zero] using hh

theorem aggregateLaw_eq_transcript {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w w' h0 : Weights n) (side : Bool) :
    aggregateLaw o γ (if side then w' else w) h0 =
      (sequentialLaw (witnessActualKernel hn o ho (aggregateWitnessSchedule γ w w' h0) side)
        (2 * Fintype.card (Edge n))).map witnessAggregate := by
  rw [sequentialLaw_map_continuation _ measurable_witnessAggregate]
  have hh := aggregateContinuation_eq_loop hn o ho γ w w' h0 side
    (Fintype.card (Edge n)) 0 [] rfl (by simp [pairsAlive])
    (by simp [witnessResidual_nil, IsMask, Bounded])
  simpa only [Nat.mul_zero, witnessAggregate_nil, aggregateLaw] using hh.symm

theorem aggregateLaw_probability {n : ℕ} (hn : 2 ≤ n) (o : OracleConfig)
    (ho : OraclePrivacyBounds n o) (γ : ℝ) (w h : Weights n) :
    IsProbabilityMeasure (aggregateLaw o γ w h) := by
  have he := aggregateLaw_eq_transcript hn o ho γ w w h false
  simp only [Bool.false_eq_true, if_false] at he
  rw [he]
  exact Measure.isProbabilityMeasure_map measurable_witnessAggregate.aemeasurable

end DPCut
