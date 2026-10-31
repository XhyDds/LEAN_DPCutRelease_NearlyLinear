import DPCut.SequentialContinuation

/-! The two-call schedule and deterministic output of AggregateWitnesses. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace DPCut
attribute [local instance] Classical.propDecidable

def pairsAlive {n : ℕ} (t : ℕ) (h : WitnessHistory n) : Prop :=
  ∀ j < t / 2, h[2 * j]?.getD none ≠ none ∨ h[2 * j + 1]?.getD none ≠ none

def aggregateCallActive {n : ℕ} (t : ℕ) (h : WitnessHistory n) : Prop :=
  pairsAlive t h ∧ (t % 2 = 0 ∨ h[t - 1]?.getD none = none)

lemma measurableSet_pairsAlive {n : ℕ} (t : ℕ) :
    MeasurableSet {h : WitnessHistory n | pairsAlive t h} := by
  unfold pairsAlive
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  exact (((measurable_list_getD none (2 * j)) measurableSet_option_none).compl).union
    (((measurable_list_getD none (2 * j + 1)) measurableSet_option_none).compl)

lemma measurableSet_aggregateCallActive {n : ℕ} (t : ℕ) :
    MeasurableSet {h : WitnessHistory n | aggregateCallActive t h} :=
  (measurableSet_pairsAlive t).inter ((MeasurableSet.const _).union
    ((measurable_list_getD none (t - 1)) measurableSet_option_none))

lemma pairsAlive_one {n l : ℕ} (h : WitnessHistory n) (hlen : h.length = 2 * l)
    (y : Option (Weights n)) : pairsAlive (2 * l + 1) (h ++ [y]) ↔ pairsAlive (2 * l) h := by
  simp only [pairsAlive, show (2 * l + 1) / 2 = l by omega, show 2 * l / 2 = l by omega]
  constructor <;> intro hh j hj
  · have hi : 2 * j < h.length := by omega
    have hi' : 2 * j + 1 < h.length := by omega
    simpa only [List.getElem?_append_left hi, List.getElem?_append_left hi'] using hh j hj
  · have hi : 2 * j < h.length := by omega
    have hi' : 2 * j + 1 < h.length := by omega
    simpa only [List.getElem?_append_left hi, List.getElem?_append_left hi'] using hh j hj

lemma pairsAlive_two {n l : ℕ} (h : WitnessHistory n) (hlen : h.length = 2 * l)
    (y z : Option (Weights n)) : pairsAlive (2 * (l + 1)) (h ++ [y, z]) ↔
      pairsAlive (2 * l) h ∧ (y ≠ none ∨ z ≠ none) := by
  have hlast : (h ++ [y, z])[2 * l]?.getD none = y ∧
      (h ++ [y, z])[2 * l + 1]?.getD none = z := by
    simp [hlen]
  simp only [pairsAlive, show 2 * (l + 1) / 2 = l + 1 by omega, show 2 * l / 2 = l by omega]
  constructor
  · intro hh
    refine ⟨?_, ?_⟩
    · intro j hj
      have hi : 2 * j < h.length := by omega
      have hi' : 2 * j + 1 < h.length := by omega
      simpa only [List.getElem?_append_left hi, List.getElem?_append_left hi'] using
        hh j (by omega)
    · simpa only [hlast.1, hlast.2] using hh l (by omega)
  · rintro ⟨hh, hy⟩ j hj
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
    · have hi : 2 * j < h.length := by omega
      have hi' : 2 * j + 1 < h.length := by omega
      simpa only [List.getElem?_append_left hi, List.getElem?_append_left hi'] using hh j hj
    · simpa only [hlast.1, hlast.2] using hy

lemma aggregateCallActive_even {n l : ℕ} (h : WitnessHistory n) :
    aggregateCallActive (2 * l) h ↔ pairsAlive (2 * l) h := by
  simp [aggregateCallActive]

lemma aggregateCallActive_odd {n l : ℕ} (h : WitnessHistory n) (hlen : h.length = 2 * l)
    (y : Option (Weights n)) : aggregateCallActive (2 * l + 1) (h ++ [y]) ↔
      pairsAlive (2 * l) h ∧ y = none := by
  simp only [aggregateCallActive, pairsAlive_one h hlen]
  simp [hlen]

def witnessAggregate {n : ℕ} (h : WitnessHistory n) : Aggregate n where
  plus e := transcriptSum none (fun t _ (y : Option (Weights n)) =>
    if t % 2 = 0 then y.getD 0 e else 0) h
  minus e := transcriptSum none (fun t _ (y : Option (Weights n)) =>
    if t % 2 = 0 then 0 else y.getD 0 e) h
  residual := witnessResidual h

lemma measurable_aggregate_mk {A : Type*} [MeasurableSpace A] {n : ℕ}
    {p m r : A → Weights n} (hp : Measurable p) (hm : Measurable m) (hr : Measurable r) :
    Measurable (fun a => (⟨p a, m a, r a⟩ : Aggregate n)) := by
  intro s hs
  obtain ⟨u, hu, rfl⟩ := hs
  exact (hp.prodMk (hm.prodMk hr)) hu

lemma measurable_witnessAggregate {n : ℕ} : Measurable (witnessAggregate (n := n)) := by
  apply measurable_aggregate_mk
  · apply measurable_pi_lambda
    intro e
    apply measurable_transcriptSum
    intro t
    split_ifs
    · exact (measurable_pi_apply e).comp ((measurable_option_getD (0 : Weights n)).comp measurable_snd)
    · exact measurable_const
  · apply measurable_pi_lambda
    intro e
    apply measurable_transcriptSum
    intro t
    split_ifs
    · exact measurable_const
    · exact (measurable_pi_apply e).comp ((measurable_option_getD (0 : Weights n)).comp measurable_snd)
  · exact measurable_witnessResidual

lemma witnessAggregate_nil (n : ℕ) : witnessAggregate ([] : WitnessHistory n) = ⟨0, 0, 1⟩ := by
  simp [witnessAggregate, transcriptSum, witnessResidual_nil]
  rfl

lemma witnessAggregate_append_none {n : ℕ} (h : WitnessHistory n) :
    witnessAggregate (h ++ [none]) = witnessAggregate h := by
  simp [witnessAggregate, transcriptSum_append, witnessResidual_append]

lemma witnessAggregate_append_two {n l : ℕ} (h : WitnessHistory n) (hlen : h.length = 2 * l)
    (y z : Option (Weights n)) : witnessAggregate (h ++ [y, z]) =
      ⟨(witnessAggregate h).plus + y.getD 0,
       (witnessAggregate h).minus + z.getD 0, witnessResidual h - y.getD 0 - z.getD 0⟩ := by
  have he : h ++ [y, z] = (h ++ [y]) ++ [z] := by simp
  rw [he]
  change Aggregate.mk _ _ _ = Aggregate.mk _ _ _
  congr 1
  · funext e
    dsimp only [witnessAggregate, Pi.add_apply]
    rw [transcriptSum_append, transcriptSum_append]
    simp [hlen]
  · funext e
    dsimp only [witnessAggregate, Pi.add_apply]
    rw [transcriptSum_append, transcriptSum_append]
    simp [hlen]
  · exact (witnessResidual_append (h ++ [y]) z).trans
      (congrArg (fun r => r - z.getD 0) (witnessResidual_append h y))

def aggregateWitnessSchedule {n : ℕ} (γ : ℝ) (w w' h0 : Weights n) : WitnessSchedule n where
  active := aggregateCallActive
  active_measurable := measurableSet_aggregateCallActive
  discrepancy side t h :=
    if t % 2 = 0 then plusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h)
    else minusDiscrepancy γ (if side then w' else w) h0 (witnessResidual h)
  discrepancy_measurable side t := by
    split_ifs <;> apply measurable_pi_lambda <;> intro e
    all_goals exact ((measurable_pi_apply e).comp measurable_witnessResidual).mul_const _

lemma aggregateWitnessSchedule_sensitive {n : ℕ} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (w w' h0 : Weights n) : (aggregateWitnessSchedule γ w w' h0).Sensitive (w - w') := by
  intro t h hr e
  dsimp [aggregateWitnessSchedule]
  split_ifs
  · exact masked_plus_discrepancy hγ hγ1 w w' h0 (witnessResidual h) hr e
  · exact masked_minus_discrepancy hγ hγ1 w w' h0 (witnessResidual h) hr e

end DPCut
