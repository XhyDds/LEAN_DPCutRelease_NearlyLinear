import DPCut.UtilityCalibration

/-!
Lemma 20 (`lem:gradient_estimation`): utility of AggregateWitnesses, with the
same oracle as Lemma 17 and explicit certificate constant 16.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

/-- **Lemma 20**, with all three conclusions and the partition invariant. -/
theorem lemma20 : AggregateUtilityStatement utilityConstants := by
  intro n hn U ε δ β γ hU hε hε1 hδ hδ1 hβ hβ1 hγ hγ1 w h hw hh
  let o := oracleConfig n utilityConstants ε δ β
  have ho : OracleUtilityBounds n o := public_oracle_utility_bounds hn hε hε1 hδ hδ1 hβ hβ1
  have hp : OraclePrivacyBounds n o := public_oracle_privacy_bounds hn hε hε1 hδ hδ1 hβ hβ1
  have hl : 0 < o.lam := by linarith [hp.lam_lower]
  letI := aggregateLoop_probability hn o hl ho.eps_pos γ w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩
  letI : IsProbabilityMeasure (aggregateLaw o γ w h) := inferInstanceAs
    (IsProbabilityMeasure (aggregateLoop o γ w h (Fintype.card (Edge n)) ⟨0, 0, 1⟩))
  have hi : AggregateInvariant γ w h ⟨0, 0, 1⟩ := by
    simp [AggregateInvariant, Aggregate.Partition, IsMask, Bounded, pairing]
  have hc : (activeEdges (1 : Weights n)).card ≤ Fintype.card (Edge n) := Finset.card_le_univ _
  have hb := aggregateLoop_utility hn o ho hl hU hγ.le hγ1.le w h hw hh
    (Fintype.card (Edge n)) ⟨0, 0, 1⟩ hi hc
  have hbudget := public_oracle_utility_budget hn hε hε1 hδ hδ1 hβ hβ1
  change HighProbability (aggregateLaw o γ w h) β (fun a => a.Partition ∧ a.Accurate w h γ
    (16 * (o.tau1 + o.lam * n * Real.log n + n * U)))
  apply highProbability_of_failure (measurableSet_aggregate_accurate w h γ _) hβ.le
  exact hb.trans (ENNReal.ofReal_le_ofReal hbudget)

/-- Aggregate privacy and utility hold with one explicit choice of constants. -/
theorem lemma17_utilityConstants : AggregatePrivacyStatement utilityConstants := by
  exact lemma17

theorem aggregate_privacy_and_utility : utilityConstants.Positive ∧
    AggregatePrivacyStatement utilityConstants ∧ AggregateUtilityStatement utilityConstants :=
  ⟨utilityConstants_positive, lemma17_utilityConstants, lemma20⟩

end DPCut
