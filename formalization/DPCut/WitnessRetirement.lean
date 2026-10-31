import DPCut.FindWitnessSupport

/-! Accepted witnesses retire an active edge; this justifies the aggregate fuel. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def activeEdges {n : ℕ} (r : Weights n) : Finset (Edge n) :=
  Finset.univ.filter (fun e => 0 < r e)

def Retires {n : ℕ} (r g : Weights n) : Prop :=
  (∀ e, 0 ≤ g e ∧ g e ≤ r e) ∧ ∃ e, 0 < r e ∧ g e = r e

lemma measurableSet_retires {n : ℕ} (r : Weights n) : MeasurableSet {g | Retires r g} := by
  unfold Retires
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_exists]
  refine (MeasurableSet.iInter fun e => ?_).inter (MeasurableSet.iUnion fun e => ?_)
  · exact (measurableSet_le measurable_const (measurable_pi_apply e)).inter
      (measurableSet_le (measurable_pi_apply e) measurable_const)
  · exact (MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_pi_apply e) measurable_const)

lemma activeMaximum_attained {n : ℕ} (r g : Weights n) (hp : 0 < activeMaximum r g) :
    ∃ e, 0 < r e ∧ g e = activeMaximum r g := by
  have hm := (show (insert 0 (g '' {e | 0 < r e})).Nonempty from ⟨0, mem_insert _ _⟩).csSup_mem
    ((Set.toFinite _).insert 0)
  change activeMaximum r g ∈ insert 0 (g '' {e | 0 < r e}) at hm
  rcases hm with hzero | ⟨e, he, heq⟩
  · exact False.elim (hp.ne' hzero)
  · exact ⟨e, he, heq⟩

lemma normalizeWitness_retires {n : ℕ} {r g : Weights n} (hr : IsMask r)
    (hg : ∀ e, 0 ≤ g e) (hp : 0 < activeMaximum r g) : Retires r (normalizeWitness r g) := by
  refine ⟨normalizeWitness_bounds hr hg hp, ?_⟩
  obtain ⟨e, he, heq⟩ := activeMaximum_attained r g hp
  exact ⟨e, he, by simp [normalizeWitness, heq, hp.ne']⟩

lemma Retires.residual_mask {n : ℕ} {r g : Weights n} (hg : Retires r g) (hr : IsMask r) :
    IsMask (r - g) := by
  intro e
  have h := hg.1 e
  change 0 ≤ r e - g e ∧ r e - g e ≤ 1
  constructor <;> linarith [(hr e).2]

lemma Retires.active_card_lt {n : ℕ} {r g : Weights n} (hg : Retires r g) :
    (activeEdges (r - g)).card < (activeEdges r).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  have hs : activeEdges (r - g) ⊆ activeEdges r := by
    intro e he
    simp only [activeEdges, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply] at he ⊢
    linarith [(hg.1 e).1]
  refine ⟨hs, ?_⟩
  obtain ⟨e, he, heq⟩ := hg.2
  intro heqset
  have hmem : e ∈ activeEdges (r - g) := heqset.symm ▸ (by simpa [activeEdges] using he)
  simp [activeEdges, heq] at hmem

lemma activeEdges_zero {n : ℕ} {r : Weights n} (hr : IsMask r)
    (hcard : (activeEdges r).card = 0) : r = 0 := by
  have he := Finset.card_eq_zero.mp hcard
  funext e
  have h : ¬0 < r e := by
    intro hp
    have : e ∈ activeEdges r := by simpa [activeEdges] using hp
    simp [he] at this
  exact le_antisymm (le_of_not_gt h) (hr e).1

theorem findWitness_retires {n : ℕ} (o : OracleConfig) (he : 0 < o.eps1)
    (D r : Weights n) (hr : IsMask r) :
    ∀ᵐ y ∂findWitness o D r, y.elim True (Retires r) := by
  have hP := measurableSet_option_elim (measurableSet_retires r)
  unfold findWitness
  split_ifs
  · exact (ae_dirac_iff hP).mpr trivial
  · rw [findTrials_eq_repeatUntil o he]
    apply repeatUntil_ae (measurable_acceptTrial_fixed o r) hP trivial
    apply Filter.Eventually.of_forall
    intro p
    unfold acceptTrial
    split_ifs with hp
    · exact normalizeWitness_retires hr (fun e => (clippedWitness_bounds p.1 e).1) hp.2
    · trivial

end DPCut
