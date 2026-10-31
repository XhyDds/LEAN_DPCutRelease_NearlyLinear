import DPCut.Algorithms
import DPCut.Lemma10
import Mathlib.MeasureTheory.Order.Lattice

/-! Bounds and measurability of the accepted witness used in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace DPCut
attribute [local instance] Classical.propDecidable

lemma activeMaximum_nonneg {n : ℕ} (r g : Weights n) : 0 ≤ activeMaximum r g := by
  apply le_csSup
  · exact ((Set.toFinite _).insert 0).bddAbove
  · exact Set.mem_insert _ _

lemma le_activeMaximum {n : ℕ} (r g : Weights n) (e : Edge n) (he : 0 < r e) :
    g e ≤ activeMaximum r g := by
  apply le_csSup
  · exact ((Set.toFinite _).insert 0).bddAbove
  · exact mem_insert_of_mem _ ⟨e, he, rfl⟩

lemma activeMaximum_le {n : ℕ} (r g : Weights n) {a : ℝ} (ha : 0 ≤ a)
    (hg : ∀ e, 0 < r e → g e ≤ a) : activeMaximum r g ≤ a := by
  apply csSup_le (by exact ⟨0, mem_insert _ _⟩)
  rintro x (rfl | ⟨e, he, rfl⟩)
  · exact ha
  · exact hg e he

lemma clippedWitness_bounds {n k : ℕ} (z : Fin k → Fin n → ℝ) (e : Edge n) :
    0 ≤ clippedWitness z e ∧ clippedWitness z e ≤ 1 := by
  have h : 0 ≤ rawWitness z e := by
    unfold rawWitness
    positivity
  exact ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩

lemma normalizeWitness_bounds {n : ℕ} {r g : Weights n} (hr : IsMask r)
    (hg : ∀ e, 0 ≤ g e) (hp : 0 < activeMaximum r g) (e : Edge n) :
    0 ≤ normalizeWitness r g e ∧ normalizeWitness r g e ≤ r e := by
  dsimp [normalizeWitness]
  constructor
  · exact div_nonneg (mul_nonneg (hr e).1 (hg e)) hp.le
  · apply (div_le_iff₀ hp).mpr
    rcases eq_or_lt_of_le (hr e).1 with he | he
    · simp [← he]
    · exact mul_le_mul_of_nonneg_left (le_activeMaximum r g e he) he.le

lemma normalized_witness_charge {n : ℕ} {r g q : Weights n} (hr : IsMask r)
    (hgood : ∀ e, q e / 8 ≤ g e) (hg : ∀ e, 0 ≤ g e ∧ g e ≤ 1)
    (hp : 0 < activeMaximum r g) (e : Edge n) :
    r e * q e ≤ 8 * normalizeWitness r g e := by
  have hm : activeMaximum r g ≤ 1 := activeMaximum_le r g zero_le_one (fun i _ => (hg i).2)
  have hl := mul_le_mul_of_nonneg_left (hgood e) (hr e).1
  have hn : r e * g e ≤ normalizeWitness r g e := by
    apply (le_div_iff₀ hp).mpr
    exact mul_le_of_le_one_right (mul_nonneg (hr e).1 (hg e).1) hm
  nlinarith

private def activeValue {n : ℕ} (r g : Weights n) : Option (Edge n) → ℝ
  | none => 0
  | some e => if 0 < r e then g e else 0

lemma activeMaximum_eq_sup {n : ℕ} (r g : Weights n) :
    activeMaximum r g = Finset.univ.sup' Finset.univ_nonempty (activeValue r g) := by
  rw [Finset.sup'_eq_csSup_image]
  unfold activeMaximum
  congr 1
  ext x
  constructor
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact ⟨none, Finset.mem_univ _, rfl⟩
    · exact ⟨some e, Finset.mem_univ _, by simp [activeValue, show 0 < r e from he]⟩
  · rintro ⟨e, _, rfl⟩
    cases e with
    | none => exact mem_insert _ _
    | some e =>
      by_cases he : 0 < r e
      · exact mem_insert_of_mem _ ⟨e, he, by simp [activeValue, he]⟩
      · simp [activeValue, he]

lemma measurable_activeMaximum {n : ℕ} :
    Measurable (fun p : Weights n × Weights n => activeMaximum p.1 p.2) := by
  simp_rw [activeMaximum_eq_sup]
  have hm (e : Option (Edge n)) :
      Measurable (fun p : Weights n × Weights n => activeValue p.1 p.2 e) := by
    cases e with
    | none => exact measurable_const
    | some e =>
      apply Measurable.ite
      · exact measurableSet_lt measurable_const (by fun_prop)
      · exact (measurable_pi_apply e).comp measurable_snd
      · exact measurable_const
  convert Finset.measurable_sup' Finset.univ_nonempty (fun e _ => hm e) using 1
  ext p
  simp only [Finset.sup'_apply]

lemma measurable_normalizeWitness {n : ℕ} :
    Measurable (fun p : Weights n × Weights n => normalizeWitness p.1 p.2) := by
  apply measurable_pi_lambda
  intro e
  exact ((show Measurable (fun p : Weights n × Weights n => p.1 e * p.2 e) by
    fun_prop).div measurable_activeMaximum)

end DPCut
