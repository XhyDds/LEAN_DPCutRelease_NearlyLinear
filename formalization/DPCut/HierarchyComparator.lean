import DPCut.HierarchyProbability

/-! The balanced comparison tree is an analysis witness. Its exact cut search
is not part of the private algorithm or its runtime claim. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma exact_quality_split_exists {n : ℕ} (w : Weights n) {b : ℝ} (hb₁ : b ≤ 1 / 3)
    (A : Finset (Fin n)) (hA : 2 ≤ A.card) :
    ∃ S, S ⊆ A ∧ SplitQuality w b b 1 A S (A \ S) := by
  have hbal := halfSubset_balanced hA hb₁
  by_cases hlarge : 1 / b ≤ (A.card : ℝ)
  · have hne : {S | BalancedWithin b A S}.Nonempty := ⟨halfSubset A, hbal⟩
    obtain ⟨S, hS, heq⟩ := (hne.image (inducedExpansion w A)).csInf_mem
      ((Set.toFinite _).image (inducedExpansion w A))
    refine ⟨S, hS.1, hS.2.1, hS.2.2, ?_⟩
    simpa only [if_pos hlarge, inducedExpansion, one_mul] using heq.le
  · refine ⟨halfSubset A, hbal.1, hbal.2.1, hbal.2.2, ?_⟩
    simpa only [if_neg hlarge] using halfSubset_even A

lemma hierarchyQuality_exists {n : ℕ} (hn : 0 < n) (w : Weights n) {b : ℝ}
    (hb : 0 < b) (hb₁ : b ≤ 1 / 3) :
    ∃ T : Hierarchy n, HierarchyQualityOn w b b 1 Finset.univ T := by
  let pick (A : Finset (Fin n)) := if h : 2 ≤ A.card
    then (exact_quality_split_exists w hb₁ A h).choose else halfSubset A
  let K (A : Finset (Fin n)) : Kernel (Weights n) (Finset (Fin n)) :=
    ⟨fun _ => Measure.dirac (pick A), measurable_const⟩
  letI (A : Finset (Fin n)) : IsMarkovKernel (K A) := by
    constructor
    intro x
    change IsProbabilityMeasure (Measure.dirac (pick A))
    infer_instance
  have hg : ∀ A : Finset (Fin n), 2 ≤ A.card → HighProbability (K A w) 0
      (fun S => S ⊆ A ∧ SplitQuality w b b 1 A S (A \ S)) := by
    intro A hA
    apply highProbability_dirac_finite
    dsimp [pick]
    rw [dif_pos hA]
    exact (exact_quality_split_exists w hb₁ A hA).choose_spec
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hgood := hierarchyLaw_quality K w hb hb₁ (le_refl 0) hg n hne
    (by simp : (Finset.univ : Finset (Fin n)).card ≤ n + 1)
  by_contra hnot
  have he : {T : Hierarchy n | HierarchyQualityOn w b b 1 Finset.univ T} = ∅ := by
    ext T
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hT
    exact hnot ⟨T, hT⟩
  have hh := hgood.2
  norm_num [prob, he] at hh

lemma balanced_comparator {n : ℕ} (hn : 2 ≤ n) {w : Weights n} (hw : Nonnegative w) :
    ∃ T : Hierarchy n, BalancedHierarchy (1 / 4) T ∧ hcCost w T ≤ 16 * hcOptimum w := by
  obtain ⟨T, hT⟩ := hierarchyQuality_exists (by omega : 0 < n) w (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3)
  obtain ⟨hb, hr⟩ := hT.to_global
  refine ⟨T, hb, ?_⟩
  obtain ⟨Tstar, hstar, heq⟩ := hcOptimum_exists w hb.1
  have hh := hierarchy_charging_bound hw hb.1 hstar (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3) (le_refl 1) hr
  norm_num [heq] at hh
  exact hh

end DPCut
