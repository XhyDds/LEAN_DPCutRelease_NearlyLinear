import DPCut.HierarchyKernel

/-! A union bound over the actual recursive calls, using the two child sizes. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma highProbability_dirac_finite {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (x : α) {P : α → Prop} (hx : P x) :
    HighProbability (Measure.dirac x) 0 P := by
  have hm : MeasurableSet {y | P y} := Set.toFinite _ |>.measurableSet
  refine ⟨hm, ?_⟩
  simp [prob, Measure.dirac_apply' _ hm, hx]

lemma HighProbability.map_finite {α β : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    {μ : Measure α} [IsProbabilityMeasure μ] {P : α → Prop} {Q : β → Prop} {τ : ℝ}
    (h : HighProbability μ τ P) (f : α → β) (hf : ∀ x, P x → Q (f x)) :
    HighProbability (μ.map f) τ Q := by
  have hQ : MeasurableSet {y | Q y} := Set.toFinite _ |>.measurableSet
  refine ⟨hQ, ?_⟩
  change 1 - τ ≤ (μ.map f {y | Q y}).toReal
  rw [Measure.map_apply (measurable_of_finite _) hQ]
  exact h.2.trans (measureReal_mono hf)

variable {n : ℕ} (K : Finset (Fin n) → Kernel (Weights n) (Finset (Fin n)))
  [∀ A, IsMarkovKernel (K A)]

omit [∀ A, IsMarkovKernel (K A)] in
lemma hierarchyLaw_singleton (c : ℝ) (t : ℕ) (v : Fin n) (w : Weights n) :
    hierarchyLaw K c t {v} w = Measure.dirac {{v}} := by
  cases t <;> simp [hierarchyLaw]

lemma hierarchyLaw_quality (w : Weights n) {b c a τ : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1 / 3)
    (hτ : 0 ≤ τ)
    (hgood : ∀ A : Finset (Fin n), 2 ≤ A.card → HighProbability (K A w) τ
      (fun S => S ⊆ A ∧ SplitQuality w b c a A S (A \ S)))
    (t : ℕ) {A : Finset (Fin n)} (hA : A.Nonempty) (ht : A.card ≤ t + 1) :
    HighProbability (hierarchyLaw K c t A w) (((A.card : ℝ) - 1) * τ)
      (HierarchyQualityOn w b c a A) := by
  induction t generalizing A with
  | zero =>
    have hcard : A.card = 1 := by have := hA.card_pos; omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
    simpa only [hierarchyLaw_singleton, Finset.card_singleton, Nat.cast_one, sub_self, zero_mul]
      using highProbability_dirac_finite ({{v}} : Hierarchy n) (hierarchyQuality_singleton w b c a v)
  | succ t ih =>
    by_cases hlarge : 2 ≤ A.card
    · let F : Kernel (Finset (Fin n)) (Hierarchy n) :=
        ⟨fun raw => (hierarchyLaw K c t (safeHierarchySplit c A raw) w).bind fun L =>
          (hierarchyLaw K c t (A \ safeHierarchySplit c A raw) w).map (joinHierarchy A L),
          measurable_of_finite _⟩
      letI : IsMarkovKernel F := by
        constructor
        intro raw
        letI (L : Hierarchy n) : IsProbabilityMeasure
            ((hierarchyLaw K c t (A \ safeHierarchySplit c A raw) w).map (joinHierarchy A L)) :=
          Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
        exact probability_bind _ _ (measurable_of_finite _)
      have hcont : ∀ raw, raw ⊆ A ∧ SplitQuality w b c a A raw (A \ raw) →
          HighProbability (F raw) (((A.card : ℝ) - 2) * τ) (HierarchyQualityOn w b c a A) := by
        intro S hS
        have hbal : BalancedWithin c A S := ⟨hS.1, hS.2.1, hS.2.2.1⟩
        obtain ⟨hneS, hneC, hltS, hltC⟩ := hbal.split_data hc hlarge
        have hleft := ih hneS (show S.card ≤ t + 1 by omega)
        have hright := ih hneC (show (A \ S).card ≤ t + 1 by omega)
        let J : Kernel (Hierarchy n) (Hierarchy n) :=
          ⟨fun L => (hierarchyLaw K c t (A \ S) w).map (joinHierarchy A L), measurable_of_finite _⟩
        letI : IsMarkovKernel J := ⟨fun L => Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable⟩
        have hβL : 0 ≤ ((S.card : ℝ) - 1) * τ := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ S.card from hneS.card_pos))) hτ
        have hβR : 0 ≤ (((A \ S).card : ℝ) - 1) * τ := mul_nonneg
          (sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ (A \ S).card from hneC.card_pos))) hτ
        have hj : ∀ L, HierarchyQualityOn w b c a S L →
            HighProbability (J L) ((((A \ S).card : ℝ) - 1) * τ) (HierarchyQualityOn w b c a A) := by
          intro L hL
          exact hright.map_finite (joinHierarchy A L) (fun R hR =>
            hierarchyQuality_join hL hR disjoint_sdiff_self_right
              (Finset.union_sdiff_of_subset hS.1).symm hS.2)
        have hh := hleft.bind J hβL hβR (Set.toFinite _ |>.measurableSet) hj
        have hcard : (A.card : ℝ) = S.card + (A \ S).card := by
          exact_mod_cast (Finset.card_sdiff_add_card_eq_card hS.1).symm.trans (Nat.add_comm _ _)
        change HighProbability ((hierarchyLaw K c t (safeHierarchySplit c A S) w).bind fun L =>
          (hierarchyLaw K c t (A \ safeHierarchySplit c A S) w).map (joinHierarchy A L)) _ _
        rw [splitQuality_implies_safe hS.1 hS.2]
        convert hh using 1
        nlinarith
      have hβ : 0 ≤ ((A.card : ℝ) - 2) * τ := mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hlarge)) hτ
      have hh := (hgood A hlarge).bind F hτ hβ (Set.toFinite _ |>.measurableSet) hcont
      change HighProbability (if 2 ≤ A.card then (K A w).bind F else Measure.dirac {A}) _ _
      rw [if_pos hlarge]
      convert hh using 1
      ring
    · have hcard : A.card = 1 := by have := hA.card_pos; omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      simpa only [hierarchyLaw_singleton, Finset.card_singleton, Nat.cast_one, sub_self, zero_mul]
        using highProbability_dirac_finite ({{v}} : Hierarchy n) (hierarchyQuality_singleton w b c a v)

end DPCut
