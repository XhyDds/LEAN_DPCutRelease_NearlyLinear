import DPCut.HalfSubset

/-! Symmetric local quality certificates for constructing recursive hierarchies. -/
set_option autoImplicit false
noncomputable section
namespace DPCut
attribute [local instance] Classical.propDecidable

def SplitQuality {n : ℕ} (w : Weights n) (b c a : ℝ) (A B C : Finset (Fin n)) : Prop :=
  c * A.card ≤ B.card ∧ c * A.card ≤ C.card ∧
    if 1 / b ≤ (A.card : ℝ) then
      between w B C / min (B.card : ℝ) (C.card : ℝ) ≤
        a * sInf (inducedExpansion w A '' {S | BalancedWithin b A S})
    else B.card ≤ C.card + 1 ∧ C.card ≤ B.card + 1

def HierarchyQualityOn {n : ℕ} (w : Weights n) (b c a : ℝ) (A : Finset (Fin n)) (T : Hierarchy n) : Prop :=
  IsHierarchyOn A T ∧ ∀ D E F, IsSplit T D E F → SplitQuality w b c a D E F

lemma SplitQuality.swap {n : ℕ} {w : Weights n} {b c a : ℝ} {A B C : Finset (Fin n)}
    (h : SplitQuality w b c a A B C) : SplitQuality w b c a A C B := by
  refine ⟨h.2.1, h.1, ?_⟩
  by_cases hl : 1 / b ≤ (A.card : ℝ)
  · simpa only [hl, if_true, between_comm w C B, min_comm (C.card : ℝ)] using h.2.2
  · simpa only [hl, if_false, and_comm] using h.2.2

lemma hierarchyQuality_singleton {n : ℕ} (w : Weights n) (b c a : ℝ) (v : Fin n) :
    HierarchyQualityOn w b c a {v} {{v}} := by
  refine ⟨hierarchyOn_singleton v, ?_⟩
  intro D E F hs
  have he := Finset.mem_singleton.mp hs.1
  have hc := hs.internal
  simp [he] at hc

lemma hierarchyQuality_join {n : ℕ} {w : Weights n} {b c a : ℝ}
    {A B C : Finset (Fin n)} {L R : Hierarchy n}
    (hL : HierarchyQualityOn w b c a B L) (hR : HierarchyQualityOn w b c a C R)
    (hBC : Disjoint B C) (he : A = B ∪ C) (hq : SplitQuality w b c a A B C) :
    HierarchyQualityOn w b c a A (joinHierarchy A L R) :=
  ⟨hierarchyOn_join hL.1 hR.1 hBC he,
    allSplits_join hL.1 hR.1 hBC he (SplitQuality w b c a) (fun _ _ _ h => h.swap) hq hL.2 hR.2⟩

lemma HierarchyQualityOn.to_global {n : ℕ} {w : Weights n} {b c a : ℝ} {T : Hierarchy n}
    (h : HierarchyQualityOn w b c a Finset.univ T) :
    BalancedHierarchy c T ∧ RecursiveApproximation w b a T := by
  refine ⟨⟨h.1.toHierarchy, fun A B C hs => ⟨(h.2 A B C hs).1, (h.2 A B C hs).2.1⟩⟩, ?_⟩
  intro A B C hs
  have hh := (h.2 A B C hs).2.2
  simpa only [inducedExpansion, ← hs.right_eq_sdiff] using hh

def safeHierarchySplit {n : ℕ} (c : ℝ) (A S : Finset (Fin n)) : Finset (Fin n) :=
  if BalancedWithin c A S then S else halfSubset A

lemma safeHierarchySplit_balanced {n : ℕ} {c : ℝ} (hc : c ≤ 1 / 3)
    {A : Finset (Fin n)} (hA : 2 ≤ A.card) (S : Finset (Fin n)) :
    BalancedWithin c A (safeHierarchySplit c A S) := by
  unfold safeHierarchySplit
  split_ifs with h
  · exact h
  · exact halfSubset_balanced hA hc

lemma splitQuality_implies_safe {n : ℕ} {w : Weights n} {b c a : ℝ}
    {A S : Finset (Fin n)} (hS : S ⊆ A) (h : SplitQuality w b c a A S (A \ S)) :
    safeHierarchySplit c A S = S := if_pos ⟨hS, h.1, h.2.1⟩

end DPCut
