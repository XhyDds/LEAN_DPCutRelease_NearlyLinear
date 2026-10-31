import DPCut.HierarchyBasics
import DPCut.CutDiscrepancy

/-! The positive boundary-cut decomposition of Dasgupta's hierarchy objective. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def hcSubcost {n : ℕ} (w : Weights n) (T : Hierarchy n) (A : Finset (Fin n)) : ℝ :=
  ∑ e, if e.val.1 ∈ A ∧ e.val.2 ∈ A then w e * lcaSize T e else 0

lemma hcSubcost_singleton {n : ℕ} (w : Weights n) (T : Hierarchy n) (v : Fin n) :
    hcSubcost w T {v} = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  simp only [Finset.mem_singleton]
  split_ifs with h
  · exact False.elim (hne (h.1.trans h.2.symm))
  · rfl

lemma hcSubcost_univ {n : ℕ} (w : Weights n) (T : Hierarchy n) :
    hcSubcost w T Finset.univ = hcCost w T := by simp [hcSubcost, hcCost]

lemma hcSubcost_split {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    hcSubcost w T A = hcSubcost w T B + hcSubcost w T C + A.card * between w B C := by
  simp only [hcSubcost, between, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have h₁ : e.val.1 ∈ B → e.val.1 ∉ C := fun hb => Finset.disjoint_left.mp hs.2.2.2.2.2.1 hb
  have h₂ : e.val.2 ∈ B → e.val.2 ∉ C := fun hb => Finset.disjoint_left.mp hs.2.2.2.2.2.1 hb
  have hbc := fun (hb : e.val.1 ∈ B) (hc : e.val.2 ∈ C) => lcaSize_split hT hs hb hc
  have hcb := fun (hc : e.val.1 ∈ C) (hb : e.val.2 ∈ B) => lcaSize_split hT hs.swap hc hb
  have hmem (v : Fin n) : v ∈ A ↔ v ∈ B ∨ v ∈ C := by
    rw [hs.2.2.2.2.2.2, Finset.mem_union]
  by_cases hb₁ : e.val.1 ∈ B <;> by_cases hc₁ : e.val.1 ∈ C <;>
    by_cases hb₂ : e.val.2 ∈ B <;> by_cases hc₂ : e.val.2 ∈ C <;>
    (try exact False.elim (h₁ hb₁ hc₁)) <;>
    (try exact False.elim (h₂ hb₂ hc₂)) <;>
    simp [hmem, hb₁, hc₁, hb₂, hc₂, hbc, hcb, mul_comm]

def hierarchyTerm {n : ℕ} (w : Weights n) (T : Hierarchy n) (A : Finset (Fin n)) : ℝ :=
  if 2 ≤ A.card then
    (hierarchyChildren T A).2.card * cut w (hierarchyChildren T A).1 +
    (hierarchyChildren T A).1.card * cut w (hierarchyChildren T A).2
  else 0

/-- The subtree identity retains its boundary term; at the root that term vanishes. -/
lemma hcSubcost_boundary {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T)
    {A : Finset (Fin n)} (hA : A ∈ T) :
    2 * hcSubcost w T A =
      (∑ D ∈ subtreeClusters T A, hierarchyTerm w T D) +
      (∑ v ∈ A, cut w {v}) - A.card * cut w A := by
  apply hierarchy_induction hT (fun A => 2 * hcSubcost w T A =
      (∑ D ∈ subtreeClusters T A, hierarchyTerm w T D) +
      (∑ v ∈ A, cut w {v}) - A.card * cut w A) _ _ hA
  · intro v
    simp [hcSubcost_singleton, subtreeClusters_singleton hT, hierarchyTerm]
  · intro A B C hs ihB ihC
    -- Use the canonical children so that the summand at A is definitionally the desired one.
    have sides := hierarchyChildren_eq_or_swap hT hs
    have hterm : hierarchyTerm w T A = C.card * cut w B + B.card * cut w C := by
      simp only [hierarchyTerm, if_pos hs.internal]
      rcases sides with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hl, hr]
      · rw [hl, hr]
        ring
    have hsum : (∑ v ∈ A, cut w {v}) = (∑ v ∈ B, cut w {v}) + (∑ v ∈ C, cut w {v}) := by
      rw [hs.2.2.2.2.2.2, Finset.sum_union hs.2.2.2.2.2.1]
    have hb := two_between_eq_cuts w hs.2.2.2.2.2.1
    rw [← hs.2.2.2.2.2.2] at hb
    rw [hcSubcost_split w hT hs, sum_subtreeClusters_split hT hs, hterm, hsum]
    have he : (A.card : ℝ) = B.card + C.card := by exact_mod_cast hs.card_eq
    rw [he]
    nlinarith [congrArg (fun x : ℝ => ((B.card : ℝ) + C.card) * x) hb]

lemma cut_univ {n : ℕ} (w : Weights n) : cut w Finset.univ = 0 := by
  simp [cut, pairing, cutQuery]

lemma hcCost_boundary {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T) :
    2 * hcCost w T = (∑ D ∈ T, hierarchyTerm w T D) + ∑ v, cut w {v} := by
  simpa [hcSubcost_univ, subtreeClusters_univ, cut_univ] using hcSubcost_boundary w hT hT.1

end DPCut
