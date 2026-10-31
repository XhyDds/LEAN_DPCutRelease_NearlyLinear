import DPCut.Applications
import DPCut.ApplicationOptima
import Mathlib.Data.Finset.Interval

/-! Immediate combinatorial foundations of the laminar-family representation
of binary hierarchies used by Appendix C. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma IsHierarchy.nonempty {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A : Finset (Fin n)} (hA : A ∈ T) : A.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  exact hT.2.1 (h ▸ hA)

lemma IsHierarchy.nested {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B : Finset (Fin n)} (hA : A ∈ T) (hB : B ∈ T) {v : Fin n}
    (hvA : v ∈ A) (hvB : v ∈ B) : A ⊆ B ∨ B ⊆ A := by
  rcases hT.2.2.2.1 A hA B hB with h | h
  · exact False.elim ((Finset.disjoint_left.mp h) hvA hvB)
  · exact h

lemma IsSplit.left_subset {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : B ⊆ A := by rw [h.2.2.2.2.2.2]; exact Finset.subset_union_left

lemma IsSplit.right_subset {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : C ⊆ A := by rw [h.2.2.2.2.2.2]; exact Finset.subset_union_right

lemma IsSplit.card_eq {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : A.card = B.card + C.card := by
  rw [h.2.2.2.2.2.2, Finset.card_union_of_disjoint h.2.2.2.2.2.1]

lemma IsSplit.card_lt {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : B.card < A.card ∧ C.card < A.card := by
  have hb := h.2.2.2.1.card_pos
  have hc := h.2.2.2.2.1.card_pos
  rw [h.card_eq]
  omega

lemma IsSplit.internal {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : 2 ≤ A.card := by
  have hb := h.2.2.2.1.card_pos
  have hc := h.2.2.2.2.1.card_pos
  rw [h.card_eq]
  omega

lemma IsSplit.right_eq_sdiff {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : C = A \ B := by
  rw [h.2.2.2.2.2.2]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro hv
    exact ⟨Or.inr hv, fun hb => Finset.disjoint_left.mp h.2.2.2.2.2.1 hb hv⟩
  · rintro ⟨hb | hc, hn⟩
    · exact False.elim (hn hb)
    · exact hc

lemma split_descendant_side {n : ℕ} {T : Hierarchy n}
    (hLam : ∀ A ∈ T, ∀ B ∈ T, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A)
    {A B C D : Finset (Fin n)} (hs : IsSplit T A B C) (hD : D ∈ T)
    (hDA : D ⊆ A) (hneq : D ≠ A) : D ⊆ B ∨ D ⊆ C := by
  by_cases hDB : Disjoint D B
  · right
    intro v hv
    have hvA := hDA hv
    rw [hs.2.2.2.2.2.2] at hvA
    rcases Finset.mem_union.mp hvA with hb | hc
    · exact False.elim (Finset.disjoint_left.mp hDB hv hb)
    · exact hc
  · rcases hLam D hD B hs.2.1 with h | h | h
    · exact False.elim (hDB h)
    · exact Or.inl h
    · by_cases hDC : Disjoint D C
      · left
        intro v hv
        have hvA := hDA hv
        rw [hs.2.2.2.2.2.2] at hvA
        rcases Finset.mem_union.mp hvA with hb | hc
        · exact hb
        · exact False.elim (Finset.disjoint_left.mp hDC hv hc)
      · rcases hLam D hD C hs.2.2.1 with hh | hh | hh
        · exact False.elim (hDC hh)
        · exact Or.inr hh
        · exact False.elim (hneq (Finset.Subset.antisymm hDA (by
            rw [hs.2.2.2.2.2.2]
            exact Finset.union_subset h hh)))

/-- Every proper descendant lies wholly in one of the two children. -/
lemma IsHierarchy.descendant_side {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C D : Finset (Fin n)} (hs : IsSplit T A B C) (hD : D ∈ T)
    (hDA : D ⊆ A) (hneq : D ≠ A) : D ⊆ B ∨ D ⊆ C := by
  exact split_descendant_side hT.2.2.2.1 hs hD hDA hneq

def hierarchyChildren {n : ℕ} (T : Hierarchy n) (A : Finset (Fin n)) :
    Finset (Fin n) × Finset (Fin n) :=
  if h : ∃ B C, IsSplit T A B C then (h.choose, h.choose_spec.choose) else (∅, ∅)

lemma hierarchyChildren_spec {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A : Finset (Fin n)} (hA : A ∈ T) (hcard : 2 ≤ A.card) :
    IsSplit T A (hierarchyChildren T A).1 (hierarchyChildren T A).2 := by
  have h := hT.2.2.2.2 A hA hcard
  simp only [hierarchyChildren, dif_pos h]
  exact h.choose_spec.choose_spec

def subtreeClusters {n : ℕ} (T : Hierarchy n) (A : Finset (Fin n)) : Hierarchy n :=
  T.filter (fun D => D ⊆ A)

lemma mem_subtreeClusters {n : ℕ} {T : Hierarchy n} {A D : Finset (Fin n)} :
    D ∈ subtreeClusters T A ↔ D ∈ T ∧ D ⊆ A := Finset.mem_filter

lemma subtreeClusters_disjoint {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {B C : Finset (Fin n)} (hBC : Disjoint B C) :
    Disjoint (subtreeClusters T B) (subtreeClusters T C) := by
  apply Finset.disjoint_left.mpr
  intro D hDB hDC
  have h₁ := mem_subtreeClusters.mp hDB
  have h₂ := mem_subtreeClusters.mp hDC
  obtain ⟨v, hv⟩ := hT.nonempty h₁.1
  exact Finset.disjoint_left.mp hBC (h₁.2 hv) (h₂.2 hv)

lemma subtreeClusters_split {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    subtreeClusters T A = insert A (subtreeClusters T B ∪ subtreeClusters T C) := by
  ext D
  simp only [mem_subtreeClusters, Finset.mem_insert, Finset.mem_union]
  constructor
  · rintro ⟨hD, hDA⟩
    by_cases he : D = A
    · exact Or.inl he
    · exact Or.inr ((hT.descendant_side hs hD hDA he).elim
        (fun h => Or.inl ⟨hD, h⟩) (fun h => Or.inr ⟨hD, h⟩))
  · rintro (rfl | ⟨hD, hDB⟩ | ⟨hD, hDC⟩)
    · exact ⟨hs.1, Finset.Subset.refl _⟩
    · exact ⟨hD, hDB.trans hs.left_subset⟩
    · exact ⟨hD, hDC.trans hs.right_subset⟩

lemma sum_subtreeClusters_split {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) (f : Finset (Fin n) → ℝ) :
    (∑ D ∈ subtreeClusters T A, f D) = f A +
      (∑ D ∈ subtreeClusters T B, f D) + (∑ D ∈ subtreeClusters T C, f D) := by
  have hlt := hs.card_lt
  rw [subtreeClusters_split hT hs, Finset.sum_insert, Finset.sum_union]
  · ring
  · exact subtreeClusters_disjoint hT hs.2.2.2.2.2.1
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · have hc := Finset.card_le_card (mem_subtreeClusters.mp h).2
      omega
    · have hc := Finset.card_le_card (mem_subtreeClusters.mp h).2
      omega

lemma subtreeClusters_singleton {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T) (v : Fin n) :
    subtreeClusters T {v} = {{v}} := by
  ext D
  simp only [mem_subtreeClusters, Finset.mem_singleton]
  constructor
  · rintro ⟨hD, hsub⟩
    exact Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hT.nonempty hD, fun x hx => Finset.mem_singleton.mp (hsub hx)⟩
  · rintro rfl
    exact ⟨hT.2.2.1 v, Finset.Subset.refl _⟩

lemma subtreeClusters_univ {n : ℕ} (T : Hierarchy n) : subtreeClusters T Finset.univ = T := by
  ext D
  simp [subtreeClusters]

lemma hierarchy_lca_exists {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T) (e : Edge n) :
    ∃ A ∈ T, e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ A.card = lcaSize T e := by
  have hne : ((fun A : Finset (Fin n) => A.card) '' {A | A ∈ T ∧ e.val.1 ∈ A ∧ e.val.2 ∈ A}).Nonempty :=
    ⟨n, Finset.univ, ⟨hT.1, Finset.mem_univ _, Finset.mem_univ _⟩, Finset.card_univ.trans (Fintype.card_fin _)⟩
  obtain ⟨A, hA, heq⟩ := Nat.sInf_mem hne
  exact ⟨A, hA.1, hA.2.1, hA.2.2, heq⟩

lemma lcaSize_le {n : ℕ} {T : Hierarchy n} {A : Finset (Fin n)} {e : Edge n}
    (hA : A ∈ T) (hu : e.val.1 ∈ A) (hv : e.val.2 ∈ A) : lcaSize T e ≤ A.card :=
  Nat.sInf_le ⟨A, ⟨hA, hu, hv⟩, rfl⟩

lemma lcaSize_split {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) {e : Edge n}
    (hu : e.val.1 ∈ B) (hv : e.val.2 ∈ C) : lcaSize T e = A.card := by
  apply Nat.le_antisymm (lcaSize_le hs.1 (hs.left_subset hu) (hs.right_subset hv))
  obtain ⟨D, hD, huD, hvD, heq⟩ := hierarchy_lca_exists hT e
  rw [← heq]
  rcases hT.nested hD hs.1 huD (hs.left_subset hu) with hsub | hsub
  · by_cases he : D = A
    · rw [he]
    · rcases hT.descendant_side hs hD hsub he with hB | hC
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 (hB hvD) hv)
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 hu (hC huD))
  · exact Finset.card_le_card hsub

lemma IsSplit.swap {n : ℕ} {T : Hierarchy n} {A B C : Finset (Fin n)}
    (h : IsSplit T A B C) : IsSplit T A C B :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.1, h.2.2.2.1,
    h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.trans (Finset.union_comm _ _)⟩

lemma hierarchy_induction {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    (P : Finset (Fin n) → Prop) (hleaf : ∀ v, P {v})
    (hnode : ∀ A B C, IsSplit T A B C → P B → P C → P A)
    {A : Finset (Fin n)} (hA : A ∈ T) : P A := by
  have go : ∀ k, ∀ A ∈ T, A.card = k → P A := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro A hA heq
      by_cases hc : 2 ≤ A.card
      · obtain ⟨B, C, hs⟩ := hT.2.2.2.2 A hA hc
        exact hnode A B C hs (ih B.card (heq ▸ hs.card_lt.1) B hs.2.1 rfl)
          (ih C.card (heq ▸ hs.card_lt.2) C hs.2.2.1 rfl)
      · have hone : A.card = 1 := by have := (hT.nonempty hA).card_pos; omega
        obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
        exact hleaf v
  exact go A.card A hA rfl

lemma IsSplit.eq_or_swap {n : ℕ} {T : Hierarchy n}
    (hLam : ∀ A ∈ T, ∀ B ∈ T, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A)
    {A B C B' C' : Finset (Fin n)} (hs : IsSplit T A B C) (hc : IsSplit T A B' C') :
    (B' = B ∧ C' = C) ∨ (B' = C ∧ C' = B) := by
  have hleft := split_descendant_side hLam hs hc.2.1 hc.left_subset
    (fun he => by have := hc.card_lt.1; rw [he] at this; omega)
  have hright := split_descendant_side hLam hs hc.2.2.1 hc.right_subset
    (fun he => by have := hc.card_lt.2; rw [he] at this; omega)
  rcases hleft with hl | hl <;> rcases hright with hr | hr
  · obtain ⟨v, hv⟩ := hs.2.2.2.2.1
    have hvA := hs.right_subset hv
    rw [hc.2.2.2.2.2.2] at hvA
    exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1
      ((Finset.mem_union.mp hvA).elim (fun h => hl h) (fun h => hr h)) hv)
  · left
    constructor
    · apply Finset.Subset.antisymm hl
      intro v hv
      have hvA := hs.left_subset hv
      rw [hc.2.2.2.2.2.2] at hvA
      rcases Finset.mem_union.mp hvA with hv | hv
      · exact hv
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 ‹v ∈ B› (hr hv))
    · apply Finset.Subset.antisymm hr
      intro v hv
      have hvA := hs.right_subset hv
      rw [hc.2.2.2.2.2.2] at hvA
      rcases Finset.mem_union.mp hvA with hv | hv
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 (hl hv) ‹v ∈ C›)
      · exact hv
  · right
    constructor
    · apply Finset.Subset.antisymm hl
      intro v hv
      have hvA := hs.right_subset hv
      rw [hc.2.2.2.2.2.2] at hvA
      rcases Finset.mem_union.mp hvA with hv | hv
      · exact hv
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 (hr hv) ‹v ∈ C›)
    · apply Finset.Subset.antisymm hr
      intro v hv
      have hvA := hs.left_subset hv
      rw [hc.2.2.2.2.2.2] at hvA
      rcases Finset.mem_union.mp hvA with hv | hv
      · exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 ‹v ∈ B› (hl hv))
      · exact hv
  · obtain ⟨v, hv⟩ := hs.2.2.2.1
    have hvA := hs.left_subset hv
    rw [hc.2.2.2.2.2.2] at hvA
    exact False.elim (Finset.disjoint_left.mp hs.2.2.2.2.2.1 hv
      ((Finset.mem_union.mp hvA).elim (fun h => hl h) (fun h => hr h)))

lemma hierarchyChildren_eq_or_swap {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    ((hierarchyChildren T A).1 = B ∧ (hierarchyChildren T A).2 = C) ∨
    ((hierarchyChildren T A).1 = C ∧ (hierarchyChildren T A).2 = B) := by
  have hc := hierarchyChildren_spec hT hs.1 hs.internal
  exact hs.eq_or_swap hT.2.2.2.1 hc


end DPCut
