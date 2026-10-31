import DPCut.Lemma35

/-! Binary hierarchy construction on a subset of the ambient vertices. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

structure IsHierarchyOn {n : ℕ} (A : Finset (Fin n)) (T : Hierarchy n) : Prop where
  root : A ∈ T
  no_empty : ∅ ∉ T
  subset : ∀ D ∈ T, D ⊆ A
  leaves : ∀ v ∈ A, {v} ∈ T
  laminar : ∀ D ∈ T, ∀ E ∈ T, Disjoint D E ∨ D ⊆ E ∨ E ⊆ D
  splits : ∀ D ∈ T, 2 ≤ D.card → ∃ E F, IsSplit T D E F

lemma IsHierarchyOn.toHierarchy {n : ℕ} {T : Hierarchy n}
    (h : IsHierarchyOn Finset.univ T) : IsHierarchy T :=
  ⟨h.root, h.no_empty, fun v => h.leaves v (Finset.mem_univ v), h.laminar, h.splits⟩

lemma IsHierarchyOn.nonempty {n : ℕ} {A : Finset (Fin n)} {T : Hierarchy n}
    (h : IsHierarchyOn A T) : A.Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (fun he => h.no_empty (he ▸ h.root))

lemma hierarchyOn_singleton {n : ℕ} (v : Fin n) : IsHierarchyOn {v} {{v}} := by
  constructor
  · simp
  · intro h
    have he := Finset.mem_singleton.mp h
    have := congrArg Finset.card he
    simp at this
  · intro D hD
    have he := Finset.mem_singleton.mp hD
    rw [he]
  · intro u hu
    have he := Finset.mem_singleton.mp hu
    rw [he]
    simp
  · intro D hD E hE
    have hd : D = {v} := Finset.mem_singleton.mp hD
    have he : E = {v} := Finset.mem_singleton.mp hE
    exact Or.inr (Or.inl (by rw [hd, he]))
  · intro D hD hc
    have hd : D = {v} := Finset.mem_singleton.mp hD
    simp [hd] at hc

lemma IsSplit.mono {n : ℕ} {T U : Hierarchy n} (hTU : T ⊆ U)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) : IsSplit U A B C :=
  ⟨hTU hs.1, hTU hs.2.1, hTU hs.2.2.1, hs.2.2.2⟩

def joinHierarchy {n : ℕ} (A : Finset (Fin n)) (L R : Hierarchy n) : Hierarchy n :=
  insert A (L ∪ R)

lemma left_subset_join {n : ℕ} (A : Finset (Fin n)) (L R : Hierarchy n) : L ⊆ joinHierarchy A L R :=
  fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)

lemma right_subset_join {n : ℕ} (A : Finset (Fin n)) (L R : Hierarchy n) : R ⊆ joinHierarchy A L R :=
  fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_right _ h)

lemma joinHierarchy_split {n : ℕ} {A B C : Finset (Fin n)} {L R : Hierarchy n}
    (hL : IsHierarchyOn B L) (hR : IsHierarchyOn C R) (hBC : Disjoint B C) (he : A = B ∪ C) :
    IsSplit (joinHierarchy A L R) A B C :=
  ⟨Finset.mem_insert_self _ _, left_subset_join A L R hL.root,
    right_subset_join A L R hR.root, hL.nonempty, hR.nonempty, hBC, he⟩

lemma hierarchyOn_join {n : ℕ} {A B C : Finset (Fin n)} {L R : Hierarchy n}
    (hL : IsHierarchyOn B L) (hR : IsHierarchyOn C R) (hBC : Disjoint B C) (he : A = B ∪ C) :
    IsHierarchyOn A (joinHierarchy A L R) := by
  have hs := joinHierarchy_split hL hR hBC he
  have hsub : ∀ D ∈ joinHierarchy A L R, D ⊆ A := by
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact Finset.Subset.refl _
    · rcases Finset.mem_union.mp hD with hD | hD
      · exact (hL.subset D hD).trans hs.left_subset
      · exact (hR.subset D hD).trans hs.right_subset
  refine ⟨hs.1, ?_, hsub, ?_, ?_, ?_⟩
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · have := hs.internal
      simp [← h] at this
    · exact (Finset.mem_union.mp h).elim hL.no_empty hR.no_empty
  · intro v hv
    rw [he] at hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact left_subset_join A L R (hL.leaves v hv)
    · exact right_subset_join A L R (hR.leaves v hv)
  · intro D hD E hE
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact Or.inr (Or.inr (hsub E hE))
    rcases Finset.mem_insert.mp hE with rfl | hE
    · exact Or.inr (Or.inl (hsub D hD))
    rcases Finset.mem_union.mp hD with hD | hD <;> rcases Finset.mem_union.mp hE with hE | hE
    · exact hL.laminar D hD E hE
    · exact Or.inl (hBC.mono (hL.subset D hD) (hR.subset E hE))
    · exact Or.inl (hBC.symm.mono (hR.subset D hD) (hL.subset E hE))
    · exact hR.laminar D hD E hE
  · intro D hD hc
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact ⟨B, C, hs⟩
    · rcases Finset.mem_union.mp hD with hD | hD
      · obtain ⟨E, F, hsplit⟩ := hL.splits D hD hc
        exact ⟨E, F, hsplit.mono (left_subset_join A L R)⟩
      · obtain ⟨E, F, hsplit⟩ := hR.splits D hD hc
        exact ⟨E, F, hsplit.mono (right_subset_join A L R)⟩

/-- Any symmetric split property propagates through the recursive construction. -/
lemma allSplits_join {n : ℕ} {A B C : Finset (Fin n)} {L R : Hierarchy n}
    (hL : IsHierarchyOn B L) (hR : IsHierarchyOn C R) (hBC : Disjoint B C) (he : A = B ∪ C)
    (P : Finset (Fin n) → Finset (Fin n) → Finset (Fin n) → Prop)
    (hPsym : ∀ D E F, P D E F → P D F E) (hroot : P A B C)
    (hPL : ∀ D E F, IsSplit L D E F → P D E F)
    (hPR : ∀ D E F, IsSplit R D E F → P D E F) :
    ∀ D E F, IsSplit (joinHierarchy A L R) D E F → P D E F := by
  have htree := hierarchyOn_join hL hR hBC he
  intro D E F hs
  have transfer {E' F' : Finset (Fin n)} (hs' : IsSplit (joinHierarchy A L R) D E' F')
      (hp : P D E' F') : P D E F := by
    rcases hs'.eq_or_swap htree.laminar hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp
    · exact hPsym _ _ _ hp
  rcases Finset.mem_insert.mp hs.1 with rfl | hD
  · exact transfer (joinHierarchy_split hL hR hBC he) hroot
  · rcases Finset.mem_union.mp hD with hD | hD
    · obtain ⟨E', F', hs'⟩ := hL.splits D hD hs.internal
      exact transfer (hs'.mono (left_subset_join A L R)) (hPL D E' F' hs')
    · obtain ⟨E', F', hs'⟩ := hR.splits D hD hs.internal
      exact transfer (hs'.mono (right_subset_join A L R)) (hPR D E' F' hs')

end DPCut
