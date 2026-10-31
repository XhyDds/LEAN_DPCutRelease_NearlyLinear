import DPCut.HierarchyBalance

/-! Partitions of a hierarchy at a real size threshold and balanced unions of their blocks. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def levelClusters {n : ℕ} (T : Hierarchy n) (z : ℝ) : Hierarchy n :=
  T.filter fun A => (A.card : ℝ) ≤ z ∧ ∀ B ∈ T, A ⊆ B → (B.card : ℝ) ≤ z → B = A

lemma levelClusters_cover {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {z : ℝ} (hz : 1 ≤ z) (v : Fin n) : ∃ A ∈ levelClusters T z, v ∈ A := by
  let S := T.filter fun A => v ∈ A ∧ (A.card : ℝ) ≤ z
  have hn : S.Nonempty := ⟨{v}, by simp [S, hT.2.2.1, hz]⟩
  obtain ⟨A, hA, hmax⟩ := S.exists_max_image Finset.card hn
  have ha := Finset.mem_filter.mp hA
  refine ⟨A, Finset.mem_filter.mpr ⟨ha.1, ha.2.2, ?_⟩, ha.2.1⟩
  intro B hB hAB hzB
  exact (Finset.eq_of_subset_of_card_le hAB (hmax B (Finset.mem_filter.mpr
    ⟨hB, hAB ha.2.1, hzB⟩))).symm

lemma levelClusters_disjoint {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T) (z : ℝ) :
    (levelClusters T z : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro A hA B hB hne
  have ha := Finset.mem_filter.mp hA
  have hb := Finset.mem_filter.mp hB
  rcases hT.2.2.2.1 A ha.1 B hb.1 with hd | hd | hd
  · exact hd
  · exact False.elim (hne (ha.2.2 B hb.1 hd hb.2.1).symm)
  · exact False.elim (hne (hb.2.2 A ha.1 hd ha.2.1))

lemma levelClusters_same {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {z : ℝ} {A : Finset (Fin n)} (hA : A ∈ levelClusters T z)
    {e : Edge n} (hu : e.val.1 ∈ A) (he : (lcaSize T e : ℝ) ≤ z) : e.val.2 ∈ A := by
  obtain ⟨D, hD, huD, hvD, heq⟩ := hierarchy_lca_exists hT e
  have ha := Finset.mem_filter.mp hA
  rcases hT.nested ha.1 hD hu huD with hd | hd
  · have heD : (D.card : ℝ) ≤ z := by simpa [heq] using he
    exact (ha.2.2 D hD hd heD) ▸ hvD
  · exact hd hvD

lemma greedy_bounded_sum {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℝ)
    {z : ℝ} (hz : 0 ≤ z) (hf : ∀ i ∈ S, 0 ≤ f i ∧ f i ≤ z)
    (ht : z ≤ ∑ i ∈ S, f i) : ∃ R ⊆ S, z ≤ ∑ i ∈ R, f i ∧ (∑ i ∈ R, f i) ≤ 2 * z := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simpa using ht, by simp [hz]⟩
  | @insert i S hi ih =>
    by_cases hs : z ≤ ∑ j ∈ S, f j
    · obtain ⟨R, hR, hr⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) hs
      exact ⟨R, hR.trans (Finset.subset_insert _ _), hr⟩
    · refine ⟨insert i S, Finset.Subset.refl _, ht, ?_⟩
      rw [Finset.sum_insert hi]
      have hh := (hf i (Finset.mem_insert_self _ _)).2
      linarith

lemma levelClusters_inter_card {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {z : ℝ} (hz : 1 ≤ z) (A : Finset (Fin n)) :
    (∑ D ∈ levelClusters T z, ((A ∩ D).card : ℝ)) = A.card := by
  have he : (levelClusters T z).biUnion (fun D => A ∩ D) = A := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨D, hD, hv, _⟩; exact hv
    · intro hv
      obtain ⟨D, hD, hvD⟩ := levelClusters_cover hT hz v
      exact ⟨D, hD, hv, hvD⟩
  have hd : (levelClusters T z : Set (Finset (Fin n))).PairwiseDisjoint (fun D => A ∩ D) := by
    intro B hB C hC hne
    exact (levelClusters_disjoint hT z hB hC hne).mono Finset.inter_subset_right Finset.inter_subset_right
  have hh := Finset.card_biUnion hd
  rw [he] at hh
  exact_mod_cast hh.symm

/-- A union of threshold blocks gives a balanced cut without cutting any pair
whose least common ancestor has size at most the threshold. -/
lemma hierarchy_balanced_candidate {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    (A : Finset (Fin n)) {b : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 3)
    (hr : 1 ≤ b * A.card) :
    ∃ R, BalancedWithin b A R ∧ ∀ e : Edge n,
      ((e.val.1 ∈ R ∧ e.val.2 ∈ A \ R) ∨ (e.val.2 ∈ R ∧ e.val.1 ∈ A \ R)) →
      b * A.card < lcaSize T e := by
  let z : ℝ := b * A.card
  have hz : 0 ≤ z := le_trans (by norm_num) hr
  have ht : z ≤ ∑ D ∈ levelClusters T z, ((A ∩ D).card : ℝ) := by
    rw [levelClusters_inter_card hT hr]
    dsimp [z]
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  have hf : ∀ D ∈ levelClusters T z, 0 ≤ ((A ∩ D).card : ℝ) ∧ ((A ∩ D).card : ℝ) ≤ z := by
    intro D hD
    exact ⟨Nat.cast_nonneg _, (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)).trans
      (Finset.mem_filter.mp hD).2.1⟩
  obtain ⟨Q, hQ, hlo, hhi⟩ := greedy_bounded_sum (levelClusters T z) (fun D => ((A ∩ D).card : ℝ)) hz hf ht
  let R := Q.biUnion (fun D => A ∩ D)
  have hRA : R ⊆ A := Finset.biUnion_subset.mpr (fun _ _ => Finset.inter_subset_left)
  have hd : (Q : Set (Finset (Fin n))).PairwiseDisjoint (fun D => A ∩ D) := by
    intro B hB C hC hne
    exact (levelClusters_disjoint hT z (hQ hB) (hQ hC) hne).mono Finset.inter_subset_right Finset.inter_subset_right
  have hcard : (R.card : ℝ) = ∑ D ∈ Q, ((A ∩ D).card : ℝ) := by exact_mod_cast Finset.card_biUnion hd
  have htotal : ((A \ R).card : ℝ) = A.card - R.card := by
    rw [Finset.card_sdiff_of_subset hRA, Nat.cast_sub (Finset.card_le_card hRA)]
  refine ⟨R, ⟨hRA, by simpa [hcard] using hlo, ?_⟩, ?_⟩
  · rw [htotal, hcard]
    dsimp [z] at hhi
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  · intro e he
    by_contra hnot
    have hle : (lcaSize T e : ℝ) ≤ z := le_of_not_gt hnot
    rcases he with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · obtain ⟨D, hD, huAD⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨huA, huD⟩ := Finset.mem_inter.mp huAD
      have hvD := levelClusters_same hT (hQ hD) huD hle
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_biUnion.mpr
        ⟨D, hD, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hv).1, hvD⟩⟩)
    · obtain ⟨D, hD, hvAD⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨hvA, hvD⟩ := Finset.mem_inter.mp hvAD
      obtain ⟨L, hL, huL, hvL, heq⟩ := hierarchy_lca_exists hT e
      have hD' := Finset.mem_filter.mp (hQ hD)
      have huD : e.val.1 ∈ D := by
        rcases hT.nested hD'.1 hL hvD hvL with hs | hs
        · have hsize : (L.card : ℝ) ≤ z := by simpa [heq] using hle
          exact (hD'.2.2 L hL hs hsize) ▸ huL
        · exact hs huL
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr
        ⟨D, hD, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hu).1, huD⟩⟩)

end DPCut
