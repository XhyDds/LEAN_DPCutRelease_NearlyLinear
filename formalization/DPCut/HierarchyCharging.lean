import DPCut.HierarchySplitBound

/-! The charging argument: smaller-child sizes telescope along every leaf path. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

def splitSmall {n : ℕ} (T : Hierarchy n) (A : Finset (Fin n)) : ℝ :=
  if 2 ≤ A.card then min ((hierarchyChildren T A).1.card : ℝ) ((hierarchyChildren T A).2.card : ℝ) else 0

lemma splitSmall_nonneg {n : ℕ} (T : Hierarchy n) (A : Finset (Fin n)) : 0 ≤ splitSmall T A := by
  unfold splitSmall
  split_ifs <;> positivity

lemma splitSmall_split {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    splitSmall T A = min (B.card : ℝ) (C.card : ℝ) := by
  simp only [splitSmall, if_pos hs.internal]
  rcases hierarchyChildren_eq_or_swap hT hs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr]
  exact min_comm _ _

def vertexCharge {n : ℕ} (T : Hierarchy n) (b L : ℝ) (v : Fin n) (A : Finset (Fin n)) : ℝ :=
  ∑ D ∈ subtreeClusters T A, if v ∈ D ∧ b * D.card < L then splitSmall T D else 0

lemma vertexCharge_outside {n : ℕ} (T : Hierarchy n) (b L : ℝ) (v : Fin n)
    {A : Finset (Fin n)} (hv : v ∉ A) : vertexCharge T b L v A = 0 := by
  apply Finset.sum_eq_zero
  intro D hD
  have hn : v ∉ D := fun h => hv ((mem_subtreeClusters.mp hD).2 h)
  simp [hn]

lemma vertexCharge_split {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T) (b L : ℝ) (v : Fin n)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    vertexCharge T b L v A = (if v ∈ A ∧ b * A.card < L then splitSmall T A else 0) +
      vertexCharge T b L v B + vertexCharge T b L v C :=
  sum_subtreeClusters_split hT hs _

lemma vertexCharge_le_card {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    (b L : ℝ) (v : Fin n) {A : Finset (Fin n)} (hA : A ∈ T) :
    vertexCharge T b L v A ≤ A.card := by
  apply hierarchy_induction hT (fun A => vertexCharge T b L v A ≤ A.card) _ _ hA
  · intro u
    simp [vertexCharge, subtreeClusters_singleton hT, splitSmall]
  · intro A B C hs ihB ihC
    rw [vertexCharge_split hT b L v hs, splitSmall_split hT hs]
    have he : (A.card : ℝ) = B.card + C.card := by exact_mod_cast hs.card_eq
    have hmB := min_le_left (B.card : ℝ) (C.card : ℝ)
    have hmC := min_le_right (B.card : ℝ) (C.card : ℝ)
    by_cases hvB : v ∈ B
    · have hvC : v ∉ C := Finset.disjoint_left.mp hs.2.2.2.2.2.1 hvB
      rw [vertexCharge_outside T b L v hvC]
      split_ifs <;> nlinarith [Nat.cast_nonneg (α := ℝ) C.card]
    · rw [vertexCharge_outside T b L v hvB]
      split_ifs <;> nlinarith [Nat.cast_nonneg (α := ℝ) B.card]

lemma vertexCharge_le_threshold {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {b L : ℝ} (hb : 0 < b) (hL : 0 ≤ L) (v : Fin n)
    {A : Finset (Fin n)} (hA : A ∈ T) : vertexCharge T b L v A ≤ L / b := by
  apply hierarchy_induction hT (fun A => vertexCharge T b L v A ≤ L / b) _ _ hA
  · intro u
    simp only [vertexCharge, subtreeClusters_singleton hT, Finset.sum_singleton,
      splitSmall, Finset.card_singleton, show ¬ (2 ≤ 1) by omega, if_false, ite_self]
    positivity
  · intro A B C hs ihB ihC
    by_cases hc : v ∈ A ∧ b * A.card < L
    · exact (vertexCharge_le_card hT b L v hs.1).trans
        ((le_div_iff₀ hb).mpr (by nlinarith [hc.2]))
    · rw [vertexCharge_split hT b L v hs, if_neg hc, zero_add]
      by_cases hvB : v ∈ B
      · have hvC : v ∉ C := Finset.disjoint_left.mp hs.2.2.2.2.2.1 hvB
        simpa [vertexCharge_outside T b L v hvC] using ihB
      · simpa [vertexCharge_outside T b L v hvB] using ihC

lemma edge_charge_bound {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T)
    {b : ℝ} (hb : 0 < b) (Tstar : Hierarchy n) (e : Edge n) :
    (∑ A ∈ T, if e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize Tstar e
      then splitSmall T A else 0) ≤ lcaSize Tstar e / b := by
  calc
    _ ≤ vertexCharge T b (lcaSize Tstar e) e.val.1 Finset.univ := by
      simp only [vertexCharge, subtreeClusters_univ]
      apply Finset.sum_le_sum
      intro A hA
      by_cases hc : e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize Tstar e
      · simp [hc.1, hc.2.1, hc.2.2]
      · simp only [if_neg hc]
        split_ifs <;> first | exact le_refl _ | exact splitSmall_nonneg T A
    _ ≤ _ := vertexCharge_le_threshold hT hb (Nat.cast_nonneg _) _ hT.1

end DPCut
