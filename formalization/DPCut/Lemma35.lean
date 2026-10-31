import DPCut.HierarchyCharging

/-! Lemma 35: bicriteria balanced recursion. The constant is explicit and does
not depend on the balance of the returned cuts. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma between_comm {n : ℕ} (w : Weights n) (B C : Finset (Fin n)) :
    between w B C = between w C B := by
  unfold between
  apply Finset.sum_congr rfl
  intro e he
  congr 1
  apply propext
  tauto

def hierarchySplitCost {n : ℕ} (w : Weights n) (T : Hierarchy n) (A : Finset (Fin n)) : ℝ :=
  if 2 ≤ A.card then A.card * between w (hierarchyChildren T A).1 (hierarchyChildren T A).2 else 0

lemma hierarchySplitCost_split {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T)
    {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    hierarchySplitCost w T A = A.card * between w B C := by
  simp only [hierarchySplitCost, if_pos hs.internal]
  rcases hierarchyChildren_eq_or_swap hT hs with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> rw [hl, hr]
  rw [between_comm w C B]

lemma hcSubcost_splits {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T)
    {A : Finset (Fin n)} (hA : A ∈ T) :
    hcSubcost w T A = ∑ D ∈ subtreeClusters T A, hierarchySplitCost w T D := by
  apply hierarchy_induction hT (fun A => hcSubcost w T A =
    ∑ D ∈ subtreeClusters T A, hierarchySplitCost w T D) _ _ hA
  · intro v
    simp [hcSubcost_singleton, subtreeClusters_singleton hT, hierarchySplitCost]
  · intro A B C hs ihB ihC
    rw [hcSubcost_split w hT hs, sum_subtreeClusters_split hT hs,
      hierarchySplitCost_split w hT hs, ihB, ihC]
    ring

lemma hcCost_splits {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T) :
    hcCost w T = ∑ A ∈ T, hierarchySplitCost w T A := by
  simpa only [hcSubcost_univ, subtreeClusters_univ] using hcSubcost_splits w hT hT.1

lemma hierarchy_charging_bound {n : ℕ} {w : Weights n} (hw : Nonnegative w)
    {T Tstar : Hierarchy n} (hT : IsHierarchy T) (hstar : IsHierarchy Tstar)
    {b a : ℝ} (hb : 0 < b) (hb₁ : b ≤ 1 / 3) (ha : 1 ≤ a)
    (hrec : RecursiveApproximation w b a T) :
    hcCost w T ≤ (1 / b ^ 2) * a * hcCost w Tstar := by
  have hab : 0 ≤ a / b := div_nonneg (by linarith) hb.le
  have hone : hcCost w T ≤ (a / b) * ∑ A ∈ T, splitSmall T A * heavyMass w Tstar b A := by
    rw [hcCost_splits w hT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    by_cases hc : 2 ≤ A.card
    · have hs := hierarchyChildren_spec hT hA hc
      simpa only [hierarchySplitCost, splitSmall, if_pos hc, mul_assoc] using
        hierarchy_one_split hw hstar hb hb₁ ha hrec hs
    · simp [hierarchySplitCost, splitSmall, hc]
  have hswap : (∑ A ∈ T, splitSmall T A * heavyMass w Tstar b A) =
      ∑ e, w e * ∑ A ∈ T, if e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize Tstar e
        then splitSmall T A else 0 := by
    simp only [heavyMass, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.sum_congr rfl
    intro A hA
    split_ifs <;> ring
  rw [hswap] at hone
  have hsum : (∑ e, w e * ∑ A ∈ T,
      if e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize Tstar e then splitSmall T A else 0) ≤
      ∑ e, w e * (lcaSize Tstar e / b) :=
    Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (edge_charge_bound hT hb Tstar e) (hw e)
  apply hone.trans ((mul_le_mul_of_nonneg_left hsum hab).trans_eq ?_)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  unfold hcCost
  field_simp

lemma hcOptimum_exists {n : ℕ} (w : Weights n) {T : Hierarchy n} (hT : IsHierarchy T) :
    ∃ Tstar, IsHierarchy Tstar ∧ hcCost w Tstar = hcOptimum w :=
  ((show {T : Hierarchy n | IsHierarchy T}.Nonempty from ⟨T, hT⟩).image (hcCost w)).csInf_mem
    ((Set.toFinite _).image (hcCost w))

/-- The paper's bicriteria recursion lemma, with constant `1 / b²`. -/
theorem lemma35 : HCRecursionStatement := by
  intro b hb hb₁
  refine ⟨1 / b ^ 2, by positivity, ?_⟩
  intro b' a hb' hb'₁ ha n hn w T hw hT hrec
  obtain ⟨Tstar, hstar, heq⟩ := hcOptimum_exists w hT.1
  simpa only [heq] using hierarchy_charging_bound hw hT.1 hstar hb hb₁ ha hrec

end DPCut
