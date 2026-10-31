import DPCut.HierarchyCost

/-! Uniform preservation of hierarchy cost by simultaneous cut preservation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma hierarchyTerm_transfer {n : ℕ} {w h : Weights n} {T : Hierarchy n}
    (hT : IsHierarchy T) {η E : ℝ} (hcuts : AllCuts w h η E)
    {A : Finset (Fin n)} (hA : A ∈ T) :
    |hierarchyTerm h T A - hierarchyTerm w T A| ≤ η * hierarchyTerm w T A +
      E * (if 2 ≤ A.card then (A.card : ℝ) else 0) := by
  by_cases hc : 2 ≤ A.card
  · have hs := hierarchyChildren_spec hT hA hc
    have hb := hcuts (hierarchyChildren T A).1
    have hd := hcuts (hierarchyChildren T A).2
    rw [abs_sub_comm] at hb hd
    have hb' := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (hierarchyChildren T A).2.card : (0 : ℝ) ≤ _)
    have hd' := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg (hierarchyChildren T A).1.card : (0 : ℝ) ≤ _)
    have hcard : (A.card : ℝ) = (hierarchyChildren T A).1.card + (hierarchyChildren T A).2.card :=
      by exact_mod_cast hs.card_eq
    simp only [hierarchyTerm, if_pos hc]
    have he : (hierarchyChildren T A).2.card * cut h (hierarchyChildren T A).1 +
        (hierarchyChildren T A).1.card * cut h (hierarchyChildren T A).2 -
        ((hierarchyChildren T A).2.card * cut w (hierarchyChildren T A).1 +
        (hierarchyChildren T A).1.card * cut w (hierarchyChildren T A).2) =
        (hierarchyChildren T A).2.card * (cut h (hierarchyChildren T A).1 - cut w (hierarchyChildren T A).1) +
        (hierarchyChildren T A).1.card * (cut h (hierarchyChildren T A).2 - cut w (hierarchyChildren T A).2) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)]
    rw [hcard]
    nlinarith
  · simp [hierarchyTerm, hc]

lemma hierarchy_transfer {n : ℕ} {w h : Weights n} {T : Hierarchy n}
    (hT : IsHierarchy T) {η E : ℝ} (hcuts : AllCuts w h η E) :
    |hcCost h T - hcCost w T| ≤ η * hcCost w T +
      E / 2 * (n + ∑ A ∈ T.filter (fun A => 2 ≤ A.card), (A.card : ℝ)) := by
  have ht : |(∑ A ∈ T, hierarchyTerm h T A) - ∑ A ∈ T, hierarchyTerm w T A| ≤
      η * (∑ A ∈ T, hierarchyTerm w T A) +
      E * ∑ A ∈ T.filter (fun A => 2 ≤ A.card), (A.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ A ∈ T, (η * hierarchyTerm w T A + E * (if 2 ≤ A.card then (A.card : ℝ) else 0)) :=
        Finset.sum_le_sum fun A hA => hierarchyTerm_transfer hT hcuts hA
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_filter]
  have hl : |(∑ v : Fin n, cut h {v}) - ∑ v : Fin n, cut w {v}| ≤
      η * (∑ v : Fin n, cut w {v}) + E * n := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ v : Fin n, (η * cut w {v} + E) := Finset.sum_le_sum fun v _ => by
        simpa only [abs_sub_comm] using hcuts {v}
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, mul_comm]
  have he : 2 * (hcCost h T - hcCost w T) =
      ((∑ A ∈ T, hierarchyTerm h T A) - ∑ A ∈ T, hierarchyTerm w T A) +
      ((∑ v : Fin n, cut h {v}) - ∑ v : Fin n, cut w {v}) := by
    linarith [hcCost_boundary h hT, hcCost_boundary w hT]
  have ha := abs_add_le ((∑ A ∈ T, hierarchyTerm h T A) - ∑ A ∈ T, hierarchyTerm w T A)
      ((∑ v : Fin n, cut h {v}) - ∑ v : Fin n, cut w {v})
  rw [← he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ha
  nlinarith [congrArg (fun x : ℝ => η * x) (hcCost_boundary w hT)]

/-- Equation (hc-uniform-transfer), with the exact additive coefficient. -/
theorem hc_uniform_transfer : HCTransferStatement := by
  intro n hn w h T η E hw hh hT hη hE hcuts
  exact hierarchy_transfer hT hcuts

end DPCut
