import DPCut.CutBasics

/-! Relating disjoint rectangles to simultaneous boundary-cut accuracy. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

lemma two_between_eq_cuts {n : ℕ} (w : Weights n) {S T : Finset (Fin n)}
    (h : Disjoint S T) : 2 * between w S T = cut w S + cut w T - cut w (S ∪ T) := by
  classical
  simp only [between, cut, pairing, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have h₁ : e.val.1 ∈ S → e.val.1 ∉ T := fun hs => Finset.disjoint_left.mp h hs
  have h₂ : e.val.2 ∈ S → e.val.2 ∉ T := fun hs => Finset.disjoint_left.mp h hs
  by_cases hs₁ : e.val.1 ∈ S <;> by_cases ht₁ : e.val.1 ∈ T <;>
    by_cases hs₂ : e.val.2 ∈ S <;> by_cases ht₂ : e.val.2 ∈ T <;>
    simp_all [cutQuery] <;> ring

lemma between_sub {n : ℕ} (w w' : Weights n) (S T : Finset (Fin n)) :
    between (w - w') S T = between w S T - between w' S T := by
  simp only [between, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _; split <;> simp

lemma compatible_between_bound {n : ℕ} {w w' h : Weights n} {γ A : ℝ}
    (hw : Nonnegative w) (hw' : Nonnegative w') (hγ : 0 ≤ γ)
    (hc : AllCuts w h γ A) (hc' : AllCuts w' h γ A)
    {S T : Finset (Fin n)} (hST : Disjoint S T) :
    |between w S T - between w' S T| ≤ 3 / 2 * γ * (mass w + mass w') + 3 * A := by
  have hb (U : Finset (Fin n)) : |cut w U - cut w' U| ≤
      γ * (mass w + mass w') + 2 * A := by
    have hh := (abs_sub_le (cut w U) (cut h U) (cut w' U)).trans
      (add_le_add (hc U) (by simpa only [abs_sub_comm] using hc' U))
    have h₁ := mul_le_mul_of_nonneg_left (cut_le_mass hw U) hγ
    have h₂ := mul_le_mul_of_nonneg_left (cut_le_mass hw' U) hγ
    linarith
  have he : 2 * (between w S T - between w' S T) =
      (cut w S - cut w' S) + (cut w T - cut w' T) - (cut w (S ∪ T) - cut w' (S ∪ T)) := by
    linarith [two_between_eq_cuts w hST, two_between_eq_cuts w' hST]
  have ht : |(cut w S - cut w' S) + (cut w T - cut w' T) -
      (cut w (S ∪ T) - cut w' (S ∪ T))| ≤
      |cut w S - cut w' S| + |cut w T - cut w' T| + |cut w (S ∪ T) - cut w' (S ∪ T)| :=
    (abs_sub _ _).trans (add_le_add_right (abs_add_le _ _) _)
  rw [← he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  linarith [hb S, hb T, hb (S ∪ T)]

end DPCut
