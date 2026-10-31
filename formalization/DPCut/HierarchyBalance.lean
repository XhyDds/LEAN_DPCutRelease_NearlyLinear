import DPCut.HierarchyTransfer

/-! Entropy telescoping bounds the accumulated additive error in balanced trees. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma balanced_entropy_split {b r s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (he : r = s + t) (hbs : b * r ≤ s) (hbt : b * r ≤ t) :
    b * r + s * Real.log s + t * Real.log t ≤ r * Real.log r := by
  have hr : 0 < r := by linarith
  have log_bound (u v : ℝ) (hu : 0 < u) (huv : r = u + v) (hbv : b * r ≤ v) :
      Real.log u ≤ Real.log r - b := by
    have hq : u / r ≤ 1 - b := (div_le_iff₀ hr).mpr (by nlinarith)
    have hl := Real.log_le_sub_one_of_pos (div_pos hu hr)
    rw [Real.log_div hu.ne' hr.ne'] at hl
    linarith
  have hl₁ := mul_le_mul_of_nonneg_left (log_bound s t hs he hbt) hs.le
  have hl₂ := mul_le_mul_of_nonneg_left (log_bound t s ht (by linarith) hbs) ht.le
  rw [he] at *
  nlinarith

def internalMass {n : ℕ} (T : Hierarchy n) (A : Finset (Fin n)) : ℝ :=
  ∑ D ∈ subtreeClusters T A, if 2 ≤ D.card then (D.card : ℝ) else 0

lemma balanced_internalMass {n : ℕ} {T : Hierarchy n} {b : ℝ}
    (hT : BalancedHierarchy b T) {A : Finset (Fin n)} (hA : A ∈ T) :
    b * internalMass T A ≤ A.card * Real.log A.card := by
  apply hierarchy_induction hT.1 (fun A => b * internalMass T A ≤ A.card * Real.log A.card) _ _ hA
  · intro v
    simp [internalMass, subtreeClusters_singleton hT.1]
  · intro A B C hs ihB ihC
    have hsum : internalMass T A = A.card + internalMass T B + internalMass T C := by
      simpa only [internalMass, if_pos hs.internal] using sum_subtreeClusters_split hT.1 hs
        (fun D => if 2 ≤ D.card then (D.card : ℝ) else 0)
    have hpB : (0 : ℝ) < B.card := by exact_mod_cast hs.2.2.2.1.card_pos
    have hpC : (0 : ℝ) < C.card := by exact_mod_cast hs.2.2.2.2.1.card_pos
    have he : (A.card : ℝ) = B.card + C.card := by exact_mod_cast hs.card_eq
    obtain ⟨hbB, hbC⟩ := hT.2 A B C hs
    have hh := balanced_entropy_split hpB hpC he hbB hbC
    rw [hsum]
    nlinarith

lemma balanced_internal_sum {n : ℕ} {T : Hierarchy n} {b : ℝ}
    (hT : BalancedHierarchy b T) (hb : 0 < b) :
    (∑ A ∈ T.filter (fun A => 2 ≤ A.card), (A.card : ℝ)) ≤ n * Real.log n / b := by
  apply (le_div_iff₀ hb).mpr
  simpa [internalMass, subtreeClusters_univ, Finset.sum_filter, mul_comm]
    using balanced_internalMass hT hT.1.1

lemma hc_balanced_transfer {n : ℕ} {w h : Weights n} {T : Hierarchy n} {b η E : ℝ}
    (hT : BalancedHierarchy b T) (hb : 0 < b) (hE : 0 ≤ E) (hcuts : AllCuts w h η E) :
    |hcCost h T - hcCost w T| ≤ η * hcCost w T + E / 2 * (n + n * Real.log n / b) := by
  apply (hierarchy_transfer hT.1 hcuts).trans
  gcongr
  exact balanced_internal_sum hT hb

end DPCut
