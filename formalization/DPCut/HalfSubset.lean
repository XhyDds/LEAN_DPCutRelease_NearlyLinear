import DPCut.HierarchyConstruction
import Mathlib.Data.Finset.Sort

/-! A public, deterministic balanced fallback cut, obtained by sorting and halving. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

def halfSubset {n : ℕ} (A : Finset (Fin n)) : Finset (Fin n) :=
  ((A.sort (· ≤ ·)).take (A.card / 2)).toFinset

lemma halfSubset_subset {n : ℕ} (A : Finset (Fin n)) : halfSubset A ⊆ A := by
  intro v hv
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take (List.mem_toFinset.mp hv))

lemma halfSubset_card {n : ℕ} (A : Finset (Fin n)) : (halfSubset A).card = A.card / 2 := by
  unfold halfSubset
  rw [List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take), List.length_take,
    Finset.length_sort, min_eq_left (Nat.div_le_self _ _)]

lemma halfSubset_sdiff_card {n : ℕ} (A : Finset (Fin n)) :
    (A \ halfSubset A).card = A.card - A.card / 2 := by
  rw [Finset.card_sdiff_of_subset (halfSubset_subset A), halfSubset_card]

lemma halfSubset_even {n : ℕ} (A : Finset (Fin n)) :
    (halfSubset A).card ≤ (A \ halfSubset A).card + 1 ∧
    (A \ halfSubset A).card ≤ (halfSubset A).card + 1 := by
  rw [halfSubset_card, halfSubset_sdiff_card]
  omega

lemma halfSubset_balanced {n : ℕ} {A : Finset (Fin n)} (hA : 2 ≤ A.card)
    {b : ℝ} (hb : b ≤ 1 / 3) : BalancedWithin b A (halfSubset A) := by
  refine ⟨halfSubset_subset A, ?_, ?_⟩
  · rw [halfSubset_card]
    have hh : A.card ≤ 3 * (A.card / 2) := by omega
    have hr : (A.card : ℝ) ≤ 3 * (A.card / 2 : ℕ) := by exact_mod_cast hh
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
  · rw [halfSubset_sdiff_card]
    have hh : A.card ≤ 3 * (A.card - A.card / 2) := by omega
    have hr : (A.card : ℝ) ≤ 3 * (A.card - A.card / 2 : ℕ) := by exact_mod_cast hh
    nlinarith [Nat.cast_nonneg (α := ℝ) A.card]

lemma BalancedWithin.split_data {n : ℕ} {A S : Finset (Fin n)} {b : ℝ}
    (h : BalancedWithin b A S) (hb : 0 < b) (hA : 2 ≤ A.card) :
    S.Nonempty ∧ (A \ S).Nonempty ∧ S.card < A.card ∧ (A \ S).card < A.card := by
  have hp : (0 : ℝ) < b * A.card := mul_pos hb (by exact_mod_cast (show 0 < A.card by omega))
  have hs : 0 < S.card := by exact_mod_cast (lt_of_lt_of_le hp h.2.1)
  have ht : 0 < (A \ S).card := by exact_mod_cast (lt_of_lt_of_le hp h.2.2)
  have he := Finset.card_sdiff_of_subset h.1
  exact ⟨Finset.card_pos.mp hs, Finset.card_pos.mp ht, by omega, by omega⟩

end DPCut
