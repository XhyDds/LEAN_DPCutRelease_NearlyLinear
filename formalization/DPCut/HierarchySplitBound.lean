import DPCut.HierarchyLevels

/-! The one-split charging inequality in Lemma 35. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut
attribute [local instance] Classical.propDecidable

lemma lcaSize_two_le {n : ℕ} {T : Hierarchy n} (hT : IsHierarchy T) (e : Edge n) :
    2 ≤ lcaSize T e := by
  obtain ⟨A, hA, hu, hv, he⟩ := hierarchy_lca_exists hT e
  rw [← he]
  exact Finset.one_lt_card.mpr ⟨e.val.1, hu, e.val.2, hv, ne_of_lt e.property⟩

def heavyMass {n : ℕ} (w : Weights n) (T : Hierarchy n) (b : ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ e, if e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize T e then w e else 0

lemma heavyMass_nonneg {n : ℕ} {w : Weights n} (hw : Nonnegative w)
    (T : Hierarchy n) (b : ℝ) (A : Finset (Fin n)) : 0 ≤ heavyMass w T b A := by
  apply Finset.sum_nonneg
  intro e he
  split_ifs <;> first | exact hw e | exact le_refl 0

lemma between_nonneg {n : ℕ} {w : Weights n} (hw : Nonnegative w) (A B : Finset (Fin n)) :
    0 ≤ between w A B := by
  apply Finset.sum_nonneg
  intro e he
  split_ifs <;> first | exact hw e | exact le_refl 0

lemma between_le_heavyMass {n : ℕ} {w : Weights n} (hw : Nonnegative w)
    (T : Hierarchy n) (b : ℝ) {A S : Finset (Fin n)} (hSA : S ⊆ A)
    (hh : ∀ e : Edge n, ((e.val.1 ∈ S ∧ e.val.2 ∈ A \ S) ∨
      (e.val.2 ∈ S ∧ e.val.1 ∈ A \ S)) → b * A.card < lcaSize T e) :
    between w S (A \ S) ≤ heavyMass w T b A := by
  apply Finset.sum_le_sum
  intro e he
  by_cases hc : (e.val.1 ∈ S ∧ e.val.2 ∈ A \ S) ∨ (e.val.2 ∈ S ∧ e.val.1 ∈ A \ S)
  · have ha : e.val.1 ∈ A ∧ e.val.2 ∈ A := hc.elim
      (fun h => ⟨hSA h.1, (Finset.mem_sdiff.mp h.2).1⟩)
      (fun h => ⟨(Finset.mem_sdiff.mp h.2).1, hSA h.1⟩)
    rw [if_pos hc, if_pos (show e.val.1 ∈ A ∧ e.val.2 ∈ A ∧ b * A.card < lcaSize T e from
      ⟨ha.1, ha.2, hh e hc⟩)]
  · simp only [if_neg hc]
    split_ifs <;> first | exact hw e | exact le_refl 0

lemma inducedExpansion_opt_le {n : ℕ} (w : Weights n) {b : ℝ}
    {A R : Finset (Fin n)} (hR : BalancedWithin b A R) :
    sInf (inducedExpansion w A '' {R | BalancedWithin b A R}) ≤ inducedExpansion w A R :=
  csInf_le ((Set.toFinite _).image _).bddBelow ⟨R, hR, rfl⟩

lemma hierarchy_one_split {n : ℕ} {w : Weights n} (hw : Nonnegative w)
    {T Tstar : Hierarchy n} (hstar : IsHierarchy Tstar) {b a : ℝ}
    (hb : 0 < b) (hb₁ : b ≤ 1 / 3) (ha : 1 ≤ a)
    (hrec : RecursiveApproximation w b a T) {A B C : Finset (Fin n)} (hs : IsSplit T A B C) :
    A.card * between w B C ≤ (a / b) * min (B.card : ℝ) (C.card : ℝ) * heavyMass w Tstar b A := by
  have hr : (0 : ℝ) < A.card := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hs.internal)
  have hbpos : (0 : ℝ) < B.card := by exact_mod_cast hs.2.2.2.1.card_pos
  have hcpos : (0 : ℝ) < C.card := by exact_mod_cast hs.2.2.2.2.1.card_pos
  have hspos := lt_min hbpos hcpos
  have hsone : (1 : ℝ) ≤ min (B.card : ℝ) (C.card : ℝ) := by
    exact le_min (by exact_mod_cast hs.2.2.2.1.card_pos) (by exact_mod_cast hs.2.2.2.2.1.card_pos)
  have hmass := heavyMass_nonneg hw Tstar b A
  by_cases hlarge : 1 / b ≤ (A.card : ℝ)
  · have hbr : 1 ≤ b * A.card := by have := (div_le_iff₀ hb).mp hlarge; nlinarith
    obtain ⟨R, hR, hheavy⟩ := hierarchy_balanced_candidate hstar A hb hb₁ hbr
    have hden : b * A.card ≤ min (R.card : ℝ) ((A \ R).card : ℝ) := le_min hR.2.1 hR.2.2
    have hdenpos : 0 < min (R.card : ℝ) ((A \ R).card : ℝ) := lt_of_lt_of_le (mul_pos hb hr) hden
    have hcand : inducedExpansion w A R ≤ heavyMass w Tstar b A / (b * A.card) := by
      unfold inducedExpansion
      exact (div_le_div_of_nonneg_right (between_le_heavyMass hw Tstar b hR.1 hheavy) hdenpos.le).trans
        (div_le_div_of_nonneg_left hmass (mul_pos hb hr) hden)
    have happrox := hrec A B C hs
    rw [if_pos hlarge] at happrox
    have hbound := happrox.trans ((mul_le_mul_of_nonneg_left (inducedExpansion_opt_le w hR) (by linarith)).trans
      (mul_le_mul_of_nonneg_left hcand (by linarith)))
    simp only [inducedExpansion, ← hs.right_eq_sdiff] at hbound
    rw [← mul_div_assoc] at hbound
    have hh := (div_le_div_iff₀ hspos (mul_pos hb hr)).mp hbound
    have hd := div_le_div_of_nonneg_right hh hb.le
    convert hd using 1 <;> field_simp
  · have hbr : b * A.card < 1 := by have := (lt_div_iff₀ hb).mp (lt_of_not_ge hlarge); nlinarith
    have hbetween : between w B C ≤ heavyMass w Tstar b A := by
      rw [hs.right_eq_sdiff]
      apply between_le_heavyMass hw Tstar b hs.left_subset
      intro e he
      have hl : (2 : ℝ) ≤ lcaSize Tstar e := by exact_mod_cast lcaSize_two_le hstar e
      linarith
    have hscale : (A.card : ℝ) ≤ (a / b) * min (B.card : ℝ) (C.card : ℝ) := by
      have h₁ : (A.card : ℝ) ≤ 1 / b := le_of_lt (lt_of_not_ge hlarge)
      have h₂ : (1 : ℝ) ≤ a * min (B.card : ℝ) (C.card : ℝ) := by nlinarith
      have h₃ := div_le_div_of_nonneg_right h₂ hb.le
      calc
        _ ≤ 1 / b := h₁
        _ ≤ (a * min (B.card : ℝ) (C.card : ℝ)) / b := h₃
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_left hbetween hr.le).trans (mul_le_mul_of_nonneg_right hscale hmass)

end DPCut
