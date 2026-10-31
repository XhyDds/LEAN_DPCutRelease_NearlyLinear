import DPCut.CutNormalization

/-! Converting a balanced expansion approximation to the other objectives in C.4. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def largeSide {n : ℕ} (S : Finset (Fin n)) : ℝ := max (S.card : ℝ) (n - (S.card : ℝ))

lemma largeSide_bounds {n : ℕ} (S : Finset (Fin n)) : (n : ℝ) / 2 ≤ largeSide S ∧ largeSide S ≤ n := by
  have hc : (S.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  have h₁ := le_max_left (S.card : ℝ) (n - (S.card : ℝ))
  have h₂ := le_max_right (S.card : ℝ) (n - (S.card : ℝ))
  exact ⟨by dsimp [largeSide]; linarith, max_le hc (by have := Nat.cast_nonneg (α := ℝ) S.card; linarith)⟩

lemma uniformSparsity_eq_expansion {n : ℕ} (w : Weights n) (S : Finset (Fin n)) :
    uniformSparsity w S = expansion w S / largeSide S := by
  unfold uniformSparsity expansion largeSide
  rw [div_div, min_mul_max]

lemma expansion_nonneg {n : ℕ} {w : Weights n} (hw : Nonnegative w) (S : Finset (Fin n)) :
    0 ≤ expansion w S := by
  have hc : (S.card : ℝ) ≤ n := by exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin n)
  exact div_nonneg (cut_nonneg hw S) (le_min (Nat.cast_nonneg _) (sub_nonneg.mpr hc))

lemma expansion_to_sparsity {n : ℕ} (hn : 0 < n) {w : Weights n} (hw : Nonnegative w)
    {b ρ : ℝ} (hρ : 0 ≤ ρ) (hF : {R : Finset (Fin n) | Balanced b R}.Nonempty)
    {S : Finset (Fin n)}
    (happrox : expansion w S ≤ ρ * sInf (expansion w '' {R | Balanced b R})) :
    uniformSparsity w S ≤ (2 * ρ) * sInf (uniformSparsity w '' {R | Balanced b R}) := by
  obtain ⟨R, hR, heq⟩ := (hF.image (uniformSparsity w)).csInf_mem ((Set.toFinite _).image _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hSpos : 0 < largeSide S := lt_of_lt_of_le (half_pos hn0) (largeSide_bounds S).1
  have hRpos : 0 < largeSide R := lt_of_lt_of_le (half_pos hn0) (largeSide_bounds R).1
  have hop : sInf (expansion w '' {R | Balanced b R}) ≤ expansion w R :=
    csInf_le ((Set.toFinite _).image _).bddBelow ⟨R, hR, rfl⟩
  have hcomp := happrox.trans (mul_le_mul_of_nonneg_left hop hρ)
  have hψpos : 0 ≤ uniformSparsity w R := by
    rw [uniformSparsity_eq_expansion]
    exact div_nonneg (expansion_nonneg hw R) hRpos.le
  have hφeq : expansion w R = uniformSparsity w R * largeSide R := by
    rw [uniformSparsity_eq_expansion, div_mul_cancel₀ _ hRpos.ne']
  have hφle := mul_le_mul_of_nonneg_left (largeSide_bounds R).2 hψpos
  rw [uniformSparsity_eq_expansion]
  apply (div_le_iff₀ hSpos).mpr
  rw [← heq]
  have hs := mul_le_mul_of_nonneg_left (largeSide_bounds S).1 (by positivity : 0 ≤ 2 * ρ * uniformSparsity w R)
  have hr := mul_le_mul_of_nonneg_left hφle hρ
  nlinarith

lemma expansion_to_cut {n : ℕ} (hn : 0 < n) {w : Weights n} (hw : Nonnegative w)
    {b c ρ : ℝ} (hb : 0 < b) (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hF : {R : Finset (Fin n) | Balanced b R}.Nonempty)
    {S : Finset (Fin n)} (hS : Balanced c S)
    (happrox : expansion w S ≤ ρ * sInf (expansion w '' {R | Balanced b R})) :
    cut w S ≤ (ρ / b) * constrainedOptimum w {R | Balanced b R} := by
  obtain ⟨R, hR, heq⟩ := constrainedOptimum_exists w hF
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hdenR := hR.expansion_denominator
  have hdenS := hS.expansion_denominator
  have hpR : 0 < min (R.card : ℝ) (n - (R.card : ℝ)) := lt_of_lt_of_le (mul_pos hb hn0) hdenR
  have hpS : 0 < min (S.card : ℝ) (n - (S.card : ℝ)) := lt_of_lt_of_le (mul_pos hc hn0) hdenS
  have hop : sInf (expansion w '' {R | Balanced b R}) ≤ expansion w R :=
    csInf_le ((Set.toFinite _).image _).bddBelow ⟨R, hR, rfl⟩
  have hφ : expansion w S ≤ ρ * (cut w R / (b * n)) :=
    happrox.trans ((mul_le_mul_of_nonneg_left hop hρ).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (cut_nonneg hw R) (mul_pos hb hn0) hdenR) hρ))
  have hdenle : min (S.card : ℝ) (n - (S.card : ℝ)) ≤ n :=
    (min_le_left _ _).trans (by exact_mod_cast (Finset.card_le_univ S).trans_eq (Fintype.card_fin n))
  have hcost : cut w S ≤ expansion w S * n := by
    have hh := mul_le_mul_of_nonneg_left hdenle (expansion_nonneg hw S)
    simpa only [expansion, div_mul_cancel₀ _ hpS.ne'] using hh
  have hh := mul_le_mul_of_nonneg_right hφ hn0.le
  have he : ρ * (cut w R / (b * n)) * n = (ρ / b) * cut w R := by field_simp
  rw [he, heq] at hh
  exact hcost.trans hh

end DPCut
