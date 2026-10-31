import DPCut.Theorem34
import DPCut.HalfSubset

/-! Exact forms of the expansion and uniform-sparsity consequences in Appendix C.4. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

def normalizedOptimum {n : ℕ} (w : Weights n) (F : Set (Finset (Fin n)))
    (den : Finset (Fin n) → ℝ) : ℝ := sInf ((fun S => cut w S / den S) '' F)

lemma normalizedOptimum_exists {n : ℕ} (w : Weights n) {F : Set (Finset (Fin n))}
    (hF : F.Nonempty) (den : Finset (Fin n) → ℝ) :
    ∃ S ∈ F, cut w S / den S = normalizedOptimum w F den :=
  (hF.image _).csInf_mem ((Set.toFinite _).image _)

lemma normalizedOptimum_le {n : ℕ} (w : Weights n) {F : Set (Finset (Fin n))}
    (den : Finset (Fin n) → ℝ) {S : Finset (Fin n)} (hS : S ∈ F) :
    normalizedOptimum w F den ≤ cut w S / den S := csInf_le ((Set.toFinite _).image _).bddBelow ⟨S, hS, rfl⟩

lemma normalized_cut_accuracy {n : ℕ} {w h : Weights n} {η E L : ℝ}
    (hc : AllCuts w h η E) (hE : 0 ≤ E) (hL : 0 < L) (S : Finset (Fin n))
    (den : Finset (Fin n) → ℝ) (hden : L ≤ den S) :
    |cut w S / den S - cut h S / den S| ≤ η * (cut w S / den S) + E / L := by
  have hd := lt_of_lt_of_le hL hden
  rw [← sub_div, abs_div, abs_of_pos hd]
  have hh := div_le_div_of_nonneg_right (hc S) hd.le
  have he := div_le_div_of_nonneg_left hE hL hden
  calc
    _ ≤ (η * cut w S + E) / den S := hh
    _ = η * (cut w S / den S) + E / den S := by ring
    _ ≤ _ := add_le_add_left he _

lemma normalized_cut_transfer {n : ℕ} {w h : Weights n} {F : Set (Finset (Fin n))}
    (hF : F.Nonempty) (den : Finset (Fin n) → ℝ) {η E ρ L L' : ℝ}
    (hη : η < 1) (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hL : 0 < L) (hL' : 0 < L')
    (hden : ∀ S ∈ F, L ≤ den S) (hc : AllCuts w h η E)
    {S : Finset (Fin n)} (hout : L' ≤ den S)
    (happrox : cut h S / den S ≤ ρ * normalizedOptimum h F den) :
    cut w S / den S ≤ ρ * (1 + η) / (1 - η) * normalizedOptimum w F den +
      (ρ * (E / L) + E / L') / (1 - η) := by
  obtain ⟨Sstar, hstar, heq⟩ := normalizedOptimum_exists w hF den
  have h₁ := (abs_le.mp (normalized_cut_accuracy hc hE hL' S den hout)).2
  have h₂ := (abs_le.mp (normalized_cut_accuracy hc hE hL Sstar den (hden Sstar hstar))).1
  rw [heq] at h₂
  have hop := mul_le_mul_of_nonneg_left (normalizedOptimum_le h den hstar) hρ
  have hr := mul_le_mul_of_nonneg_left h₂ hρ
  have hh : cut w S / den S ≤
      (ρ * (1 + η) * normalizedOptimum w F den + ρ * (E / L) + E / L') / (1 - η) :=
    (le_div_iff₀ (sub_pos.mpr hη)).mpr (by nlinarith)
  convert hh using 1
  ring

lemma Balanced.expansion_denominator {n : ℕ} {b : ℝ} {S : Finset (Fin n)} (hS : Balanced b S) :
    b * n ≤ min (S.card : ℝ) (n - (S.card : ℝ)) := le_min hS.1 hS.2

lemma Balanced.sparsity_denominator {n : ℕ} {b : ℝ} {S : Finset (Fin n)} (hS : Balanced b S) :
    b * (1 - b) * (n : ℝ) ^ 2 ≤ (S.card : ℝ) * (n - (S.card : ℝ)) := by
  have hp := mul_nonneg (sub_nonneg.mpr hS.1) (sub_nonneg.mpr hS.2)
  nlinarith

lemma expansion_transfer {n : ℕ} {w h : Weights n} {η E ρ b c : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hc : 0 < c) (hη : η < 1) (hE : 0 ≤ E) (hρ : 0 ≤ ρ)
    (hF : {S : Finset (Fin n) | Balanced b S}.Nonempty)
    (hcuts : AllCuts w h η E) {S : Finset (Fin n)} (hS : Balanced c S)
    (happrox : expansion h S ≤ ρ * sInf (expansion h '' {R | Balanced b R})) :
    expansion w S ≤ ρ * (1 + η) / (1 - η) * sInf (expansion w '' {R | Balanced b R}) +
      (ρ * (E / (b * n)) + E / (c * n)) / (1 - η) := by
  exact normalized_cut_transfer hF (fun R => min (R.card : ℝ) (n - (R.card : ℝ))) hη hE hρ
    (mul_pos hb (by exact_mod_cast hn)) (mul_pos hc (by exact_mod_cast hn))
    (fun R hR => hR.expansion_denominator) hcuts hS.expansion_denominator happrox

lemma uniformSparsity_transfer {n : ℕ} {w h : Weights n} {η E ρ b c : ℝ}
    (hn : 0 < n) (hb : 0 < b) (hb₁ : b < 1) (hc : 0 < c) (hc₁ : c < 1)
    (hη : η < 1) (hE : 0 ≤ E) (hρ : 0 ≤ ρ)
    (hF : {S : Finset (Fin n) | Balanced b S}.Nonempty)
    (hcuts : AllCuts w h η E) {S : Finset (Fin n)} (hS : Balanced c S)
    (happrox : uniformSparsity h S ≤ ρ * sInf (uniformSparsity h '' {R | Balanced b R})) :
    uniformSparsity w S ≤ ρ * (1 + η) / (1 - η) * sInf (uniformSparsity w '' {R | Balanced b R}) +
      (ρ * (E / (b * (1 - b) * (n : ℝ) ^ 2)) + E / (c * (1 - c) * (n : ℝ) ^ 2)) / (1 - η) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbpos : 0 < 1 - b := sub_pos.mpr hb₁
  have hcpos : 0 < 1 - c := sub_pos.mpr hc₁
  exact normalized_cut_transfer hF (fun R => (R.card : ℝ) * (n - (R.card : ℝ))) hη hE hρ
    (by positivity) (by positivity) (fun R hR => hR.sparsity_denominator) hcuts hS.sparsity_denominator happrox

end DPCut
