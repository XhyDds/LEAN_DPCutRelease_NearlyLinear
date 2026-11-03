import DPCut.BipartiteLowerBound
import DPCut.StarLowerBound
import DPCut.LowerCalibration
import DPCut.Statements

/-!
Theorem 38 (`thm:lower_bound`).
The discrepancy estimate is proved directly for a complete bipartite bit family;
the external EKKL discrepancy statement is not an assumption of this proof.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- An explicit uniform constant; graph-valuedness of the output is not needed. -/
theorem theorem38_explicit {n : ℕ} (hn : 33 ≤ n) {ε δ β γ A : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 ≤ δ) (hδε : δ ≤ ε / 100)
    (hβ : β ≤ 1 / 40) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 0 ≤ A)
    (M : Kernel (Weights n) (Weights n)) [IsMarkovKernel M]
    (hDP : EdgeDP M ε δ)
    (hacc : ∀ w : Weights n, Nonnegative w → HighProbability (M w) β
      (fun h => AllCuts w h γ A)) : lowerScale n ε γ ≤ 2 ^ 30 * A := by
  obtain ⟨t, ht, htlo, _, he, hd⟩ := lower_group_parameters hε hε1 hδ hδε
  have hti : 1 / ε ≤ 2 * (t : ℝ) := by
    have hh : 1 / ε = 2 * (1 / (2 * ε)) := by field_simp
    rw [hh]; linarith
  have hL : 0 ≤ lowerWidth n γ := lowerWidth_nonneg n hγ
  have hne : (0 : ℝ) ≤ (n : ℝ) / ε := by positivity
  rw [lowerScale_factor n hε]
  by_cases hsmall : γ ≤ 1 / 4096
  · obtain ⟨r, k, hr, hk, hfit, hnr, hsmallk, hwidth⟩ := lower_degree_choice hn hγ hsmall
    have hmain := bipartite_lower_bound hfit hr hk hδ hβ hγ hA hsmallk hDP hacc ht he hd
    have hprod := mul_le_mul (mul_le_mul hnr hti (by positivity) (by positivity))
      hwidth hL (by positivity : (0 : ℝ) ≤ 3 * r * (2 * t))
    simp only [one_div] at hprod
    have hu : ((n : ℝ) / ε) * lowerWidth n γ ≤ 24576 * ((t : ℝ) * r * k) := by
      simpa only [one_div, div_eq_mul_inv] using (show
        (n : ℝ) * ε⁻¹ * lowerWidth n γ ≤ 24576 * ((t : ℝ) * r * k) by nlinarith [hprod])
    have hg := mul_le_of_le_one_left (mul_nonneg hne hL) (by linarith : 1 - γ ≤ 1)
    have hbound : (1 - γ) * ((n : ℝ) / ε) * lowerWidth n γ ≤
        24576 * ((t : ℝ) * r * k) := by nlinarith [hg]
    norm_num
    nlinarith
  · have hγpos : 0 < γ := by linarith
    have hwidth : lowerWidth n γ ≤ 4096 := by
      have hh : 1 / γ ≤ 4096 := (div_le_iff₀ hγpos).2 (by linarith)
      exact (show lowerWidth n γ ≤ 1 / γ by simp [lowerWidth, ne_of_gt hγpos]).trans hh
    have hr : 0 < n - 1 := by omega
    have hfit : (n - 1) + 1 ≤ n := by omega
    have hnr : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n ≤ 2 * (n - 1) by omega)
    have hmain := star_lower_bound hfit hr hδ hβ hγ1 hDP hacc ht he hd
    have hprod := mul_le_mul (mul_le_mul hnr hti (by positivity) (by positivity))
      hwidth hL (by positivity : (0 : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) * (2 * t))
    simp only [one_div] at hprod
    have hu : ((n : ℝ) / ε) * lowerWidth n γ ≤ 16384 * ((t : ℝ) * (n - 1 : ℕ)) := by
      simpa only [one_div, div_eq_mul_inv] using (show
        (n : ℝ) * ε⁻¹ * lowerWidth n γ ≤ 16384 * ((t : ℝ) * (n - 1 : ℕ)) by nlinarith [hprod])
    have hg := mul_le_mul_of_nonneg_left hu (by linarith : 0 ≤ 1 - γ)
    norm_num
    nlinarith

/-- Theorem 38, with no assumptions beyond those of the paper. -/
theorem theorem38 : LowerBoundStatement := by
  refine ⟨1 / 2 ^ 30, by norm_num, ?_⟩
  intro n hn ε δ β γ A hε hε1 hδ hδε _hβ0 hβ hγ hγ1 hA M hM _hgraph hDP hacc
  letI : IsMarkovKernel M := hM
  have hh := theorem38_explicit hn hε hε1 hδ hδε hβ hγ hγ1 hA M hDP hacc
  norm_num at hh ⊢
  linarith

end DPCut
