import DPCut.LaplaceTail
import DPCut.FailureProbability

/-! The joint noisy-mass good event and continuing-round mass comparisons. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DPCut

lemma laplace_interval_failure {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β < 1) :
    let τ := Real.log (1 / β) / ε
    laplace (1 / ε) (Icc (-τ) τ)ᶜ ≤ ENNReal.ofReal β := by
  dsimp
  let τ := Real.log (1 / β) / ε
  obtain ⟨hτ, hu, _⟩ := laplace_calibrated_tails hε hβ hβ1
  change 0 < τ at hτ
  change prob (laplace (1 / ε)) (Ioi τ) = β / 2 at hu
  have hl : prob (laplace (1 / ε)) (Iic (-τ)) = β / 2 := by
    rw [laplace_lower_tail (one_div_pos.mpr hε) hτ.le,
      ← laplace_upper_tail (one_div_pos.mpr hε) hτ.le, hu]
  letI := laplace_isProbabilityMeasure (one_div_pos.mpr hε)
  apply (prob_le_iff_measure_le hβ.le).mp
  have hsub : (Icc (-τ) τ)ᶜ ⊆ Iic (-τ) ∪ Ioi τ := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iic, mem_Ioi] at hx ⊢
    exact hx.imp le_of_lt id
  have hb := (measureReal_mono (μ := laplace (1 / ε)) hsub).trans (measureReal_union_le _ _)
  change prob _ _ ≤ prob _ (Iic (-τ)) + prob _ (Ioi τ) at hb
  linarith

lemma shifted_mass_bounds {M τ z : ℝ} (hM : 0 ≤ M) (hz : z ∈ Icc (-τ) τ) :
    M ≤ max 0 (M + z + τ) ∧ max 0 (M + z + τ) ≤ M + 2 * τ := by
  have hz0 : 0 ≤ M + z + τ := by linarith [hz.1]
  rw [max_eq_right hz0]
  constructor <;> linarith [hz.1, hz.2]

lemma continuing_mass_bounds {M H B τ γ S : ℝ} (hB : 0 ≤ B) (hτ : 0 ≤ τ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (_hMH : M ≤ H) (hHM : H ≤ M + 2 * τ)
    (hS : 10 * (B + τ / γ) ≤ S) (hcontinue : S < H) :
    0 < M ∧ 0 < H ∧ B ≤ M ∧ H ≤ (1 + γ / 4) * M := by
  have hτγ : τ ≤ τ / γ := (le_div_iff₀ hγ).mpr
    (mul_le_of_le_one_right hτ (by linarith))
  have hτγ0 : 0 ≤ τ / γ := div_nonneg hτ hγ.le
  have hM : 10 * B + 8 * (τ / γ) < M := by linarith
  have hMq : 8 * (τ / γ) < M := by linarith
  have hmul := mul_lt_mul_of_pos_left hMq hγ
  have hcancel : γ * (τ / γ) = τ := mul_div_cancel₀ _ hγ.ne'
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  nlinarith

end DPCut
