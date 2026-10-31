import DPCut.OuterProgress
import DPCut.CappedSimplex

/-! Internal deterministic estimates for the capped variant in Lemma 29. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace DPCut

def lowerBiasedMass (capacity trueMass noise τ : ℝ) : ℝ :=
  max 0 (min capacity (trueMass + noise - τ))

lemma lowerBiasedMass_bounds {capacity M noise τ : ℝ} (hc : 0 ≤ capacity) :
    0 ≤ lowerBiasedMass capacity M noise τ ∧ lowerBiasedMass capacity M noise τ ≤ capacity :=
  ⟨le_max_left _ _, max_le hc (min_le_left _ _)⟩

lemma lowerBiasedMass_good {capacity M noise τ : ℝ}
    (hM : 0 ≤ M) (hcap : M ≤ capacity) (hnoise : |noise| ≤ τ) :
    M - 2 * τ ≤ lowerBiasedMass capacity M noise τ ∧ lowerBiasedMass capacity M noise τ ≤ M := by
  have hn := abs_le.mp hnoise
  have ht := le_trans (abs_nonneg noise) hnoise
  constructor
  · apply le_trans _ (le_max_right _ _)
    exact le_min (by linarith) (by linarith)
  · exact max_le hM ((min_le_right _ _).trans (by linarith))

lemma capped_continuing_mass {M H B τ γ : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B)
    (hτ : 0 ≤ τ) (hgood : M - 2 * τ ≤ H ∧ H ≤ M)
    (hcont : 100 * (B + τ / γ) < H) :
    0 < H ∧ 0 < M ∧ H ≤ M ∧ (1 - γ / 50) * M ≤ H ∧ B ≤ M / 100 := by
  have hdiv : 0 ≤ τ / γ := div_nonneg hτ hγ.le
  have hH : 0 < H := by linarith
  have hM : 0 < M := hH.trans_le hgood.2
  have ht : τ / γ < M / 100 := by linarith
  have ht' := (div_lt_iff₀ hγ).mp ht
  refine ⟨hH, hM, hgood.2, ?_, ?_⟩ <;> nlinarith

lemma capped_minus_normalized_gap {γ M H x y : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4)
    (hM : 0 < M) (hH : 0 < H) (hMH : (1 - γ / 50) * M ≤ H)
    (hx : H ≤ 3 * x) (hy : x ≤ (1 - γ) * y) :
    γ / (4 * (1 + γ)) ≤ y / M - x / H := by
  have hx3 : (1 / 3 : ℝ) ≤ x / H := (le_div_iff₀ hH).mpr (by linarith)
  have hx0 : 0 ≤ x / H := by linarith
  have hxq : H * (x / H) = x := mul_div_cancel₀ _ hH.ne'
  have hyq : M * (y / M) = y := mul_div_cancel₀ _ hM.ne'
  have hr := mul_le_mul_of_nonneg_right hMH hx0
  have hab : (1 - γ / 50) * (x / H) ≤ (1 - γ) * (y / M) := by
    apply (mul_le_mul_iff_right₀ hM).mp
    have hyq' := congrArg (fun z => (1 - γ) * z) hyq
    nlinarith only [hy, hxq, hr, hyq']
  have hd : 0 < 150 * (1 - γ) := by linarith
  have hgap : 49 * γ / (150 * (1 - γ)) ≤ y / M - x / H := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx3 hγ.le]
  apply le_trans _ hgap
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (1 + γ)) hd).mpr
  nlinarith [sq_nonneg γ]

lemma capped_plus_normalized_gap {γ M H x y : ℝ} (hγ : 0 < γ) (hM : 0 < M) (hH : 0 < H)
    (hHM : H ≤ M) (hx : H ≤ 3 * x) (hy : (1 + γ) * y ≤ x) :
    γ / (4 * (1 + γ)) ≤ x / H - y / M := by
  apply plus_normalized_gap hγ hM hH _ hx hy
  have hh := mul_nonneg (div_nonneg hγ.le (by norm_num : (0 : ℝ) ≤ 4)) hM.le
  nlinarith

theorem capped_residual_contraction {n : ℕ} {w h : Weights n} {a : Aggregate n} {γ B : ℝ}
    (hw : Nonnegative w) (hh : Nonnegative h) (ha : a.Partition)
    (hacc : a.Accurate w h γ B) (haccept : a.Accepts h)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) (hB : 0 ≤ B)
    (hlarge : 100 * B ≤ mass w) (hMH : (1 - γ / 50) * mass w ≤ mass h) :
    mass (residualUpdate w a.residual) ≤ (19 / 20 : ℝ) * mass w := by
  have hsum := ha.pairing_mass h
  have hdom := max_le_iff.mp haccept
  have hwR : Nonnegative (hadamard w a.residual) := fun e => mul_nonneg (hw e) (ha.2.2.1 e).1
  have hhR : Nonnegative (hadamard h a.residual) := fun e => mul_nonneg (hh e) (ha.2.2.1 e).1
  have hm := mass_from_cuts n _ _ γ B hwR hhR hγ.le hB hacc.2.2
  change |pairing w a.residual - pairing h a.residual| ≤ γ * pairing w a.residual + 2 * B at hm
  have hr : 0 ≤ pairing w a.residual := Finset.sum_nonneg fun e _ => hwR e
  have hmw : 0 ≤ mass w := Finset.sum_nonneg fun e _ => hw e
  have hu := (abs_le.mp hm).1
  rw [mass_residualUpdate]
  nlinarith [mul_le_mul_of_nonneg_right hγ1 hr, mul_le_mul_of_nonneg_right hγ1 hmw]

end DPCut
