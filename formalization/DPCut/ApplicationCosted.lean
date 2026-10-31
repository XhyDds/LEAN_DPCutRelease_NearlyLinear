import DPCut.CostedAmplification
import DPCut.ApplicationRuntimeBounds
import DPCut.CCReductionKernel
import DPCut.ExternalApplicationContracts

/-! Shared cost bounds for external application algorithms and amplification.
The costed private reductions are implemented in `LSWApplicationCosted`. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DPCut

lemma graph_algorithm_cost_polynomial {Output : ℕ → Type} [∀ n, MeasurableSpace (Output n)]
    (alg : PolynomialGraphAlgorithm Output) :
    PolynomialVertexBound (fun n => ENNReal.ofReal (alg.coefficient * (1 + (n : ℝ)) ^ alg.degree)) :=
  ⟨alg.coefficient, alg.coefficient_pos, alg.degree, fun _ _ => le_refl _⟩

lemma amplification_repetitions_polynomial {s : ℝ} (hs : 0 < s) :
    PolynomialVertexBound (fun n => (⌈Real.log (1 / ((n : ℝ)⁻¹ ^ 10)) / s⌉₊ : ℝ≥0∞)) := by
  refine ⟨10 / s + 1, by positivity, 1, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have he : Real.log (1 / ((n : ℝ)⁻¹ ^ 10)) / s = 10 * Real.log n / s := by
    rw [one_div, Real.log_inv, Real.log_pow, Real.log_inv]
    ring
  dsimp only
  rw [he]
  have hceil := Nat.ceil_lt_add_one (div_nonneg (by positivity) hs.le : 0 ≤ 10 * Real.log n / s)
  have hlogle := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (Real.log_le_self (Nat.cast_nonneg n)) (by norm_num : (0 : ℝ) ≤ 10)) hs.le
  have hh : (⌈10 * Real.log n / s⌉₊ : ℝ) ≤ (10 / s + 1) * (1 + n) ^ 1 := by
    rw [pow_one]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hp : 0 < 10 / s := by positivity
    simp only [div_eq_mul_inv] at hceil hlogle hp ⊢
    nlinarith
  simpa using ENNReal.ofReal_le_ofReal hh

end DPCut
