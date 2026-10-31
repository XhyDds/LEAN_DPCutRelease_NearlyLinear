import DPCut.CCCalibration

/-! A single n-independent coefficient for all error terms in the CC reduction. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

theorem cc_total_error_bound_of_constant (releaseConstant : ℝ) (hrelease : 0 < releaseConstant) {γ η ε ρ θ C₀ : ℝ} (d₀ : ℕ)
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hη : 0 < η) (hε : 0 < ε)
    (hρ : 0 ≤ ρ) (hθ : θ < 1) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ n, 2 ≤ n →
      (ρ + 1) / (1 - θ) * ccTransferError n γ η (C₀ * n * Real.log n ^ d₀)
        (releaseConstant * mainError n (ccParameters n γ ε)) ((n : ℝ)⁻¹ ^ 10) ≤
          C * n * Real.log n ^ d := by
  obtain ⟨CA, hCA, hcap⟩ := cc_error_bound_of_constant releaseConstant hrelease hγ hγ4 hε
  let d := max d₀ 7
  let Q := (2 : ℝ) ^ d
  let C := (ρ + 1) / (1 - θ) * Q * ((1 + η) * (9 * γ * C₀ + 18 * CA) + 36 / η)
  have hden : 0 < 1 - θ := by linarith
  have hC : 0 < C := by dsimp [C, Q]; positivity
  refine ⟨C, d, hC, fun n hn => ?_⟩
  let V := (n : ℝ) * Real.log n ^ d
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have h₀ : C₀ * n * Real.log n ^ d₀ ≤ C₀ * Q * V := by
    have h := mul_le_mul_of_nonneg_left (log_power_domination hn (le_max_left d₀ 7))
      (show 0 ≤ C₀ * (n : ℝ) by positivity)
    convert h using 1
    dsimp [Q, V, d]
    ring
  have hA : releaseConstant * mainError n (ccParameters n γ ε) ≤ CA * Q * V := by
    apply (hcap n hn).trans
    have h := mul_le_mul_of_nonneg_left (log_power_domination hn (le_max_right d₀ 7))
      (show 0 ≤ CA * (n : ℝ) by positivity)
    convert h using 1
    dsimp [Q, V, d]
    ring
  have hlog : (n : ℝ) * Real.log n ≤ Q * V := by
    have h := mul_le_mul_of_nonneg_left (log_power_domination hn
      (show 1 ≤ d by dsimp [d]; omega)) (Nat.cast_nonneg n)
    simpa only [pow_one, Q, V, mul_assoc, mul_left_comm] using h
  have hR : 3 / η * (n * Real.log n + Real.log (2 / ((n : ℝ)⁻¹ ^ 10))) ≤ 36 / η * Q * V := by
    have h := mul_le_mul_of_nonneg_left (cc_rounding_threshold_bound hn)
      (show 0 ≤ 3 / η by positivity)
    have h' := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 36 / η by positivity)
    calc
      _ ≤ 3 / η * (12 * n * Real.log n) := h
      _ = 36 / η * (n * Real.log n) := by ring
      _ ≤ _ := by convert h' using 1; ring
  have hB : ccTransferError n γ η (C₀ * n * Real.log n ^ d₀)
      (releaseConstant * mainError n (ccParameters n γ ε)) ((n : ℝ)⁻¹ ^ 10) ≤
        Q * ((1 + η) * (9 * γ * C₀ + 18 * CA) + 36 / η) * V := by
    have hb := add_le_add (mul_le_mul_of_nonneg_left h₀ (show 0 ≤ 9 * γ by positivity))
      (mul_le_mul_of_nonneg_left hA (by norm_num : (0 : ℝ) ≤ 18))
    have h := add_le_add (mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 + η by positivity)) hR
    unfold ccTransferError
    convert h using 1
    ring
  have h := mul_le_mul_of_nonneg_left hB (show 0 ≤ (ρ + 1) / (1 - θ) by positivity)
  convert h using 1
  dsimp [C, V]
  ring

theorem cc_total_error_bound {γ η ε ρ θ C₀ : ℝ} (d₀ : ℕ)
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hη : 0 < η) (hε : 0 < ε)
    (hρ : 0 ≤ ρ) (hθ : θ < 1) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧ ∀ n, 2 ≤ n →
      (ρ + 1) / (1 - θ) * ccTransferError n γ η (C₀ * n * Real.log n ^ d₀)
        ((2 : ℝ) ^ 126 * mainError n (ccParameters n γ ε)) ((n : ℝ)⁻¹ ^ 10) ≤
          C * n * Real.log n ^ d :=
  cc_total_error_bound_of_constant ((2:ℝ)^126) (by positivity) d₀ hγ hγ4 hη hε hρ hθ hC₀

end DPCut
