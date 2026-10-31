import DPCut.Definitions

/-! Explicit degree choice and the gamma = 0 convention in the lower-bound scale. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

def lowerWidth (n : ℕ) (γ : ℝ) : ℝ :=
  if γ = 0 then Real.sqrt n else min (Real.sqrt n) (1 / γ)

lemma lowerWidth_nonneg (n : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) : 0 ≤ lowerWidth n γ := by
  unfold lowerWidth
  split_ifs <;> positivity

lemma lowerScale_factor (n : ℕ) {ε γ : ℝ} (hε : 0 < ε) :
    lowerScale n ε γ = (1 - γ) * ((n : ℝ) / ε) * lowerWidth n γ := by
  unfold lowerScale lowerWidth
  split_ifs with h
  · ring
  · have he₁ : (n : ℝ) * Real.sqrt n / ε = (n / ε) * Real.sqrt n := by ring
    have he₂ : (n : ℝ) / (ε * γ) = (n / ε) * (1 / γ) := by
      simp [div_eq_mul_inv]; ring
    rw [he₁, he₂, ← mul_min_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ n / ε)]
    ring

/-- A square right side keeps sqrt(d) exact; the constants are intentionally coarse. -/
lemma lower_degree_choice {n : ℕ} (hn : 33 ≤ n) {γ : ℝ}
    (hγ : 0 ≤ γ) (hsmall : γ ≤ 1 / 4096) :
    ∃ r k : ℕ, 0 < r ∧ 0 < k ∧ r + k ^ 2 ≤ n ∧
      (n : ℝ) ≤ 3 * r ∧ γ * k ≤ 1 / 2048 ∧ lowerWidth n γ ≤ 4096 * k := by
  have hnr : (33 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
  have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
  have hsqrt2 : 2 ≤ Real.sqrt n / 2 := by nlinarith
  let s : ℝ := if γ = 0 then Real.sqrt n / 2 else min (Real.sqrt n / 2) (1 / (2048 * γ))
  have hs : 2 ≤ s := by
    dsimp [s]
    split_ifs with hz
    · exact hsqrt2
    · apply le_min hsqrt2
      have hg : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hz)
      apply (le_div_iff₀ (by positivity)).2
      linarith
  have hsupper : s ≤ Real.sqrt n / 2 := by
    dsimp [s]; split_ifs <;> simp
  let k : ℕ := ⌊s⌋₊
  have hk : 1 ≤ k := (Nat.le_floor_iff (by linarith : 0 ≤ s)).2 (by norm_num; linarith)
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkupper : (k : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hks : s ≤ 2 * k := by have hh := Nat.lt_floor_add_one s; dsimp [k]; linarith
  have hksq : ((k ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) / 4 := by
    push_cast
    nlinarith
  have hgamma : γ * k ≤ 1 / 2048 := by
    by_cases hz : γ = 0
    · simp [hz]
    · have hg : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hz)
      have hki : (k : ℝ) ≤ 1 / (2048 * γ) := hkupper.trans (by simp [s, hz])
      have hh := (le_div_iff₀ (by positivity : 0 < 2048 * γ)).mp hki
      nlinarith
  have hwidth : lowerWidth n γ ≤ 4096 * k := by
    by_cases hz : γ = 0
    · simp only [lowerWidth, hz, ↓reduceIte]
      have hh : Real.sqrt n / 2 ≤ 2 * k := by simpa [s, hz] using hks
      nlinarith
    · have hg : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hz)
      have hL₁ : lowerWidth n γ ≤ Real.sqrt n := by simp [lowerWidth, hz]
      have hL₂ : lowerWidth n γ ≤ 1 / γ := by simp [lowerWidth, hz]
      by_cases hc : Real.sqrt n / 2 ≤ 1 / (2048 * γ)
      · have hh : Real.sqrt n / 2 ≤ 2 * k := by simpa only [s, if_neg hz, min_eq_left hc] using hks
        nlinarith
      · have hh : 1 / (2048 * γ) ≤ 2 * k := by
          simpa only [s, if_neg hz, min_eq_right (le_of_not_ge hc)] using hks
        have he : 1 / γ = 2048 * (1 / (2048 * γ)) := by field_simp
        rw [he] at hL₂
        linarith
  refine ⟨n / 2, k, by omega, by omega, ?_, ?_, hgamma, hwidth⟩
  · have hr : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      exact Nat.cast_div_le (α := ℝ)
    have hh : ((n / 2 + k ^ 2 : ℕ) : ℝ) ≤ n := by push_cast; nlinarith
    exact_mod_cast hh
  · exact_mod_cast (show n ≤ 3 * (n / 2) by omega)

end DPCut
