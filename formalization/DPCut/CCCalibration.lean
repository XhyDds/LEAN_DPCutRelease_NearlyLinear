import DPCut.CCReductionUtility
import DPCut.ApplicationCalibration
import DPCut.Theorem34

/-! Fixed slacks, privacy splitting, and uniform polylogarithmic error bounds
for the CC applications. -/
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace DPCut

lemma cc_slack_choice {c ρ ξ : ℝ} (hc : 1 ≤ c) (hρ : 1 ≤ ρ) (hξ : 0 < ξ) :
    ∃ γ η : ℝ, 0 < γ ∧ γ ≤ 1 / 4 ∧ 0 < η ∧ η ≤ 1 ∧ ccTransferTheta c γ η < 1 ∧
      ρ * (1 + ccTransferTheta c γ η) / (1 - ccTransferTheta c γ η) ≤ ρ + ξ := by
  let q := ξ / (2 * ρ + ξ)
  have hd : 0 < 2 * ρ + ξ := by linarith
  have hq : 0 < q := div_pos hξ hd
  have hq1 : q < 1 := (div_lt_one hd).mpr (by linarith)
  let η := q / 4
  let γ := η / (9 * c)
  have hc0 : 0 < c := by linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η ≤ 1 / 4 := by dsimp [η]; linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ4 : γ ≤ 1 / 4 := by
    dsimp [γ]
    apply (div_le_iff₀ (by positivity : 0 < 9 * c)).mpr
    linarith
  have heq : 9 * c * γ = η := by dsimp [γ]; field_simp
  have hθ : ccTransferTheta c γ η ≤ q := by
    unfold ccTransferTheta
    rw [heq]
    have hqη : q = 4 * η := by dsimp [η]; ring
    rw [hqη]
    nlinarith [mul_nonneg hη.le (sub_nonneg.mpr hη4)]
  refine ⟨γ, η, hγ, hγ4, hη, by linarith, hθ.trans_lt hq1, ?_⟩
  exact minimization_ratio_slack (by linarith : 0 ≤ ρ) (hθ.trans_lt hq1) hξ hθ

def ccParameters (n : ℕ) (γ ε : ℝ) : Parameters :=
  { applicationParameters n γ (ε / 2) with delta := (n : ℝ)⁻¹ ^ 10 / 2 }

lemma ccParameters_valid {n : ℕ} (hn : 2 ≤ n) {γ ε : ℝ}
    (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hε : 0 < ε) : (ccParameters n γ ε).Valid := by
  have h := applicationParameters_valid hn hγ hγ4 (half_pos hε)
  have hd := inverse_tenth_small hn
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by dsimp [ccParameters]; positivity,
    by change (n : ℝ)⁻¹ ^ 10 / 2 < 1 / 10; linarith [hd.2], h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

lemma cc_error_bound_of_constant (releaseConstant : ℝ) (hrelease : 0 < releaseConstant) {γ ε : ℝ} (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 2 ≤ n →
      releaseConstant * mainError n (ccParameters n γ ε) ≤ C * n * Real.log n ^ 7 := by
  let L := applicationLogCoefficient γ (ε / 2) + 1
  have hL : 0 < L := by dsimp [L]; linarith [applicationLogCoefficient_pos γ (ε / 2)]
  have he : 0 < min (ε / 2) 1 := lt_min (half_pos hε) (by norm_num)
  refine ⟨releaseConstant * (L ^ 7 / (γ * min (ε / 2) 1)), by positivity, ?_⟩
  intro n hn
  have hp := ccParameters_valid hn hγ hγ4 hε
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hi := (inverse_tenth_small hn).1
  have heq : logFactor n 1 (ccParameters n γ ε) =
      logFactor n 1 (applicationParameters n γ (ε / 2)) + Real.log 2 := by
    simp only [logFactor, ccParameters, applicationParameters, mul_one]
    rw [Real.log_div hn0.ne' (by positivity), Real.log_div hn0.ne' (by positivity)]
    rw [Real.log_mul (by positivity) he.ne', Real.log_mul (by positivity) hγ.ne',
      Real.log_mul (by positivity) hi.ne', Real.log_div hi.ne' (by norm_num)]
    rw [Real.log_mul (by positivity) he.ne', Real.log_mul (by positivity) hγ.ne', Real.log_mul hi.ne' hi.ne']
    ring
  have hlog : logFactor n 1 (ccParameters n γ ε) ≤ L * Real.log n := by
    rw [heq]
    have h := application_log_bound hn hγ (half_pos hε)
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
    dsimp [L]
    nlinarith
  have hlog0 : 0 ≤ logFactor n 1 (ccParameters n γ ε) := by
    have h := (core_log_bounds hn (le_refl 1) _ hp).one_le
    linarith
  have hpow := pow_le_pow_left₀ hlog0 hlog 7
  have hh := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ releaseConstant * (n / (γ * min (ε / 2) 1)) by positivity)
  change releaseConstant * (n / (γ * min (ε / 2) 1) * logFactor n 1 (ccParameters n γ ε) ^ 7) ≤ _
  convert hh using 1 <;> ring

lemma cc_error_bound {γ ε : ℝ} (hγ : 0 < γ) (hγ4 : γ ≤ 1 / 4) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, 2 ≤ n →
      (2 : ℝ) ^ 126 * mainError n (ccParameters n γ ε) ≤ C * n * Real.log n ^ 7 :=
  cc_error_bound_of_constant ((2:ℝ)^126) (by positivity) hγ hγ4 hε

lemma log_power_domination {n a d : ℕ} (hn : 2 ≤ n) (had : a ≤ d) :
    Real.log n ^ a ≤ (2 : ℝ) ^ d * Real.log n ^ d := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
  have hhalf : 1 / 2 ≤ Real.log n := by linarith [Real.log_two_gt_d9]
  have hnonneg : 0 ≤ Real.log n := by linarith
  calc
    _ ≤ (2 * Real.log n) ^ a := pow_le_pow_left₀ hnonneg (by linarith) _
    _ ≤ (2 * Real.log n) ^ d := pow_le_pow_right₀ (by linarith) had
    _ = _ := mul_pow _ _ _

lemma cc_rounding_threshold_bound {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) * Real.log n + Real.log (2 / ((n : ℝ)⁻¹ ^ 10)) ≤ 12 * n * Real.log n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
  rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, Real.log_inv]
  norm_num only [Nat.cast_ofNat]
  nlinarith [Real.log_natCast_nonneg n,
    mul_nonneg (sub_nonneg.mpr hnR) (Real.log_natCast_nonneg n)]

end DPCut
