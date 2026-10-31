import DPCut.StoppingCalibration

/-! Uniform error coefficient and exact failure budget for bounded cut release. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

lemma outer_certificate_bound {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    let L := logFactor n U p
    let c := runConfig n U p outerUtilityConstants
    c.B ≤ 16 * n * U + (10 ^ 30 : ℝ) * (n * L ^ 6 / (p.gamma * p.epsilon)) := by
  let L := logFactor n U p
  let c := runConfig n U p outerUtilityConstants
  have hL := core_log_bounds hn hU p hp
  change CoreLogBounds n U p L at hL
  have hL0 : 0 < L := by linarith [hL.one_le]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := hp.1
  have he := hp.2.2.1
  obtain ⟨ht, hl⟩ := outer_oracle_size_bounds hn hU p hp hL
  change c.oracle.tau1 ≤ _ at ht
  change c.oracle.lam ≤ _ at hl
  let Q := (n : ℝ) * L ^ 6 / (p.gamma * p.epsilon)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have htn : L ^ 5 / (p.gamma * p.epsilon) ≤ Q := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hpow := pow_le_pow_right₀ hL.one_le (show 5 ≤ 6 by omega)
    nlinarith [pow_nonneg hL0.le 6]
  have hlamn : c.oracle.lam * n * Real.log n ≤ (10 ^ 28 : ℝ) * Q := by
    calc
      _ ≤ ((10 ^ 28 : ℝ) * L ^ 5 / (p.gamma * p.epsilon)) * n * L :=
        mul_le_mul (mul_le_mul_of_nonneg_right hl hn0.le) hL.log_n
          (Real.log_natCast_nonneg n) (by positivity)
      _ = _ := by dsimp [Q]; ring
  have ht' : c.oracle.tau1 ≤ (3 * 10 ^ 22 : ℝ) * Q :=
    ht.trans (by
      convert mul_le_mul_of_nonneg_left htn (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 22) using 1
      ring)
  change 16 * (c.oracle.tau1 + c.oracle.lam * n * Real.log n + n * U) ≤
    16 * n * U + (10 ^ 30 : ℝ) * Q
  norm_num
  nlinarith

/-- The O-constant is a single real number, independent of every input parameter. -/
theorem release_error_bound {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    let c := runConfig n U p outerUtilityConstants
    c.T1 * c.B + c.stop ≤ (2 : ℝ) ^ 121 * boundedError n U p := by
  let L := logFactor n U p
  let c := runConfig n U p outerUtilityConstants
  have hL := core_log_bounds hn hU p hp
  change CoreLogBounds n U p L at hL
  have hL0 : 0 < L := by linarith [hL.one_le]
  have hU0 : 0 ≤ U := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hg := hp.1
  have he := hp.2.2.1
  have hT := (outer_horizons_bound hn hU p hp hL).1
  have hB := outer_certificate_bound hn hU p hp
  change (c.T1 : ℝ) ≤ 81 * L at hT
  change c.B ≤ 16 * n * U + (10 ^ 30 : ℝ) * (n * L ^ 6 / (p.gamma * p.epsilon)) at hB
  let N := (n : ℝ) * U * L
  let Q := (n : ℝ) / (p.gamma * p.epsilon) * L ^ 7
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hB0 : 0 ≤ c.B := (mul_nonneg hn0 hU0).trans
    (outerConfig_inner_utility_bounds hn hU p hp).certificate_lower
  have hTB : (c.T1 : ℝ) * c.B ≤ 1296 * N + (81 * 10 ^ 30 : ℝ) * Q := by
    calc
      _ ≤ (81 * L) * (16 * n * U + (10 ^ 30 : ℝ) * (n * L ^ 6 / (p.gamma * p.epsilon))) :=
        mul_le_mul hT hB hB0 (by positivity)
      _ = _ := by dsimp [N, Q]; ring
  have hS : c.stop ≤ (2 : ℝ) ^ 120 * (N + Q) := by
    have hpow : L ^ 6 ≤ L ^ 7 := pow_le_pow_right₀ hL.one_le (by omega)
    have hq := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (n : ℝ) / (p.gamma * p.epsilon) by positivity)
    change (2 : ℝ) ^ 120 * (N + n / (p.gamma * p.epsilon) * L ^ 6) ≤ _
    exact mul_le_mul_of_nonneg_left (add_le_add_left hq N) (by positivity)
  change c.T1 * c.B + c.stop ≤ (2 : ℝ) ^ 121 * (N + Q)
  norm_num at hTB hS ⊢
  nlinarith

theorem release_failure_budget {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    let c := runConfig n U p outerUtilityConstants
    c.T1 * c.T2 * c.betaGE + c.T1 * c.beta2 = p.beta := by
  let c := runConfig n U p outerUtilityConstants
  have hc := outerConfig_inner_utility_bounds hn hU p hp
  have hT1 : 0 < c.T1 := by
    have hpos := hc.eps2_pos
    change 0 < p.epsilon / (2 * c.T1) at hpos
    by_contra hh
    have hz : c.T1 = 0 := by omega
    simp [hz] at hpos
  have hT2 : 0 < c.T2 := by change 0 < 1 + _; omega
  have hT1R : (0 : ℝ) < c.T1 := by exact_mod_cast hT1
  have hT2R : (0 : ℝ) < c.T2 := by exact_mod_cast hT2
  change c.T1 * c.T2 * (p.beta / (2 * c.T1 * c.T2)) +
    c.T1 * (p.beta / (2 * c.T1)) = p.beta
  field_simp
  ring

end DPCut
