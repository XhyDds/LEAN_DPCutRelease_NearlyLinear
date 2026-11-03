import DPCut.OuterBudgetBounds

/-! A universal stopping coefficient satisfying the paper's displayed threshold. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

lemma outer_oracle_size_bounds_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    let c := runConfig n U p outerUtilityConstants
    c.oracle.tau1 ≤ (3 * 10 ^ 22 : ℝ) * L ^ 5 / (p.gamma * p.epsilon) ∧
      c.oracle.lam ≤ (10 ^ 28 : ℝ) * L ^ 5 / (p.gamma * p.epsilon) := by
  let c := runConfig n U p outerUtilityConstants
  have hc := outerConfig_inner_utility_bounds_general hn hU p hp
  have hb := outer_budget_bounds_general hn hU p hp hL
  change InnerUtilityBounds n U p c at hc
  change OuterBudgetBounds p c L at hb
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL0 : 0 < L := by linarith [hL.one_le]
  have hg := hp.1
  have he := hp.2.2.1
  have hlogb : -Real.log c.betaGE ≤ 190 * L := by simpa [one_div, Real.log_inv] using hb.log_betaGE
  have hlogd : -Real.log c.deltaGE ≤ 190 * L := by simpa [one_div, Real.log_inv] using hb.log_deltaGE
  have hlogn : Real.log (n / c.betaGE) ≤ 191 * L := by
    rw [Real.log_div hn0.ne' hb.betaGE_pos.ne']
    linarith [hL.log_n]
  have hlogn0 : 0 < Real.log (n / c.betaGE) := Real.log_pos
    ((one_lt_div hb.betaGE_pos).mpr (by linarith [hb.betaGE_lt_one]))
  have hK : 0 < c.oracle.K := Nat.ceil_pos.mpr (by change 0 < 8192 * Real.log (n / c.betaGE); positivity)
  have hKR : (0 : ℝ) < c.oracle.K := by exact_mod_cast hK
  have hKb : (c.oracle.K : ℝ) ≤ 2000000 * L := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 8192 * Real.log (n / c.betaGE) by positivity)
    change (⌈8192 * Real.log (n / c.betaGE)⌉₊ : ℝ) ≤ _
    linarith [hL.one_le]
  have hlogK : Real.log c.oracle.K ≤ 2000001 * L := by
    convert log_le_from_bound hKR (by norm_num : (0 : ℝ) < 2000000) hL.one_le hKb using 1
    norm_num
  have hlogβ1 : Real.log (1 / c.oracle.beta1) ≤ 3000000 * L := by
    change Real.log (1 / (c.betaGE / (4 * (n : ℝ) ^ 2 * c.oracle.K))) ≤ _
    rw [one_div, Real.log_inv, Real.log_div hb.betaGE_pos.ne' (by positivity),
      Real.log_mul (by positivity) hKR.ne', Real.log_mul (by norm_num) (pow_ne_zero _ hn0.ne'),
      Real.log_pow]
    norm_num
    linarith [hL.log_n, hL.one_le, Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)]
  have hlogδ : 1 + Real.log (2 / c.deltaGE) ≤ 193 * L := by
    rw [Real.log_div (by norm_num) hb.deltaGE_pos.ne']
    linarith [hL.one_le, Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)]
  have hlogδ0 : 0 ≤ 1 + Real.log (2 / c.deltaGE) := by
    have hδ1 : c.deltaGE < 1 := by
      have hT1 : (1 : ℝ) ≤ c.T1 := by
        have hnum := hc.eps2_pos
        change 0 < p.epsilon / (2 * c.T1) at hnum
        have hpos : 0 < c.T1 := by
          by_contra hh
          have hz : c.T1 = 0 := by omega
          simp [hz] at hnum
        exact_mod_cast hpos
      have hT2 : (1 : ℝ) ≤ c.T2 := by change (1 : ℝ) ≤ ((1 + _ : ℕ) : ℝ); exact_mod_cast (Nat.le_add_right 1 _)
      change p.delta / (2 * c.T1 * c.T2) < 1
      apply (div_lt_one (by positivity)).mpr
      have hm := mul_le_mul hT1 hT2 (by norm_num) (by linarith)
      linarith [hp.2.2.2.2.2.1]
    have hl := Real.log_nonneg ((one_le_div hb.deltaGE_pos).mpr (show c.deltaGE ≤ 2 by linarith))
    linarith
  have he1b : 1 / c.oracle.eps1 ≤ (10 ^ 16 : ℝ) * L ^ 4 / (p.gamma * p.epsilon) := by
    have heq : 1 / c.oracle.eps1 =
        (320 * c.oracle.K * (1 + Real.log (2 / c.deltaGE))) * (1 / c.epsGE) := by
      change 1 / (c.epsGE / (320 * c.oracle.K * (1 + Real.log (2 / c.deltaGE)))) = _
      field_simp
    rw [heq]
    calc
      _ ≤ (320 * (2000000 * L) * (193 * L)) * (50000 * L ^ 2 / (p.gamma * p.epsilon)) :=
        mul_le_mul (mul_le_mul (by linarith only [hKb]) hlogδ hlogδ0 (by positivity))
          hb.inverse_epsGE (one_div_nonneg.mpr hb.epsGE_pos.le) (by positivity)
      _ ≤ _ := by
        apply (le_div_iff₀ (mul_pos hg he)).mpr
        field_simp
        nlinarith [pow_nonneg hL0.le 4]
  have hlognβδ : Real.log (n / (c.betaGE * c.deltaGE)) ≤ 381 * L := by
    rw [Real.log_div hn0.ne' (mul_pos hb.betaGE_pos hb.deltaGE_pos).ne',
      Real.log_mul hb.betaGE_pos.ne' hb.deltaGE_pos.ne']
    linarith [hL.log_n]
  have hε1 := hc.oracle_privacy.eps_pos
  constructor
  · change Real.log (1 / c.oracle.beta1) / c.oracle.eps1 ≤ _
    rw [div_eq_mul_one_div]
    calc
      _ ≤ (3000000 * L) * ((10 ^ 16 : ℝ) * L ^ 4 / (p.gamma * p.epsilon)) :=
        mul_le_mul hlogβ1 he1b (by positivity) (by positivity)
      _ = _ := by ring
  · change (1073741824 : ℝ) / c.oracle.eps1 * Real.log (n / (c.betaGE * c.deltaGE)) ≤ _
    have hlam : 0 ≤ Real.log (n / (c.betaGE * c.deltaGE)) := by
      have hl := hc.oracle_privacy.lam_lower
      change 8 ≤ (1073741824 : ℝ) / c.oracle.eps1 * Real.log (n / (c.betaGE * c.deltaGE)) at hl
      by_contra hh
      have hh' := mul_neg_of_pos_of_neg (div_pos (by norm_num : (0 : ℝ) < 1073741824) hε1) (lt_of_not_ge hh)
      linarith
    calc
      _ ≤ (1073741824 * ((10 ^ 16 : ℝ) * L ^ 4 / (p.gamma * p.epsilon))) * (381 * L) :=
        mul_le_mul (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he1b (by norm_num : (0 : ℝ) ≤ 1073741824))
          hlognβδ hlam (by positivity)
      _ ≤ _ := by
        apply (le_div_iff₀ (mul_pos hg he)).mpr
        field_simp
        nlinarith [pow_nonneg hL0.le 5]

theorem outer_stopping_threshold_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) :
    let c := runConfig n U p outerUtilityConstants
    10 * (c.B + c.tau2 / p.gamma) ≤ c.stop := by
  let L := logFactor n U p
  let c := runConfig n U p outerUtilityConstants
  have hL := core_log_bounds_general hn hU p hp
  change CoreLogBounds n U p L at hL
  have hL0 : 0 < L := by linarith [hL.one_le]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hg := hp.1
  have he := hp.2.2.1
  have hb := outer_budget_bounds_general hn hU p hp hL
  obtain ⟨ht, hl⟩ := outer_oracle_size_bounds_general hn hU p hp hL
  change c.oracle.tau1 ≤ _ at ht
  change c.oracle.lam ≤ _ at hl
  change OuterBudgetBounds p c L at hb
  have hlogn := Real.log_natCast_nonneg n
  have hpow56 : L ^ 5 ≤ L ^ 6 := pow_le_pow_right₀ hL.one_le (by omega)
  have hpow26 : L ^ 2 ≤ L ^ 6 := pow_le_pow_right₀ hL.one_le (by omega)
  let Q := (n : ℝ) * L ^ 6 / (p.gamma * p.epsilon)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have htn : L ^ 5 / (p.gamma * p.epsilon) ≤ Q := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [pow_nonneg hL0.le 6]
  have hlamn : c.oracle.lam * n * Real.log n ≤ (10 ^ 28 : ℝ) * Q := by
    have hlam0 : 0 ≤ c.oracle.lam := by linarith [(outerConfig_inner_utility_bounds_general hn hU p hp).oracle_privacy.lam_lower]
    calc
      _ ≤ ((10 ^ 28 : ℝ) * L ^ 5 / (p.gamma * p.epsilon)) * n * L :=
        mul_le_mul (mul_le_mul_of_nonneg_right hl hn0.le) hL.log_n hlogn (by positivity)
      _ = _ := by dsimp [Q]; ring
  have ht' : c.oracle.tau1 ≤ (3 * 10 ^ 22 : ℝ) * Q :=
    ht.trans (by
      convert mul_le_mul_of_nonneg_left htn (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 22) using 1
      ring)
  have hτ : c.tau2 / p.gamma ≤ 14000 * Q := by
    calc
      _ ≤ (14000 * L ^ 2 / p.epsilon) / p.gamma := div_le_div_of_nonneg_right hb.tau2_le hg.le
      _ ≤ 14000 * Q := by
        dsimp [Q]
        field_simp
        nlinarith [pow_nonneg hL0.le 6]
  have hnU : 0 ≤ (n : ℝ) * U := mul_nonneg hn0.le (by linarith)
  have hnUL : n * U ≤ n * U * L := le_mul_of_one_le_right hnU hL.one_le
  change 10 * (16 * (c.oracle.tau1 + c.oracle.lam * n * Real.log n + n * U) + c.tau2 / p.gamma) ≤
    (2 : ℝ) ^ 120 * (n * U * L + n / (p.gamma * p.epsilon) * L ^ 6)
  have hQeq : n / (p.gamma * p.epsilon) * L ^ 6 = Q := by dsimp [Q]; ring
  rw [hQeq]
  norm_num
  nlinarith

/-- Specializations to the main theorem's parameter range. -/
lemma outer_oracle_size_bounds {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    let c := runConfig n U p outerUtilityConstants
    c.oracle.tau1 ≤ (3 * 10 ^ 22 : ℝ) * L ^ 5 / (p.gamma * p.epsilon) ∧
      c.oracle.lam ≤ (10 ^ 28 : ℝ) * L ^ 5 / (p.gamma * p.epsilon) := by
  exact outer_oracle_size_bounds_general hn hU p hp.iterationValid hL

theorem outer_stopping_threshold {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) :
    let c := runConfig n U p outerUtilityConstants
    10 * (c.B + c.tau2 / p.gamma) ≤ c.stop := by
  exact outer_stopping_threshold_general hn hU p hp.iterationValid

end DPCut
