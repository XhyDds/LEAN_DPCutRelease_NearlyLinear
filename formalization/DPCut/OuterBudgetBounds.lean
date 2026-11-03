import DPCut.OuterLogBounds

/-! Bounds on the advanced-composition budgets used by Lemma 22. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

structure OuterBudgetBounds (p : Parameters) (c : RunConfig) (L : ℝ) : Prop where
  epsGE_pos : 0 < c.epsGE
  deltaGE_pos : 0 < c.deltaGE
  betaGE_pos : 0 < c.betaGE
  betaGE_lt_one : c.betaGE < 1
  log_betaGE : Real.log (1 / c.betaGE) ≤ 190 * L
  log_deltaGE : Real.log (1 / c.deltaGE) ≤ 190 * L
  inverse_epsGE : 1 / c.epsGE ≤ 50000 * L ^ 2 / (p.gamma * p.epsilon)
  tau2_le : c.tau2 ≤ 14000 * L ^ 2 / p.epsilon

theorem outer_budget_bounds_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    OuterBudgetBounds p (runConfig n U p outerUtilityConstants) L := by
  let c := runConfig n U p outerUtilityConstants
  have hc := outerConfig_inner_utility_bounds_general hn hU p hp
  change InnerUtilityBounds n U p c at hc
  have hT1 : 0 < c.T1 := by
    apply Nat.ceil_pos.mpr
    change 0 < 80 * Real.log (n * U)
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl := Real.log_pos (show 1 < (n : ℝ) * U by nlinarith)
    positivity
  have hT2 : 0 < c.T2 := by change 0 < 1 + _; omega
  have hT1R : (0 : ℝ) < c.T1 := by exact_mod_cast hT1
  have hT2R : (0 : ℝ) < c.T2 := by exact_mod_cast hT2
  have hT11 : (1 : ℝ) ≤ c.T1 := by exact_mod_cast hT1
  have hT21 : (1 : ℝ) ≤ c.T2 := by exact_mod_cast hT2
  have he := hp.2.2.1
  have hd := hp.2.2.2.2.1
  have hb := hp.2.2.2.2.2.2.1
  have hg := hp.1
  have hL0 : 0 < L := by linarith [hL.one_le]
  obtain ⟨hT1b, hT2b⟩ := outer_horizons_bound_general hn hU p hp hL
  change (c.T1 : ℝ) ≤ 81 * L at hT1b
  change (c.T2 : ℝ) ≤ 102 * L / p.gamma ^ 2 at hT2b
  have hlT1 : Real.log c.T1 ≤ 82 * L := by
    convert log_le_from_bound hT1R (by norm_num : (0 : ℝ) < 81) hL.one_le hT1b using 1
    norm_num
  have hlT2 : Real.log c.T2 ≤ 105 * L := by
    convert log_le_from_bound_div_sq hT2R (by norm_num : (0 : ℝ) < 102) hL.one_le hg
      hL.neg_log_gamma hT2b using 1
    norm_num
  have hlog2 : Real.log (2 : ℝ) ≤ 2 := Real.log_le_self (by norm_num)
  have hlogBudget {b : ℝ} (hb : 0 < b) (hlb : -Real.log b ≤ L) :
      Real.log (1 / (b / (2 * c.T1 * c.T2))) ≤ 190 * L := by
    rw [one_div, Real.log_inv, Real.log_div hb.ne' (by positivity),
      Real.log_mul (by positivity) hT2R.ne', Real.log_mul (by norm_num) hT1R.ne']
    linarith [hL.one_le]
  have hbd : 0 < c.deltaGE := by change 0 < p.delta / (2 * c.T1 * c.T2); positivity
  have hbb : 0 < c.betaGE := by change 0 < p.beta / (2 * c.T1 * c.T2); positivity
  have hbb1 : c.betaGE < 1 := by
    change p.beta / (2 * c.T1 * c.T2) < 1
    apply (div_lt_one (by positivity)).mpr
    have hm := mul_le_mul hT11 hT21 (by norm_num) hT1R.le
    linarith [hp.2.2.2.2.2.2.2]
  have heG : 0 < c.epsGE := (main_composition_budget hT1 hT2 he hp.2.2.2.1 hd
    (by linarith [hp.2.2.2.2.2.1])).1
  have hlogSimple {b : ℝ} (hb : 0 < b) (hlb : -Real.log b ≤ L) :
      Real.log (2 * c.T1 / b) ≤ 85 * L := by
    rw [Real.log_div (by positivity) hb.ne', Real.log_mul (by norm_num) hT1R.ne']
    linarith [hL.one_le]
  have hlogd := hlogSimple hd hL.neg_log_delta
  have hs : Real.sqrt (2 * c.T2 * Real.log (2 * c.T1 / p.delta)) ≤ 132 * L / p.gamma := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hld : 0 ≤ Real.log (2 * c.T1 / p.delta) := Real.log_nonneg
      ((one_le_div hd).mpr (by linarith [hp.2.2.2.2.2.1]))
    calc
      _ ≤ (2 * (102 * L / p.gamma ^ 2)) * (85 * L) :=
        mul_le_mul (by linarith only [hT2b]) hlogd hld (by positivity)
      _ ≤ (132 * L / p.gamma) ^ 2 := by
        field_simp
        nlinarith [sq_nonneg L]
  have heGb : 1 / c.epsGE ≤ 50000 * L ^ 2 / (p.gamma * p.epsilon) := by
    have heq : 1 / c.epsGE = (4 * c.T1 * Real.sqrt (2 * c.T2 * Real.log (2 * c.T1 / p.delta))) /
        p.epsilon := by dsimp [c, runConfig]; field_simp
    rw [heq]
    calc
      _ ≤ (4 * (81 * L) * (132 * L / p.gamma)) / p.epsilon :=
        div_le_div_of_nonneg_right (mul_le_mul (by linarith only [hT1b]) hs (Real.sqrt_nonneg _) (by positivity)) he.le
      _ ≤ _ := by
        field_simp
        nlinarith [sq_nonneg L]
  refine ⟨heG, hbd, hbb, hbb1, hlogBudget hb hL.neg_log_beta,
    hlogBudget hd hL.neg_log_delta, heGb, ?_⟩
  have hlogb : Real.log (1 / c.beta2) ≤ 85 * L := by
    have heq : 1 / c.beta2 = 2 * c.T1 / p.beta := by change 1 / (p.beta / (2 * c.T1)) = _; field_simp
    rw [heq]
    exact hlogSimple hb hL.neg_log_beta
  change Real.log (1 / c.beta2) / (p.epsilon / (2 * c.T1)) ≤ _
  rw [div_div_eq_mul_div]
  calc
    _ ≤ (85 * L) * (2 * (81 * L)) / p.epsilon :=
      div_le_div_of_nonneg_right (mul_le_mul hlogb (by linarith only [hT1b]) (by positivity) (by positivity)) he.le
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ he.le
      nlinarith [sq_nonneg L]

/-- Specializations to the main theorem's parameter range. -/
theorem outer_budget_bounds {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    OuterBudgetBounds p (runConfig n U p outerUtilityConstants) L := by
  exact outer_budget_bounds_general hn hU p hp.iterationValid hL

end DPCut
