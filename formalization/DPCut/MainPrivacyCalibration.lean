import DPCut.Lemma17

/-! The exact epsilon and delta ledger used in Lemma 18. -/

set_option autoImplicit false
noncomputable section

namespace DPCut

lemma main_outer_horizon_pos {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U) :
    0 < outerHorizon n U privacyConstants.outer := by
  change 0 < ⌈1 * Real.log (n * U)⌉₊
  apply Nat.ceil_pos.mpr
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hprod : 1 < (n : ℝ) * U := by nlinarith
  simpa using Real.log_pos hprod

/-- The paper's per-inner-loop advanced-composition budget, including all
positivity hypotheses needed by the oracle and the square root. -/
lemma main_composition_budget {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let x := ε / (4 * k * Real.sqrt (2 * m * Real.log (2 * k / δ)))
    let d := δ / (2 * k)
    0 < x ∧ x < 1 ∧ 0 < d ∧ d < 1 ∧ advancedEpsilon m x d ≤ ε / (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let L := Real.log (2 * k / δ)
  have hL : 1 / 2 ≤ L := by
    have hr : (2 : ℝ) ≤ 2 * k / δ := (le_div_iff₀ hδ).mpr (by linarith)
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hr
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hL0 : 0 < L := by linarith
  let s := Real.sqrt (2 * m * L)
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = 2 * m * L := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    have hp := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (m : ℝ) by positivity)
    nlinarith only [hp, hs2, hs, hm1]
  let x := ε / (4 * k * s)
  have hx : 0 < x := by dsimp [x]; positivity
  have hxq : x ≤ 1 / 4 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : 0 < 4 * k * s)).mpr
    nlinarith only [hε1, mul_le_mul hk1 hs1 (by norm_num) hk0.le]
  have hxs : x * s = ε / (4 * k) := by dsimp [x]; field_simp
  have hxsq : x * s ≤ 1 / 4 := by
    rw [hxs]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (k : ℝ))).mpr
    linarith only [hε1, hk1]
  have hcritical : 2 * m * x ≤ s := by
    apply (mul_le_mul_iff_left₀ hs).mp
    have hh := mul_le_mul_of_nonneg_left (show x * s ≤ L by linarith only [hxsq, hL])
      (show 0 ≤ 2 * (m : ℝ) by positivity)
    nlinarith only [hh, hs2]
  have hexp : Real.exp x - 1 ≤ 2 * x := by
    have hh := Real.abs_exp_sub_one_le (show |x| ≤ 1 by rw [abs_of_pos hx]; linarith)
    rw [abs_of_pos hx] at hh
    exact (le_abs_self _).trans hh
  have hdrift : m * x * (Real.exp x - 1) ≤ x * s := by
    have hh := mul_le_mul_of_nonneg_left hexp (show 0 ≤ m * x by positivity)
    have hh' := mul_le_mul_of_nonneg_right hcritical hx.le
    nlinarith only [hh, hh']
  have hd : 0 < δ / (2 * k) := by positivity
  have hd1 : δ / (2 * k) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  refine ⟨hx, by linarith only [hxq], hd, hd1, ?_⟩
  have hinv : 1 / (δ / (2 * k)) = 2 * k / δ := by field_simp
  change advancedEpsilon m x (δ / (2 * k)) ≤ ε / (2 * k)
  rw [advancedEpsilon, hinv]
  change x * s + m * x * (Real.exp x - 1) ≤ ε / (2 * k)
  calc
    _ ≤ 2 * (x * s) := by linarith only [hdrift]
    _ = _ := by rw [hxs]; ring

end DPCut
