import DPCut.OuterLoopUtility
import DPCut.OuterUtilityCalibration

/-! An explicit logarithmic horizon, with room for the final stopping test. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

theorem outer_horizon_mass_bound {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U) :
    let T := outerHorizon n U 80
    0 < T ∧ (19 / 20 : ℝ) ^ (T - 1) * ((n : ℝ) ^ 2 * U) ≤ n * U := by
  let T := outerHorizon n U 80
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hU0 : 0 < U := by linarith
  have hlogn : 1 / 2 ≤ Real.log n := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnR
    linarith [Real.log_two_gt_d9]
  have hlog : Real.log n ≤ Real.log (n * U) := Real.log_le_log hn0 (by nlinarith)
  have hT : 0 < T := Nat.ceil_pos.mpr (by change 0 < 80 * Real.log (n * U); linarith)
  have hceil : 80 * Real.log (n * U) ≤ (T : ℝ) := Nat.le_ceil _
  have hcast : ((T - 1 : ℕ) : ℝ) = T - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have htime : 20 * Real.log n ≤ ((T - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
  have hpow : (19 / 20 : ℝ) ^ (T - 1) ≤ 1 / n := by
    calc
      _ ≤ Real.exp (-1 / 20) ^ (T - 1) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (-1 / 20)]) _
      _ = Real.exp ((T - 1 : ℕ) * (-1 / 20)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log n) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hn0, one_div]
  refine ⟨hT, ?_⟩
  calc
    _ ≤ (1 / (n : ℝ)) * ((n : ℝ) ^ 2 * U) := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = _ := by field_simp

theorem outer_initial_budget {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (c : RunConfig) (hc : InnerUtilityBounds n U p c)
    (hγ : 0 < p.gamma) (hγ1 : p.gamma ≤ 1 / 4)
    (hT : c.T1 = outerHorizon n U 80) (hstop : 10 * (c.B + c.tau2 / p.gamma) ≤ c.stop)
    {w : Weights n} (hw : Bounded U w) :
    0 < c.T1 ∧ (19 / 20 : ℝ) ^ (c.T1 - 1) * mass (hadamard 1 w) + 2 * c.tau2 ≤ c.stop := by
  have hh := outer_horizon_mass_bound hn hU
  have hτ : 0 < c.tau2 := by
    rw [hc.tau2_eq]
    exact (laplace_calibrated_tails hc.eps2_pos hc.beta2_pos hc.beta2_lt_one).1
  have hτγ : c.tau2 ≤ c.tau2 / p.gamma := (le_div_iff₀ hγ).mpr
    (mul_le_of_le_one_right hτ.le (by linarith))
  have hm := masked_mass_le (show 0 ≤ U by linarith) hw (show IsMask (1 : Weights n) by intro e; norm_num)
  have hbound := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ (19 / 20 : ℝ) ^ (c.T1 - 1))
  rw [hT] at hbound ⊢
  refine ⟨hh.1, ?_⟩
  have hmeq : mass (hadamard (1 : Weights n) w) = pairing w 1 := by simp [mass, hadamard, pairing]
  rw [hmeq]
  have hnU : 0 ≤ (n : ℝ) * U := mul_nonneg (Nat.cast_nonneg n) (by linarith)
  linarith [hh.2, hc.certificate_lower]

end DPCut
