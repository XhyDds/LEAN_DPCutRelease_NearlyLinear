import DPCut.OuterUtilityCalibration

/-! Elementary logarithmic bounds for the public outer-round parameter ledger. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

structure CoreLogBounds (n : ℕ) (U : ℝ) (p : Parameters) (L : ℝ) : Prop where
  one_le : 1 ≤ L
  log_nU : Real.log (n * U) ≤ L
  log_n : Real.log n ≤ L
  neg_log_gamma : -Real.log p.gamma ≤ L
  neg_log_delta : -Real.log p.delta ≤ L
  neg_log_beta : -Real.log p.beta ≤ L

lemma core_log_bounds_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) : CoreLogBounds n U p (logFactor n U p) := by
  obtain ⟨hγ, hγ1, hε, hε1, hδ, hδ1, hβ, hβ1⟩ := hp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hU0 : 0 < U := by linarith
  have hnlog : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hUlog := Real.log_nonneg hU
  have hγlog := Real.log_nonpos hγ.le (show p.gamma ≤ 1 by linarith)
  have hεlog := Real.log_nonpos hε.le hε1
  have hδlog := Real.log_nonpos hδ.le (show p.delta ≤ 1 by linarith)
  have hβlog := Real.log_nonpos hβ.le (show p.beta ≤ 1 by linarith)
  have hγbig : 1 ≤ -Real.log p.gamma := by
    have hh := Real.log_le_log hγ hγ1
    have hfour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1
      norm_num
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, hfour] at hh
    linarith [Real.log_two_gt_d9]
  have heq : logFactor n U p = Real.log n + Real.log U -
      (Real.log p.delta + Real.log p.beta + Real.log p.gamma + Real.log p.epsilon) := by
    simp [logFactor, Real.log_div, Real.log_mul, hn0.ne', hU0.ne', hδ.ne', hβ.ne', hγ.ne', hε.ne']
  have hnu : Real.log (n * U) = Real.log n + Real.log U := Real.log_mul hn0.ne' hU0.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [heq] <;> linarith

lemma outer_horizons_bound_general {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.IterationValid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    let c := runConfig n U p outerUtilityConstants
    (c.T1 : ℝ) ≤ 81 * L ∧ (c.T2 : ℝ) ≤ 102 * L / p.gamma ^ 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnu : 0 ≤ Real.log (n * U) := Real.log_nonneg (by nlinarith)
  have hln := Real.log_natCast_nonneg n
  have hγ := hp.1
  have hγ1 := hp.2.1
  have hL0 : 0 < L := by linarith [hL.one_le]
  constructor
  · change (⌈80 * Real.log (n * U)⌉₊ : ℝ) ≤ 81 * L
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 80 * Real.log (n * U) by positivity)
    linarith [hL.log_nU, hL.one_le]
  · change ((1 + ⌈64 * (1 + p.gamma) ^ 2 * Real.log n / p.gamma ^ 2⌉₊ : ℕ) : ℝ) ≤ _
    have hc := Nat.ceil_lt_add_one
      (show 0 ≤ 64 * (1 + p.gamma) ^ 2 * Real.log n / p.gamma ^ 2 by positivity)
    have hcoeff : 64 * (1 + p.gamma) ^ 2 ≤ 100 := by nlinarith
    have hnumer : 64 * (1 + p.gamma) ^ 2 * Real.log n ≤ 100 * L :=
      (mul_le_mul_of_nonneg_right hcoeff hln).trans (by linarith [hL.log_n])
    have hfrac := (div_le_div_of_nonneg_right hnumer (sq_nonneg p.gamma))
    have hsmall : (2 : ℝ) ≤ 2 * L / p.gamma ^ 2 := (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
      (by nlinarith [hL.one_le])
    push_cast
    have heq : 102 * L / p.gamma ^ 2 = 100 * L / p.gamma ^ 2 + 2 * L / p.gamma ^ 2 := by ring
    rw [heq]
    linarith

/-- A coarse log bound avoids numerical approximations to logarithms of constants. -/
lemma log_le_from_bound {x C L : ℝ} (hx : 0 < x) (hC : 0 < C) (hL : 1 ≤ L)
    (hb : x ≤ C * L) : Real.log x ≤ (C + 1) * L := by
  have hL0 : 0 < L := by linarith
  have hlog := Real.log_le_log hx hb
  rw [Real.log_mul hC.ne' hL0.ne'] at hlog
  have hc := Real.log_le_self hC.le
  have hl := Real.log_le_self hL0.le
  nlinarith

lemma log_le_from_bound_div_sq {x C L γ : ℝ} (hx : 0 < x) (hC : 0 < C) (hL : 1 ≤ L)
    (hγ : 0 < γ) (hγlog : -Real.log γ ≤ L) (hb : x ≤ C * L / γ ^ 2) :
    Real.log x ≤ (C + 3) * L := by
  have hL0 : 0 < L := by linarith
  have hlog := Real.log_le_log hx hb
  rw [Real.log_div (mul_pos hC hL0).ne' (pow_ne_zero _ hγ.ne'),
    Real.log_mul hC.ne' hL0.ne', Real.log_pow] at hlog
  have hc := Real.log_le_self hC.le
  have hl := Real.log_le_self hL0.le
  norm_num at hlog
  nlinarith

/-- Specializations to the main theorem's parameter range. -/
lemma core_log_bounds {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) : CoreLogBounds n U p (logFactor n U p) := by
  exact core_log_bounds_general hn hU p hp.iterationValid

lemma outer_horizons_bound {n : ℕ} (hn : 2 ≤ n) {U : ℝ} (hU : 1 ≤ U)
    (p : Parameters) (hp : p.Valid) {L : ℝ} (hL : CoreLogBounds n U p L) :
    let c := runConfig n U p outerUtilityConstants
    (c.T1 : ℝ) ≤ 81 * L ∧ (c.T2 : ℝ) ≤ 102 * L / p.gamma ^ 2 := by
  exact outer_horizons_bound_general hn hU p hp.iterationValid hL

end DPCut
