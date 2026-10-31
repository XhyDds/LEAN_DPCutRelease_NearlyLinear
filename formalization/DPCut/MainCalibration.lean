import DPCut.MainParameters
import DPCut.ReleaseCalibration

/-! Absorbing the preprocessing threshold into the main logarithm, with explicit constants. -/
set_option autoImplicit false
noncomputable section
namespace DPCut

lemma main_log_expansion {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    logFactor n 1 p = Real.log n -
      (Real.log p.delta + Real.log p.beta + Real.log p.gamma + Real.log p.epsilon) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hg, _, he, _, hd, _, hb, _⟩ := hp
  simp [logFactor, Real.log_div, Real.log_mul, hn0.ne', hd.ne', hb.ne', hg.ne', he.ne']

lemma preprocessing_log_bounds {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    let L := logFactor n 1 p
    Real.log (n / (p.beta / 2)) ≤ 3 * L ∧ -Real.log p.epsilon ≤ L := by
  have hL := core_log_bounds hn (le_refl (1 : ℝ)) p hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩ := hp
  have hlogg := Real.log_nonpos hg.le (show p.gamma ≤ 1 by linarith)
  have hlogd := Real.log_nonpos hd.le (show p.delta ≤ 1 by linarith)
  have hlogb := Real.log_nonpos hb.le (show p.beta ≤ 1 by linarith)
  have hlogn := Real.log_natCast_nonneg n
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have heq := main_log_expansion hn ⟨hg, hg1, he, he1, hd, hd1, hb, hb1⟩
  dsimp
  constructor
  · rw [Real.log_div hn0.ne' (by positivity), Real.log_div hb.ne' (by norm_num)]
    linarith [hL.log_n, hL.neg_log_beta, hL.one_le]
  · linarith

lemma preprocessingThreshold_upper {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    preprocessingThreshold n p ≤ 48 * logFactor n 1 p / (p.gamma * p.epsilon) := by
  rw [preprocessingThreshold_eq]
  have h := mul_le_mul_of_nonneg_left (preprocessing_log_bounds hn hp).1
    (show 0 ≤ 16 / (p.gamma * p.epsilon) by
      exact div_nonneg (by norm_num) (mul_pos hp.1 hp.2.2.1).le)
  convert h using 1
  ring

lemma full_release_log_bound {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    logFactor n (preprocessingThreshold n p) (boundedParameters p) ≤ 64 * logFactor n 1 p := by
  let L := logFactor n 1 p
  let U := preprocessingThreshold n p
  have hL := core_log_bounds hn (le_refl (1 : ℝ)) p hp
  have hL1 : 1 ≤ L := hL.one_le
  have hL0 : 0 < L := by linarith
  have hU1 : 1 ≤ U := preprocessingThreshold_one_le hn hp
  have hU0 : 0 < U := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hg := hp.1
  have he := hp.2.2.1
  have hd := hp.2.2.2.2.1
  have hb := hp.2.2.2.2.2.2.1
  have hlogU : Real.log U ≤ 51 * L := by
    have hh := Real.log_le_log hU0 (preprocessingThreshold_upper hn hp)
    rw [Real.log_div (by positivity) (mul_pos hg he).ne',
      Real.log_mul (by norm_num : (48 : ℝ) ≠ 0) hL0.ne', Real.log_mul hg.ne' he.ne'] at hh
    have h48 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 48)
    have hl := Real.log_le_self hL0.le
    have heL : -Real.log p.epsilon ≤ L := (preprocessing_log_bounds hn hp).2
    have hgL : -Real.log p.gamma ≤ L := hL.neg_log_gamma
    nlinarith
  have heq : logFactor n U (boundedParameters p) = L + Real.log U + 3 * Real.log 2 := by
    dsimp [L, logFactor, boundedParameters]
    rw [Real.log_div (mul_pos hn0 hU0).ne' (by positivity),
      Real.log_mul hn0.ne' hU0.ne']
    simp [Real.log_div, Real.log_mul, hn0.ne', hg.ne', he.ne', hd.ne', hb.ne']
    ring
  change logFactor n U (boundedParameters p) ≤ 64 * L
  rw [heq]
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

set_option maxRecDepth 2048 in
theorem full_release_error_bound {n : ℕ} (hn : 2 ≤ n) {p : Parameters} (hp : p.Valid) :
    (2 : ℝ) ^ 121 * boundedError n (preprocessingThreshold n p) (boundedParameters p) ≤
      (2 : ℝ) ^ 166 * mainError n p := by
  let L := logFactor n 1 p
  let J := logFactor n (preprocessingThreshold n p) (boundedParameters p)
  let q := (n : ℝ) / (p.gamma * p.epsilon)
  have hg := hp.1
  have he := hp.2.2.1
  have hL1 : 1 ≤ L := (core_log_bounds hn (le_refl (1 : ℝ)) p hp).one_le
  have hL0 : 0 ≤ L := by linarith
  have hJ0 : 0 ≤ J := by
    have := (core_log_bounds hn (preprocessingThreshold_one_le hn hp)
      (boundedParameters p) (boundedParameters_valid hp)).one_le
    linarith
  have hJ : J ≤ 64 * L := full_release_log_bound hn hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hU0 : 0 ≤ preprocessingThreshold n p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (preprocessingThreshold_one_le hn hp)
  have hlinear : n * preprocessingThreshold n p * J ≤ 3072 * (q * L ^ 7) := by
    calc
      _ ≤ n * (48 * L / (p.gamma * p.epsilon)) * (64 * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (preprocessingThreshold_upper hn hp) hn0)
          hJ hJ0 (by positivity)
      _ = 3072 * (q * L ^ 2) := by dsimp [q]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL1 (by omega : 2 ≤ 7)) hq)
        (by norm_num)
  have hpower : n / ((p.gamma / 2) * (p.epsilon / 2)) * J ^ 7 ≤
      (4 * 64 ^ 7 : ℝ) * (q * L ^ 7) := by
    calc
      _ ≤ n / ((p.gamma / 2) * (p.epsilon / 2)) * (64 * L) ^ 7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hJ0 hJ 7) (by positivity)
      _ = _ := by dsimp [q]; ring
  have hbound : boundedError n (preprocessingThreshold n p) (boundedParameters p) ≤
      (2 : ℝ) ^ 45 * (q * L ^ 7) := by
    change n * preprocessingThreshold n p * J + n / ((p.gamma / 2) * (p.epsilon / 2)) * J ^ 7 ≤ _
    have hqL : 0 ≤ q * L ^ 7 := mul_nonneg hq (pow_nonneg hL0 _)
    norm_num at hpower ⊢
    linarith
  have hh := mul_le_mul_of_nonneg_left hbound (by positivity : (0 : ℝ) ≤ 2 ^ 121)
  convert hh using 1
  change (2 : ℝ) ^ 166 * (q * L ^ 7) = 2 ^ 121 * (2 ^ 45 * (q * L ^ 7))
  ring

end DPCut
