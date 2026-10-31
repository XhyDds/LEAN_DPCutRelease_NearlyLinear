import DPCut.OracleCalibration
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit universal constants realizing the parameter choices in Lemma 17. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace DPCut

/-- Conservative constants; only trials, batch, and regularization enter Lemma 17. -/
def privacyConstants : Constants := ⟨1, 8192, 512, 1073741824, 1, 1⟩

theorem privacyConstants_positive : privacyConstants.Positive := by
  norm_num [Constants.Positive, privacyConstants]

set_option maxHeartbeats 800000 in
theorem public_oracle_privacy_bounds {n : ℕ} (hn : 2 ≤ n) {ε δ β : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    OraclePrivacyBounds n (oracleConfig n privacyConstants ε δ β) := by
  let o := oracleConfig n privacyConstants ε δ β
  let L := Real.log (n / (β * δ))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnb : (2 : ℝ) ≤ n / β := (le_div_iff₀ hβ).mpr (by nlinarith)
  have hnbδ : (2 : ℝ) ≤ n / (β * δ) :=
    (le_div_iff₀ (mul_pos hβ hδ)).mpr (by nlinarith [mul_lt_mul_of_pos_left hδ1 hβ])
  have hL : 1 / 2 ≤ L := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hnbδ
    dsimp [L]
    linarith [Real.log_two_gt_d9]
  have hlognb : 0 < Real.log (n / β) := Real.log_pos (by linarith)
  have hK : 0 < o.K := by
    change 0 < ⌈8192 * Real.log (n / β)⌉₊
    exact Nat.ceil_pos.mpr (by positivity)
  have hKR : (0 : ℝ) < o.K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ o.K := by exact_mod_cast hK
  have hNK : (4 : ℝ) ≤ (n : ℝ) ^ 2 * o.K := by
    have hh := mul_le_mul (show (4 : ℝ) ≤ (n : ℝ) ^ 2 by nlinarith) hK1
      (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg (n : ℝ))
    simpa using hh
  have hlogδ : 0 < Real.log (2 / δ) :=
    Real.log_pos ((one_lt_div hδ).mpr (by linarith))
  have he : 0 < o.eps1 := by
    change 0 < ε / (320 * o.K * (1 + Real.log (2 / δ)))
    positivity
  have he1 : o.eps1 < 1 := by
    change ε / (320 * o.K * (1 + Real.log (2 / δ))) < 1
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [mul_pos hKR hlogδ]
  have hd : 0 < o.delta1 := by change 0 < δ / (20 * (n : ℝ) ^ 2 * o.K); positivity
  have hdhalf : o.delta1 < 1 / 2 := by
    change δ / (20 * (n : ℝ) ^ 2 * o.K) < 1 / 2
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hb : 0 < o.betaChi := by change 0 < β / (4 * (n : ℝ) ^ 2 * o.K); positivity
  have hb1 : o.betaChi < 1 := by
    change β / (4 * (n : ℝ) ^ 2 * o.K) < 1
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hKupper : (o.K : ℝ) ≤ 8193 * (n / β) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 8192 * Real.log (n / β) by positivity)
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hβ)
    change (⌈8192 * Real.log (n / β)⌉₊ : ℝ) ≤ _
    linarith
  have hlognbL : Real.log (n / β) ≤ L := by
    apply Real.log_le_log (div_pos hn0 hβ)
    apply div_le_div_of_nonneg_left hn0.le (mul_pos hβ hδ)
    nlinarith
  have hlogK : Real.log o.K ≤ 16387 * L := by
    have hh := Real.log_le_log hKR hKupper
    rw [Real.log_mul (by norm_num : (8193 : ℝ) ≠ 0) (div_pos hn0 hβ).ne'] at hh
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8193)
    linarith
  have hLn := Real.log_nonneg (show (1 : ℝ) ≤ n by linarith)
  have hLβ := Real.log_nonpos hβ.le hβ1.le
  have hLδ := Real.log_nonpos hδ.le hδ1.le
  have hLeq : L = Real.log n - Real.log β - Real.log δ := by
    dsimp [L]
    rw [Real.log_div hn0.ne' (mul_pos hβ hδ).ne', Real.log_mul hβ.ne' hδ.ne']
    ring
  have hRpos : 0 < Real.log (n / (o.betaChi * o.delta1)) := by
    apply Real.log_pos
    apply (one_lt_div (mul_pos hb hd)).mpr
    have hh : o.betaChi * o.delta1 < 1 := by
      nlinarith [mul_lt_mul_of_pos_left (show o.delta1 < 1 by linarith) hb]
    linarith
  have hReq : Real.log (n / (o.betaChi * o.delta1)) =
      Real.log 80 + 5 * Real.log n + 2 * Real.log o.K - Real.log β - Real.log δ := by
    have hi : (n : ℝ) / (o.betaChi * o.delta1) =
        80 * (n : ℝ) ^ 5 * (o.K : ℝ) ^ 2 / (β * δ) := by
      change (n : ℝ) / ((β / (4 * (n : ℝ) ^ 2 * o.K)) *
        (δ / (20 * (n : ℝ) ^ 2 * o.K))) = _
      field_simp
      ring
    rw [hi]
    simp [Real.log_div, Real.log_mul, Real.log_pow, hn0.ne', hKR.ne', hβ.ne', hδ.ne']
    ring
  have hRupper : Real.log (n / (o.betaChi * o.delta1)) ≤ 40000 * L := by
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 80)
    rw [hReq]
    linarith
  have htpos : 0 ≤ Real.log (1 / o.delta1) :=
    Real.log_nonneg ((one_le_div hd).mpr (by linarith))
  have hteq : Real.log (1 / o.delta1) =
      Real.log 20 + 2 * Real.log n + Real.log o.K - Real.log δ := by
    change Real.log (1 / (δ / (20 * (n : ℝ) ^ 2 * o.K))) = _
    simp [Real.log_div, Real.log_mul, Real.log_pow, hn0.ne', hKR.ne', hδ.ne']
  have htupper : Real.log (1 / o.delta1) ≤ 20000 * L := by
    have hc := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20)
    rw [hteq]
    linarith
  have hkdef : o.k = ⌈512 * Real.log (n / (o.betaChi * o.delta1))⌉₊ := rfl
  have hk : 0 < o.k := by rw [hkdef]; exact Nat.ceil_pos.mpr (by positivity)
  have hklow : 96 * Real.log (n / (o.betaChi * o.delta1)) ≤ o.k := by
    rw [hkdef]
    have hh := Nat.le_ceil (512 * Real.log (n / (o.betaChi * o.delta1)))
    linarith
  have hkupper : (o.k : ℝ) ≤ 20480002 * L := by
    rw [hkdef]
    have hh := Nat.ceil_lt_add_one
      (show 0 ≤ 512 * Real.log (n / (o.betaChi * o.delta1)) by positivity)
    linarith
  have hsqrt : Real.sqrt (o.k * Real.log (1 / o.delta1)) ≤
      ((o.k : ℝ) + Real.log (1 / o.delta1)) / 2 := by
    have hh := Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg o.k) htpos)
    have hp := Real.sqrt_nonneg (o.k * Real.log (1 / o.delta1))
    nlinarith [sq_nonneg ((o.k : ℝ) - Real.log (1 / o.delta1))]
  have hlamdef : o.lam = 1073741824 / o.eps1 * L := rfl
  have hlam : 8 ≤ o.lam := by
    rw [hlamdef]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ he).mpr
    nlinarith
  refine ⟨he, hlam, hb, hb1, hd, hdhalf, hk, hklow, ?_⟩
  apply (div_le_iff₀ (show 0 < o.lam by linarith)).mpr
  rw [hlamdef]
  have heq : o.eps1 * (1073741824 / o.eps1 * L) = 1073741824 * L := by
    field_simp
  rw [heq]
  linarith

end DPCut
