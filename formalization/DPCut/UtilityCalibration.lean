import DPCut.AggregateUtility

/-! Explicit public constants and failure-budget arithmetic for Lemma 20. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DPCut

/-- The same oracle as Lemma 17, with the cut-certificate constant fixed to 16. -/
def utilityConstants : Constants := { privacyConstants with certificate := 16 }

theorem utilityConstants_positive : utilityConstants.Positive := by
  norm_num [utilityConstants, privacyConstants, Constants.Positive]

@[simp] theorem oracleConfig_utilityConstants (n : ℕ) (ε δ β : ℝ) :
    oracleConfig n utilityConstants ε δ β = oracleConfig n privacyConstants ε δ β := rfl

theorem public_oracle_utility_bounds {n : ℕ} (hn : 2 ≤ n) {ε δ β : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    OracleUtilityBounds n (oracleConfig n utilityConstants ε δ β) := by
  rw [oracleConfig_utilityConstants]
  let o := oracleConfig n privacyConstants ε δ β
  have hp := public_oracle_privacy_bounds hn hε hε1 hδ hδ1 hβ hβ1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n / β) := Real.log_pos ((one_lt_div hβ).mpr (by linarith))
  have hK : 0 < o.K := Nat.ceil_pos.mpr (by change 0 < 8192 * Real.log (n / β); positivity)
  have hKR : (1 : ℝ) ≤ o.K := by exact_mod_cast hK
  have hbhalf : o.beta1 ≤ 1 / 2 := by
    change β / (4 * (n : ℝ) ^ 2 * o.K) ≤ 1 / 2
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hKR (sq_nonneg (n : ℝ))
    nlinarith
  have hb : 0 < o.beta1 := hp.beta_pos
  have hl : 512 * Real.log (n : ℝ) ≤ o.k := by
    have hbd : o.beta1 * o.delta1 ≤ 1 := by
      have := hp.delta_pos
      have := hp.delta_lt_half
      nlinarith
    have hlog' : Real.log (n : ℝ) ≤ Real.log (n / (o.beta1 * o.delta1)) := by
      apply Real.log_le_log hn0
      exact (le_div_iff₀ (mul_pos hb hp.delta_pos)).mpr (mul_le_of_le_one_right hn0.le hbd)
    have hceil := Nat.le_ceil (512 * Real.log (n / (o.beta1 * o.delta1)))
    change 512 * Real.log (n : ℝ) ≤ ⌈512 * Real.log (n / (o.beta1 * o.delta1))⌉₊
    linarith
  exact ⟨hp.eps_pos, by linarith [hp.lam_lower], hb, hbhalf, rfl, hp.batch_pos, hl⟩

lemma geometric_oracle_failure {n K : ℕ} (hn : 2 ≤ n) {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hK : 8192 * Real.log (n / β) ≤ K) :
    (n : ℝ) ^ 2 * (1 - 3 / 8192 : ℝ) ^ K ≤ β / 2 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hbase : (1 - 3 / 8192 : ℝ) ≤ Real.exp (-3 / 8192) := by
    linarith [Real.add_one_le_exp (-3 / 8192)]
  have hpow : (1 - 3 / 8192 : ℝ) ^ K ≤ (β / n) ^ 3 := by
    calc
      _ ≤ Real.exp (-3 / 8192) ^ K := pow_le_pow_left₀ (by norm_num) hbase K
      _ = Real.exp (K * (-3 / 8192)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-3 * Real.log (n / β)) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (Real.log (β / n)) ^ 3 := by
        rw [← Real.exp_nat_mul]
        congr 1
        rw [Real.log_div hn0.ne' hβ.ne', Real.log_div hβ.ne' hn0.ne']
        norm_num
        ring
      _ = _ := by rw [Real.exp_log (div_pos hβ hn0)]
  calc
    _ ≤ (n : ℝ) ^ 2 * (β / n) ^ 3 := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = β ^ 3 / n := by field_simp
    _ ≤ β / n := by
      apply div_le_div_of_nonneg_right _ hn0.le
      have hsq : β ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq hβ.le]
    _ ≤ β / 2 := div_le_div_of_nonneg_left hβ.le (by norm_num) hnR

theorem public_oracle_utility_budget {n : ℕ} (hn : 2 ≤ n) {ε δ β : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hβ : 0 < β) (hβ1 : β < 1) :
    2 * (Fintype.card (Edge n) : ℝ) * oracleUtilityError
      (oracleConfig n utilityConstants ε δ β) ≤ β := by
  let o := oracleConfig n utilityConstants ε δ β
  have ho := public_oracle_utility_bounds hn hε hε1 hδ hδ1 hβ hβ1
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log (n / β) := Real.log_pos ((one_lt_div hβ).mpr (by linarith))
  have hK : 0 < o.K := Nat.ceil_pos.mpr (by change 0 < 8192 * Real.log (n / β); positivity)
  have hKR : (0 : ℝ) < o.K := by exact_mod_cast hK
  have hk : 8192 * Real.log (n / β) ≤ o.K := Nat.le_ceil _
  have hgeo := geometric_oracle_failure hn hβ hβ1.le hk
  have hnoise : (n : ℝ) ^ 2 * (o.K * (o.beta1 / 2)) = β / 8 := by
    change (n : ℝ) ^ 2 * (o.K * ((β / (4 * (n : ℝ) ^ 2 * o.K)) / 2)) = β / 8
    field_simp
    ring
  have hcard : 2 * (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast twice_card_edge_le_square n
  change 2 * (Fintype.card (Edge n) : ℝ) * oracleUtilityError o ≤ β
  calc
    _ ≤ (n : ℝ) ^ 2 * oracleUtilityError o :=
      mul_le_mul_of_nonneg_right hcard (oracleUtilityError_nonneg ho)
    _ ≤ β := by
      rw [oracleUtilityError, mul_add, hnoise]
      linarith

end DPCut
